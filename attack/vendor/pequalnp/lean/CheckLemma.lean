/-
The verifier half of the checker. Run by tools/check-lean.mjs, after the lemma file has been
built, as:

  lake exe checklemma <module> <statement file> <check|refute>

It never trusts what the lemma file printed or how it was elaborated. It reads the compiled
result and decides four things:

1. KERNEL. Every constant of every project module the lemma rests on is sent to the kernel
   again: the definitions root on top of the pinned modules it imports, everything else on top
   of the whole pinned library and the definitions root. A declaration that reached the
   compiled file without the kernel's agreement is refused here, and so is a project
   declaration that carries a name the pinned library or the definitions root already uses
   (but for a second copy of one of their theorems, same statement, which is left out: see
   `sameTheorem`).
2. THEOREM. The module declares a theorem whose name is the module's name.
3. AXIOMS. The theorem's transitive axioms, walked over the re-checked constants (not read from
   any cache the file could write), are inside the allowlist. `sorry` is the axiom `sorryAx`,
   so a `sorry` anywhere under the theorem is caught here, from the compiled proof.
4. STATEMENT. The recorded statement is elaborated in an environment made of the pinned
   library and the definitions root (`PEqualNP.Defs` and the modules under it) and nothing else
   of this project, whatever the lemma file imports. So nothing the lemma file or any helper
   module declares (an instance, a notation, a macro) can change what the text means, and a
   statement can only speak of the pinned library and the definitions root. The kernel then
   checks that the theorem is a proof of that statement (of its negation for `refute`), in an
   environment that extends the one the statement was read in.

On acceptance it also prints `MODULES` (every project module the theorem rests on) and `DEFS`
(the modules of the definitions root), which the wrapper turns into hashes for the artifact.

Exit 0: accepted. Exit 1: rejected, with one REJECTED line naming the class. Exit 3: the
verifier itself could not run.
-/
import Lean
open Lean

namespace PEqualNPChecker

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Roots of the libraries this project owns (lean/lakefile.toml). Everything else is a pinned dependency. -/
def projectRoots : List Name := [`PEqualNP, `CheckerSuite]

def isProject (m : Name) : Bool := projectRoots.contains m.getRoot

/-- The definitions root: the one part of this project a recorded statement may speak of. -/
def defsRoot : Name := `PEqualNP.Defs

def isDefs (m : Name) : Bool := m == defsRoot || defsRoot.isPrefixOf m

/-- The pinned library a statement is read against, always the whole of it. -/
def statementLibrary : Name := `Mathlib

structure Walk where
  seen : NameSet := {}
  axioms : Array Name := #[]
  missing : Array Name := #[]

partial def walk (find : Name → Option ConstantInfo) (n : Name) : StateM Walk Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  match find n with
  | none => modify fun s => { s with missing := s.missing.push n }
  | some ci =>
    if ci matches .axiomInfo _ then modify fun s => { s with axioms := s.axioms.push n }
    for c in ci.getUsedConstantsAsSet do walk find c

def reject (cls msg : String) : IO UInt32 := do
  -- One line, always the last one printed: readers show the tail of the output.
  IO.println s!"REJECTED ({cls}): {msg.replace "\n" " "}"
  return 1

/-- No project module may declare a constant under this namespace: it is the checker's own. -/
def reserved : Name := `PEqualNPChecker

/-- A project constant `c` that carries the name of a constant `l` of the statement environment
is refused, with one exception, decided here: both are theorems, with the same universe
parameters and the same type. Lean writes some theorems on demand, in whichever module first
needs them (the equation lemmas `f.eq_1`, `f.eq_def`, ...): a project file that needs one and
does not import the pinned module that already holds it gets a second copy of its own, through
no act of its author.

Such a `c` is not accepted in place of `l`. It is LEFT OUT: it never reaches the kernel and never
enters the environment anything is checked in. Why nothing is lost:

* Every project constant that is kept is sent to the kernel on top of the statement environment,
  and there the name is `l`, the library's own theorem, with the library's own proof. Whatever
  `c`'s body says is never read by anything. So the final environment is the statement
  environment extended by kernel-accepted declarations only, as before; leaving a declaration
  out of the replay can only make the kernel refuse more (a kept constant that needed something
  `l` does not give), never accept more.
* A name still means one thing for the statement and for the proof: the name is `l` in both.
* The test is not what makes this sound (the point above holds for any left-out constant); it is
  what keeps the exception narrow. A term that names a theorem type-checks from its universe
  parameters and its type alone, and those are `l`'s exactly, so the honest file checks against
  `l` as it did against `c`. Everything else that collides is refused as before: a definition,
  an opaque, an axiom, an inductive type, a constructor, a recursor, a quotient constant on
  either side, a theorem whose type or universe parameters differ, a theorem against a
  non-theorem. `==` on `Expr` is equality up to bound variable names and binder annotations,
  neither of which the kernel reads; universe levels and constant names are compared exactly. -/
def sameTheorem (c l : ConstantInfo) : Bool :=
  match c, l with
  | .thmInfo c, .thmInfo l => c.levelParams == l.levelParams && c.type == l.type
  | _, _ => false

unsafe def run (modStr stmtPath kind : String) : IO UInt32 := do
  let mod := modStr.toName
  unless kind == "check" || kind == "refute" do
    IO.eprintln s!"kind must be check or refute, got {kind}"; return 3
  initSearchPath (← findSysroot)
  let stmt ← IO.FS.readFile stmtPath

  -- The statement environment: the whole pinned library and the definitions root, and nothing
  -- else of this project. The kernel environment the proof is checked in is built ON it, so a
  -- name means one thing for the statement and for the proof.
  enableInitializersExecution
  let stmtEnv ← importModules #[{ module := statementLibrary }, { module := defsRoot }] {}
    (trustLevel := 0) (loadExts := true)
  let stmtModules := stmtEnv.header.moduleNames
  let mut defsConsts : Std.HashMap Name ConstantInfo := {}
  let mut defsBaseImports : Array Import := #[{ module := `Init }]
  let mut defsModules : Array Name := #[]
  for i in [0:stmtModules.size] do
    let m := stmtModules[i]!
    if isProject m then
      unless isDefs m do
        return ← reject "defs-root" s!"the statement environment reached {m}, which is outside the definitions root"
      defsModules := defsModules.push m
      let d := stmtEnv.header.moduleData[i]!
      for c in d.constants do
        if reserved.isPrefixOf c.name then
          return ← reject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker"
        defsConsts := defsConsts.insert c.name c
      for imp in d.imports do
        if isProject imp.module then
          unless isDefs imp.module do
            return ← reject "defs-root" s!"{m}, in the definitions root, imports {imp.module}, which is outside it. The definitions root may import only the pinned library and itself"
        else unless defsBaseImports.any (·.module == imp.module) do
          defsBaseImports := defsBaseImports.push { module := imp.module }

  -- The compiled lemma module and every project module under it.
  let full ← importModules #[{ module := mod }] {} (trustLevel := 0)
  let names := full.header.moduleNames
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut projectModules : Array Name := #[]
  let libEnv := stmtEnv.toKernelEnv
  for i in [0:names.size] do
    let m := names[i]!
    if isProject m && !stmtModules.contains m then
      let d := full.header.moduleData[i]!
      projectModules := projectModules.push m
      if isDefs m then
        defsModules := defsModules.push m
        for imp in d.imports do
          if isProject imp.module && !isDefs imp.module then
            return ← reject "defs-root" s!"{m}, in the definitions root, imports {imp.module}, which is outside it. The definitions root may import only the pinned library and itself"
      for c in d.constants do
        if reserved.isPrefixOf c.name then
          return ← reject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker"
        -- A name of the pinned library or of the definitions root is theirs alone, whether or
        -- not the declaring file imports the module that holds it. A second copy of one of
        -- their theorems (`sameTheorem`) is left out of what is checked: the name stays theirs.
        if let some l := libEnv.find? c.name then
          if sameTheorem c l then continue
          return ← reject "redeclares" s!"{m} declares {c.name}, a name the pinned library or the definitions root already declares. A project module may not declare it again"
        consts := consts.insert c.name c
  unless names.contains mod && isProject mod do
    return ← reject "not-a-project-module" s!"{mod} is not under one of the project's libraries"

  -- 1. KERNEL: every project constant goes to the kernel again. The definitions root on top of
  -- the pinned modules it imports, alone; everything else on top of the statement environment,
  -- where a name that is already declared cannot be declared a second time.
  let defsBase ← importModules defsBaseImports {} (trustLevel := 0)
  try
    discard <| defsBase.toKernelEnv.replay defsConsts
  catch e =>
    return ← reject "kernel" s!"the kernel refused a declaration of the definitions root: {e}"
  let kenv ← try
      libEnv.replay consts
    catch e =>
      return ← reject "kernel" s!"the kernel refused a declaration under {mod}: {e}"
  -- What the walks below may rest on: a pinned constant, or a project constant the kernel has
  -- just accepted (the replay passes over unsafe and partial ones, so they do not count).
  let checked (n : Name) : Option ConstantInfo := do
    let ci ← kenv.find? n
    match stmtEnv.getModuleIdxFor? n with
    | some idx =>
      if isProject stmtModules[idx.toNat]! then
        let c ← defsConsts[n]?
        if c.isUnsafe || c.isPartial then none else some ci
      else some ci
    | none => if ci.isUnsafe || ci.isPartial then none else some ci

  -- 2. THEOREM
  let some ci := checked mod
    | return ← reject "no-theorem" s!"the file declares no theorem named {mod} (one lemma, one file: the theorem carries the module's name)"
  let .thmInfo thm := ci
    | return ← reject "no-theorem" s!"{mod} is not a theorem"

  -- 3. AXIOMS
  let (_, w) := (walk checked mod).run {}
  unless w.missing.isEmpty do
    return ← reject "kernel" s!"{mod} rests on constants the kernel never accepted: {w.missing.toList}"
  if w.axioms.contains ``sorryAx then
    return ← reject "sorry" s!"{mod} rests on sorry (read from the compiled proof)"
  let extra := w.axioms.filter (!allowedAxioms.contains ·)
  unless extra.isEmpty do
    return ← reject "axiom" s!"{mod} rests on axioms outside the allowlist: {extra.toList}"

  -- 4. STATEMENT: elaborated against the pinned library and the definitions root, and nothing
  -- else of this project.
  match Parser.runParserCategory stmtEnv `term stmt "<recorded statement>" with
  | .error e => return ← reject "statement" s!"the recorded statement is not one Lean term: {e}"
  | .ok _ => pure ()
  let src := "set_option autoImplicit false\ntheorem PEqualNPChecker.recorded :\n(\n" ++ stmt ++ "\n) := sorry\n"
  let (stmtEnv', msgs) ← Elab.process src stmtEnv {} (fileName := "<recorded statement>")
  if msgs.hasErrors then
    for m in msgs.toList do
      if m.severity matches .error then IO.println (← m.toString)
    return ← reject "statement" s!"the recorded statement does not elaborate. A statement may only use the pinned library and the definitions root ({defsRoot}); nothing declared in a lemma file or a helper module exists for it"
  let some rec := stmtEnv'.find? `PEqualNPChecker.recorded
    | return ← reject "statement" "the recorded statement did not produce a declaration"
  -- Every constant the recorded statement speaks of, however deep, is one the statement
  -- environment held before the statement was read, and one the kernel has accepted: the
  -- kernel environment extends that environment, so it is the same constant there.
  let mut sw : Walk := {}
  for c in rec.type.getUsedConstantsAsSet do
    sw := ((walk (fun n => if (libEnv.find? n).isSome then checked n else none) c).run sw).2
  unless sw.missing.isEmpty do
    return ← reject "statement" s!"the recorded statement rests on declarations that are not in the pinned library or the definitions root as the kernel accepted them: {sw.missing.toList}. Write it as one term that needs no auxiliary declaration"
  unless rec.levelParams.length == thm.levelParams.length do
    return ← reject "statement" s!"universe parameters differ: recorded {rec.levelParams}, proved {thm.levelParams}"
  let us := thm.levelParams.map mkLevelParam
  let recorded := rec.type.instantiateLevelParams rec.levelParams us
  let goal := if kind == "refute" then mkApp (mkConst ``Not) recorded else recorded
  let witness := Declaration.thmDecl {
    name := `PEqualNPChecker.witness, levelParams := thm.levelParams, type := goal, value := mkConst mod us }
  match kenv.addDeclCore 0 0 witness (cancelTk? := none) with
  | .ok _ => pure ()
  | .error ex =>
    let what := if kind == "refute" then "the negation of the recorded statement" else "the recorded statement"
    let why ← try (ex.toMessageData {}).toString catch _ => pure "(the kernel's message could not be printed)"
    IO.println s!"kernel: {why}"
    return ← reject "statement" s!"{mod} is not a proof of {what}. It proves: {thm.type}"

  IO.println s!"MODULES {" ".intercalate (projectModules.filter (!isDefs ·) |>.toList.map toString)}"
  IO.println s!"DEFS {" ".intercalate (defsModules.toList.map toString)}"
  IO.println s!"ACCEPTED ({kind}): {mod}; axioms {w.axioms.toList}; kernel re-checked {consts.size + defsConsts.size} constants of {(defsModules ++ projectModules.filter (!isDefs ·)).toList}"
  return 0

end PEqualNPChecker

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [mod, stmt, kind] =>
    try PEqualNPChecker.run mod stmt kind
    catch e => IO.eprintln s!"checker fault: {e}"; return 3
  | _ => IO.eprintln "usage: CheckLemma <module> <statement file> <check|refute>"; return 3
