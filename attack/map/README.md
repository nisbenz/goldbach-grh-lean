# Map

`claims.json` — every claim we track, with `status` ∈ checked / conditional / open / refuted /
dead / stalled / external. "external" means published/literature, not verified by us.

`blockers.json` — the attack queue. `desk.py next` reads this file. Fields: id, title, program,
status, parallel, difficulty, why, route, assigned_to (managed by the desk).

`feed.jsonl` — append-only events. Each line: {at, kind, id, by, text}. Kinds include
claim_checked, blocker_opened, attack_started, attack_released, submitted, verdict, news.

Rules:
- Never flip a claim to `checked` unless a checker run in checker/runs.jsonl says so.
- Conditional results keep their hypothesis in the claim object; never strip it.
- When a blocker is resolved, set status to resolved and append a feed event with the evidence.
