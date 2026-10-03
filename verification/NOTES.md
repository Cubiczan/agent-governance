# agent-governance — Lean 4 verification notes

Model: `verification/Governance.lean` (Lean 4.34.1, core library only, no
Mathlib). Compiles clean with `~/.elan/bin/lean Governance.lean` (exit 0).
No `sorry` / `admit` / custom axioms: `#print axioms` on the headline
theorems (`no_unapproved_execution`, `approve_locked_traces`,
`no_double_approve`, `evalStep_locked_below_threshold`,
`approveCommentary_traces`, `reach_inv`) shows only `propext` and
`Quot.sound`.

Semantics were pinned from the TypeScript source, not the README. Where
the code and the README differ, the model follows the code (see F1).

## Model choices

- Money is modelled as `Int` (read: cents). The code uses IEEE-754
  doubles throughout (`notionalUsd: number`) — see F7.
- `evaluate`'s non-arithmetic checks (action/asset allowlists, venue,
  confidence floor, leverage cap, price band, extra claims) are
  abstracted into an opaque `Checks` record; the arithmetic core
  (sanity floor, per-asset cap, max notional, projected daily cap, HITL
  threshold) is modelled exactly.
- The per-asset cap is passed to the model pre-resolved, mirroring
  `perAssetLimits[asset] ?? maxNotionalUsd` (src/gate.ts:269–270).
- Decision ids are a counter, not `randomUUID()` (src/gate.ts:493);
  uniqueness is all the proofs use.
- Throws are modelled as `(state, none)` with the state untouched.
- Policy is a fixed parameter. The gate's `updatePolicy` hot-reload is
  NOT modelled — see F3 for the consequence this hides.

## Theorem → source mapping

### Evaluation (`ChpGate.evaluate`, src/gate.ts:242–320)

| Theorem | What it pins down | Source |
|---|---|---|
| `saneNotional_true` | the sanity predicate the code computes (finite, > 0, or exactly 0 iff `allowZeroNotional`) | src/gate.ts:402–410 (`adversarialCheck`) |
| `hardOk_components` | `hardOk` unfolds to exactly the code's conjunction (checks ∧ sanity ∧ per-asset ≤ ∧ max ≤ ∧ projected-daily ≤) | src/gate.ts:271–293 |
| `hardOk_nonneg` | hard checks passing ⇒ notional ≥ 0 | src/gate.ts:402–410 |
| `evalCore_blocked` | any hard failure ⇒ BLOCKED record, no charge, nothing pends | src/gate.ts:291–300 (finalize BLOCKED) |
| `evalCore_hitl` | hard pass ∧ `notional ≥ hitlThreshold` ⇒ HITL_REQUIRED, record + pending entry, **no charge yet** | src/gate.ts:303, 312 |
| `evalCore_locked` | hard pass ∧ below threshold ⇒ LOCKED, notional charged to the daily window | src/gate.ts:317 |
| `evalCore_records` / `evalCore_nextId` | every outcome appends exactly one provenance record and mints one fresh id | src/gate.ts:481–506 (`finalize`) |
| `evalStep_locked_facts` | the rolled-window LOCKED case, all components at once | src/gate.ts:242–320 |
| `evalStep_locked_below_threshold` | **a LOCKED-via-evaluate record is strictly below the HITL threshold and not human-stamped** | src/gate.ts:303 (the `>=` boundary) |

### Approval (`ChpGate.approveHuman`, src/gate.ts:328–359)

| Theorem | What it pins down | Source |
|---|---|---|
| `approve_unknown` | unknown / already-resolved id ⇒ throw, state untouched | src/gate.ts:330 |
| `approve_pending_erased` | the pending entry is deleted by the call — **before** the cap recheck | src/gate.ts:334 |
| `approve_consumes` | after any non-throwing call the id is no longer pending | src/gate.ts:334 |
| `no_double_approve` | a second approval of the same id throws and changes nothing: no un-approving, no re-execution | src/gate.ts:330, 334 |
| `approve_locked_facts` | LOCKED outcome ⇒ id was pending with that notional; record is human-stamped with a **fresh** id; recheck passed (`rolled spent + n ≤ dailyCap`, `n ≤ maxNotional`); notional charged | src/gate.ts:338, 348, 493 |
| `approve_blocked_facts` | cap-recheck failure ⇒ BLOCKED record, no charge — but the pending entry is still consumed | src/gate.ts:334, 338 |
| `approveStep_records` | an approval appends at most one record; the throw path appends none | src/gate.ts:481–506 |

### Invariants and reachability

| Theorem | What it pins down |
|---|---|
| `roll_pending` / `roll_records` / `roll_nextId` / `roll_spent_cases` | the daily-window roll (src/gate.ts daily-window logic) touches nothing but `spent`/`windowStart`, and spent only resets to 0 |
| `PendOk` (structure) | pending-map well-formedness: keys below `nextId`, unique, backed by a HITL_REQUIRED record, non-negative notionals |
| `Inv` (structure) | safety (LOCKED ⇒ below threshold ∨ human-stamped) + cap soundness (`0 ≤ spent ≤ dailyCap`) |
| `initial_inv`, `roll_inv`, `evalCore_inv`, `evalStep_inv`, `approveStep_inv` | the invariant is established by the empty gate and preserved by every public mutation |
| `reach_inv` | every reachable state satisfies `Inv` |
| **`no_unapproved_execution`** (headline) | in every reachable state, a LOCKED record at/above the threshold necessarily carries a recorded human approval |
| **`pending_backed`** (headline) | every pending id is backed by a genuine HITL_REQUIRED provenance record — approvals can only act on real escalations |
| **`approve_locked_traces`** (headline) | an approval-produced LOCKED record is human-stamped and traces to a HITL_REQUIRED record with the approved id and the same notional |

### Finance adapter (`src/finance-analysis.ts`)

| Theorem | What it pins down | Source |
|---|---|---|
| `assignReviewer_pending` | assignment succeeds only for a genuinely pending decision | src/finance-analysis.ts:341–356 |
| `approveCommentary_binding` | a successful commentary approval proves `approver = recorded assignee` | src/finance-analysis.ts:359–368 |
| `approveCommentary_traces` | a LOCKED commentary approval inherits the gate-level traceability, plus the binding | src/finance-analysis.ts:359–368 + gate |

### Order aggregate (`src/domain-events.ts`)

| Theorem | What it pins down | Source |
|---|---|---|
| `live_terminal` | live `fill`/`cancel` reject from `filled`/`cancelled` — terminal states are one-way | src/domain-events.ts:281–293 |
| `replay_overwrites_terminal` | replaying `opened → fill → cancel` yields `cancelled` — a transition the live aggregate rejects | src/domain-events.ts:323–355 (`Order.apply`, no status guard) |
| `live_rejects_same_stream` | the same stream on the live path is rejected | src/domain-events.ts:281–293 |

### Audit ledger (`src/ledger.ts`)

| Theorem | What it pins down | Source |
|---|---|---|
| `appendEntry_entries` | an append writes exactly one entry, with `prevSig` = previous tail signature | src/ledger.ts:323–345 (esp. 334, 343, 345) |
| `appendEntry_isPrefix` | the entry list grows by suffix extension only — earlier states are prefixes of later ones (append-only in the model, matching the class's API surface) | src/ledger.ts (no update/delete API) |
| `appendEntry_link` | the new entry points at the previous tail signature and the tail advances to its signature — the invariant `verifyLedger` re-derives | src/ledger.ts:334–345 |

## Discrepancies and risks (only what was actually found)

**F1 — Threshold boundary and values: README vs code.**
The comparison is `>=` (src/gate.ts:303: `notionalUsd >= hitlThresholdUsd`),
matching the policy schema comment ("At/above => human approval
required"). An action exactly at the threshold requires a human; the
model proves LOCKED-by-evaluate records are *strictly* below it.
The value also differs by policy: README quickstart 1000; built-in
`defaultPolicy()` **250** (src/policy.ts:76); finance-analysis policy
**0** (src/finance-analysis.ts:165 — every draft is HITL); domain-event
order policy **1000** (src/domain-events.ts:102). There is no single
"the threshold" for this codebase.

**F2 — Amount splitting is not aggregated for HITL.**
The threshold is per action only. The daily cap aggregates notionals,
but nothing escalates when cumulative sub-threshold volume grows: many
just-under-threshold actions auto-lock with no human ever involved,
until the daily cap binds (and the cap's remedy is BLOCKED, not HITL).
Modelled faithfully: `Inv.safe` is a per-record property; no
aggregate-HITL theorem exists because the code has no such rule.

**F3 — `approveHuman` rechecks only two caps, against the *current*
policy.** The recheck (src/gate.ts:338) tests projected-daily and
max-notional only — not the per-asset cap, allowlists, venue,
confidence, leverage, price band, or extra claims, all of which were
checked at evaluation time. Worse, policy hot-reload can swap the
policy between evaluation and approval, so an approval is validated
against limits the original decision never saw (in either direction).
The model fixes one policy `P`, so `approve_locked_facts` should be
read as "under an unchanged policy". Also note the strictness flip:
evaluation caps are inclusive (`<=`, lines 271–279) while the approval
recheck uses strict `>` (line 338) — equivalent for the boundary, but
only because both compare the same quantities.

**F4 — A failed approval still consumes the decision.** The pending
entry is deleted (line 334) *before* the recheck (line 338), so a
cap-blocked approval cannot be retried after the window rolls or
limits are raised — the operator must re-submit the action from
scratch. Proven as `approve_consumes` + `approve_blocked_facts`.

**F5 — Who can approve: the core gate checks almost nothing.**
`approveHuman` requires only a non-empty approver string
(`requireIdentity`, line 329). No allowlist, no reviewer pool, no
separation of duties, no bar on the proposer approving their own
action. The reviewer binding exists only in the finance adapter
(`assignReviewer`/`approveCommentary`, proven as
`approveCommentary_binding`) — and it is bypassable:
`getChpGate()` is public (src/finance-analysis.ts:275), so any caller
can invoke the underlying gate's `approveHuman` directly and skip the
assigned-reviewer check entirely. The domain-event handler's
`approveHuman` (src/domain-events.ts:214–218) likewise delegates
straight to the gate with no binding.

**F6 — Approval mints a new decision; the HITL record is never
updated.** `finalize` always assigns a fresh `randomUUID()`
(src/gate.ts:493). The original HITL_REQUIRED provenance record stays
HITL_REQUIRED forever in the in-memory list; the LOCKED approval
record is a separate entry whose only link to the escalation is the
pending-map consumption and the claim detail string. Audit trails
that join on decision id will not connect the two. (Modelled: the
approved record's id is the fresh counter value, per
`approve_locked_facts`.)

**F7 — Money is floating point.** All amounts are IEEE-754 doubles;
the model's `Int` arithmetic is exact. Proofs therefore cover the
integer semantics of the checks, not float representation/rounding
edge cases (e.g. a notional a hair below the threshold in decimal that
is not representable exactly, or accumulation error in
`dailyNotionalUsd`). The `>=` boundary result in particular should be
read as exact-arithmetic.

**F8 — Corrupt persisted daily state fails open.**
If the daily-state file is unreadable/corrupt, the catch in
`loadDailyState` (src/gate.ts:463–464) keeps a fresh window with 0
spent: the day's accumulated notional is silently forgotten rather
than failing closed, resetting the daily cap mid-day.

**F9 — Ledger failure ordering inside `approveHuman`.** `finalize`
pushes provenance and appends to the ledger (src/gate.ts:500, 506)
*after* the pending entry was deleted (line 334) and, on the success
path, after the daily total was charged (line 348). A ledger-append
throw therefore consumes the approval and charges the cap without
returning a decision. In `evaluate`'s HITL branch the ordering is
safer: `pendingHitl.set` (line 312) happens after `finalize`, so a
failed append leaves nothing pending.

**F10 — Order replay does not respect the live lifecycle.**
`Order.apply` (src/domain-events.ts:323–355) sets `cancelled`/`filled`
with no current-status check, while live `cancel`/`fill` throw unless
`open`. A verified stream `opened → filled → cancelled` replays to
`cancelled`, a state the live aggregate can never reach
(`replay_overwrites_terminal` vs `live_rejects_same_stream`).
`fromEvents` validates only that the stream starts with
`order.opened`.

**F11 — Ledger "append-only" is API-level, not tamper-proof.**
Append-only holds because `AuditLedger` exposes no mutation API and
`verifyLedger` re-derives the HMAC chain (modelled as
`appendEntry_isPrefix` / `appendEntry_link`). An external writer with
file access can still rewrite history; detection depends on HMAC key
secrecy — and the key falls back to a documented insecure default when
neither the constructor option nor `AUDIT_LEDGER_KEY` is set.

## Coverage limits

- `updatePolicy` hot-reload, persistence (`loadDailyState` beyond F8),
  and the Jev/adversarial claim *contents* are outside the model;
  `Checks` abstracts every non-arithmetic predicate.
- The domain-event handler's full event-sourcing flow is represented
  only by the Order lifecycle fragment above.
- Float behaviour: see F7.
