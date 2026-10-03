/-
  Governance.lean — a Lean 4 (core library only) formal model of the
  human-in-the-loop approval gate in `@cubiczan/agent-governance`.

  Modelled from the TypeScript sources (read directly, not the README):

    * `ChpGate.evaluate` / `ChpGate.approveHuman`  — src/gate.ts
    * `Policy` arithmetic                          — src/policy.ts
    * `AuditLedger` append/chain discipline        — src/ledger.ts
    * `FinanceAnalysisGate` reviewer binding       — src/finance-analysis.ts
    * `Order` lifecycle + replay                   — src/domain-events.ts

  Money is modelled in integer cents (`Int`). The TypeScript code uses
  IEEE-754 doubles throughout; the theorems below are therefore exact
  statements about the *integer* semantics of the same comparisons, and
  NOTES.md flags the float gap. The per-asset cap is passed to `evaluate`
  already resolved (`perAssetLimits[asset] ?? maxNotionalUsd`,
  src/gate.ts:269-270). Checks that do not depend on arithmetic
  (allowlists, venue, confidence/leverage/price adversarial rules, adapter
  extra claims) are abstracted as the `Checks` booleans; the arithmetic
  checks (caps, sanity floor, HITL threshold) are modelled exactly.

  Compile with:  ~/.elan/bin/lean Governance.lean     (Lean 4.34.1, no Mathlib)
  No `sorry` / `admit` / custom axioms are used.
-/

namespace Governance

/-! ## Decision states, policy, gate state -/

/-- Lifecycle states of a proposed action (src/gate.ts, `ChpState`). -/
inductive ChpState where
  | exploring
  | provisional
  | locked
  | hitlRequired
  | blocked
  deriving DecidableEq, Repr

/-- The arithmetic part of a `Policy` (src/policy.ts) plus the gate's
    `allowZeroNotional` option (src/gate.ts, `ChpGateOptions`). -/
structure Policy where
  maxNotional : Int
  dailyCap : Int
  hitlThreshold : Int
  allowZero : Bool

/-- Outcomes of the non-arithmetic checks in `evaluate`: allowed-action,
    allowed/blocked-asset, allowed-venue (src/gate.ts:255-268), the
    confidence / leverage / price-band adversarial checks
    (src/gate.ts:402-439), and adapter-supplied extra claims
    (src/gate.ts:283-288). -/
structure Checks where
  actionOk : Bool
  assetsOk : Bool
  venueOk : Bool
  advOk : Bool
  extraOk : Bool

/-- One provenance record, as appended by `finalize` (src/gate.ts:481-500).
    `byHuman` marks the records minted by `approveHuman`, whose single
    claim is `human-approval` (src/gate.ts:350-358). Decision ids are
    modelled by a counter; the code uses `randomUUID` (src/gate.ts:493) —
    freshness is all the proofs rely on. -/
structure Record where
  id : Nat
  st : ChpState
  notional : Int
  byHuman : Bool
  deriving DecidableEq, Repr

/-- Gate state: rolling daily window (`dailyNotionalUsd`, `dailyWindowStart`),
    the `pendingHitl` map (an association list here), the append-only
    in-memory provenance list (`decisions`), and the id counter. -/
structure Gate where
  spent : Int
  windowStart : Int
  pending : List (Nat × Int)
  records : List Record
  nextId : Nat

/-- A freshly constructed gate (src/gate.ts, constructor): nothing spent,
    nothing pending, no decisions. -/
def initialGate (start : Int) : Gate :=
  { spent := 0, windowStart := start, pending := [], records := [], nextId := 0 }

/-! ## Association-list helpers (the `pendingHitl` Map) -/

/-- Lookup in an association list — `Map.get` (src/gate.ts:330). -/
def findV {β : Type} : List (Nat × β) → Nat → Option β
  | [], _ => none
  | (k, v) :: t, id => if k = id then some v else findV t id

/-- Delete the first entry with the given key — `Map.delete`
    (src/gate.ts:334). A `Map` has unique keys, and the model maintains
    key-uniqueness as an invariant (`PendOk.nodup`), under which deleting
    the first match deletes the only match. -/
def eraseId {β : Type} : List (Nat × β) → Nat → List (Nat × β)
  | [], _ => []
  | (k, v) :: t, id => if k = id then t else (k, v) :: eraseId t id

theorem findV_mem {β : Type} {l : List (Nat × β)} {id : Nat} {v : β}
    (h : findV l id = some v) : (id, v) ∈ l := by
  induction l with
  | nil => simp [findV] at h
  | cons p t ih =>
    rcases p with ⟨k, w⟩
    by_cases hk : k = id
    · have h1 : findV ((k, w) :: t) id = some w := by simp [findV, hk]
      rw [h1] at h
      have h2 : w = v := Option.some.inj h
      subst h2
      subst hk
      exact List.mem_cons_self
    · have h1 : findV ((k, w) :: t) id = findV t id := by simp [findV, hk]
      rw [h1] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem mem_eraseId {β : Type} {p : Nat × β} {l : List (Nat × β)} {id : Nat}
    (h : p ∈ eraseId l id) : p ∈ l := by
  induction l with
  | nil => simp [eraseId] at h
  | cons q t ih =>
    rcases q with ⟨k, w⟩
    by_cases hk : k = id
    · have h1 : eraseId ((k, w) :: t) id = t := by simp [eraseId, hk]
      rw [h1] at h
      exact List.mem_cons_of_mem _ h
    · have h1 : eraseId ((k, w) :: t) id = (k, w) :: eraseId t id := by
        simp [eraseId, hk]
      rw [h1] at h
      rcases List.mem_cons.mp h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hm)

theorem nodup_eraseId {β : Type} {l : List (Nat × β)} {id : Nat}
    (h : List.Nodup (l.map Prod.fst)) :
    List.Nodup ((eraseId l id).map Prod.fst) := by
  induction l with
  | nil => exact h
  | cons q t ih =>
    rcases q with ⟨k, w⟩
    have h' : List.Nodup (k :: t.map Prod.fst) := by simpa using h
    rw [List.nodup_cons] at h'
    obtain ⟨hk_notin, ht_nodup⟩ := h'
    by_cases hk : k = id
    · have h1 : eraseId ((k, w) :: t) id = t := by simp [eraseId, hk]
      rw [h1]
      exact ht_nodup
    · have h1 : eraseId ((k, w) :: t) id = (k, w) :: eraseId t id := by
        simp [eraseId, hk]
      rw [h1]
      have h2 : ((k, w) :: eraseId t id).map Prod.fst
          = k :: (eraseId t id).map Prod.fst := rfl
      rw [h2, List.nodup_cons]
      refine ⟨?_, ih ht_nodup⟩
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨p, hp, hpf⟩ := hmem
      exact hk_notin (List.mem_map.mpr ⟨p, mem_eraseId hp, hpf⟩)

/-- Under key-uniqueness, a deleted id stays deleted: this is what makes
    `approveHuman` one-shot (src/gate.ts:334 + the throw at :330-333). -/
theorem findV_eraseId_none {β : Type} {l : List (Nat × β)} {id : Nat}
    (h : List.Nodup (l.map Prod.fst)) : findV (eraseId l id) id = none := by
  induction l with
  | nil => rfl
  | cons q t ih =>
    rcases q with ⟨k, w⟩
    have h' : List.Nodup (k :: t.map Prod.fst) := by simpa using h
    rw [List.nodup_cons] at h'
    obtain ⟨hk_notin, ht_nodup⟩ := h'
    by_cases hk : k = id
    · have h1 : eraseId ((k, w) :: t) id = t := by simp [eraseId, hk]
      rw [h1]
      cases hfv : findV t id with
      | none => rfl
      | some v =>
        exfalso
        have hmem : (id, v) ∈ t := findV_mem hfv
        have hmap : id ∈ t.map Prod.fst :=
          List.mem_map.mpr ⟨(id, v), hmem, rfl⟩
        exact hk_notin (hk.symm ▸ hmap)
    · have h1 : eraseId ((k, w) :: t) id = (k, w) :: eraseId t id := by
        simp [eraseId, hk]
      rw [h1]
      have h2 : findV ((k, w) :: eraseId t id) id = findV (eraseId t id) id := by
        simp [findV, hk]
      rw [h2]
      exact ih ht_nodup

/-! ## The rolling daily window (`rollDailyWindow`, src/gate.ts:441-447) -/

/-- 24h in milliseconds (`DAY_MS`, src/gate.ts:166). -/
def DAY_MS : Int := 86400000

/-- Window roll: once `now - windowStart ≥ DAY_MS`, the spent total resets
    to 0 and the window restarts at `now`. Nothing else in the gate state
    is touched. -/
def roll (g : Gate) (now : Int) : Gate :=
  if decide (now - g.windowStart ≥ DAY_MS)
    then { g with spent := 0, windowStart := now }
    else g

theorem roll_pending (g : Gate) (now : Int) : (roll g now).pending = g.pending := by
  unfold roll
  split <;> rfl

theorem roll_records (g : Gate) (now : Int) : (roll g now).records = g.records := by
  unfold roll
  split <;> rfl

theorem roll_nextId (g : Gate) (now : Int) : (roll g now).nextId = g.nextId := by
  unfold roll
  split <;> rfl

theorem roll_spent_cases (g : Gate) (now : Int) :
    (roll g now).spent = 0 ∨ (roll g now).spent = g.spent := by
  unfold roll
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## The hard-check conjunction (`evaluate`, src/gate.ts:255-296) -/

/-- Sanity floor for the notional (src/gate.ts:407-410): it must be finite
    and positive, or exactly 0 when `allowZeroNotional` is set. The model
    uses `Int`, so finiteness is automatic and the floor is `0 < n`
    (resp. `0 ≤ n`); `Number.MIN_VALUE` in the code is the smallest
    positive double, i.e. "any positive amount" in integer terms. -/
def saneNotional (allowZero : Bool) (n : Int) : Bool :=
  if allowZero then decide (0 ≤ n) else decide (0 < n)

theorem saneNotional_true {az : Bool} {n : Int}
    (h : saneNotional az n = true) : 0 ≤ n := by
  cases az with
  | false =>
    have h1 : decide (0 < n) = true := h
    have h2 : 0 < n := of_decide_eq_true h1
    omega
  | true =>
    have h1 : decide (0 ≤ n) = true := h
    exact of_decide_eq_true h1

/-- The full hard-block conjunction of `evaluate` (src/gate.ts:291-293):
    the allowlist/adversarial booleans, the per-asset cap (`≤`, :271),
    the max-notional cap (`≤`, :274), the projected daily cap (`≤`, :279),
    and the sane-notional floor (:408). All comparisons are inclusive —
    a check fails only when the amount is *strictly over* its cap. -/
def hardOk (P : Policy) (chk : Checks) (cap spent n : Int) : Bool :=
  chk.actionOk && chk.assetsOk && chk.venueOk && chk.advOk && chk.extraOk &&
  decide (n ≤ cap) && decide (n ≤ P.maxNotional) &&
  decide (spent + n ≤ P.dailyCap) && saneNotional P.allowZero n

theorem hardOk_components {P : Policy} {chk : Checks} {cap spent n : Int}
    (h : hardOk P chk cap spent n = true) :
    ((((((((chk.actionOk = true ∧ chk.assetsOk = true) ∧
      chk.venueOk = true) ∧ chk.advOk = true) ∧ chk.extraOk = true) ∧
      n ≤ cap) ∧ n ≤ P.maxNotional) ∧ spent + n ≤ P.dailyCap) ∧
    saneNotional P.allowZero n = true) := by
  simp only [hardOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Every hard-passing action has a non-negative notional. This is what
    keeps the daily-cap accounting monotone. -/
theorem hardOk_nonneg {P : Policy} {chk : Checks} {cap spent n : Int}
    (h : hardOk P chk cap spent n = true) : 0 ≤ n :=
  saneNotional_true (hardOk_components h).2

/-! ## `evaluate` (src/gate.ts:248-320)

`evalCore` works on an already-rolled gate state; `evalStep` rolls first,
exactly as `evaluate` calls `rollDailyWindow` before the daily-cap check
(src/gate.ts:277). The proposed action is represented by its resolved
per-asset cap `cap` and its notional `n`. -/

def evalCore (P : Policy) (g : Gate) (chk : Checks) (cap n : Int) :
    Gate × Record :=
  if hardOk P chk cap g.spent n then
    if P.hitlThreshold ≤ n then
      ({ g with nextId := g.nextId + 1,
                pending := (g.nextId, n) :: g.pending,
                records := g.records ++
                  [{ id := g.nextId, st := .hitlRequired, notional := n,
                     byHuman := false }] },
       { id := g.nextId, st := .hitlRequired, notional := n, byHuman := false })
    else
      ({ g with nextId := g.nextId + 1,
                spent := g.spent + n,
                records := g.records ++
                  [{ id := g.nextId, st := .locked, notional := n,
                     byHuman := false }] },
       { id := g.nextId, st := .locked, notional := n, byHuman := false })
  else
    ({ g with nextId := g.nextId + 1,
              records := g.records ++
                [{ id := g.nextId, st := .blocked, notional := n,
                   byHuman := false }] },
     { id := g.nextId, st := .blocked, notional := n, byHuman := false })

def evalStep (P : Policy) (g : Gate) (now : Int) (chk : Checks) (cap n : Int) :
    Gate × Record :=
  evalCore P (roll g now) chk cap n

theorem evalCore_blocked {P : Policy} {g : Gate} {chk : Checks} {cap n : Int}
    (h : hardOk P chk cap g.spent n = false) :
    (evalCore P g chk cap n).2.st = .blocked ∧
    (evalCore P g chk cap n).1.spent = g.spent ∧
    (evalCore P g chk cap n).1.pending = g.pending := by
  simp [evalCore, h]

theorem evalCore_hitl {P : Policy} {g : Gate} {chk : Checks} {cap n : Int}
    (h : hardOk P chk cap g.spent n = true) (ht : P.hitlThreshold ≤ n) :
    (evalCore P g chk cap n).2.st = .hitlRequired ∧
    (evalCore P g chk cap n).2.byHuman = false ∧
    (evalCore P g chk cap n).2.notional = n ∧
    (evalCore P g chk cap n).1.pending = (g.nextId, n) :: g.pending ∧
    (evalCore P g chk cap n).1.spent = g.spent ∧
    (evalCore P g chk cap n).2.id = g.nextId ∧
    findV (evalCore P g chk cap n).1.pending g.nextId = some n := by
  simp [evalCore, h, ht, findV]

theorem evalCore_locked {P : Policy} {g : Gate} {chk : Checks} {cap n : Int}
    (h : hardOk P chk cap g.spent n = true) (ht : n < P.hitlThreshold) :
    (evalCore P g chk cap n).2.st = .locked ∧
    (evalCore P g chk cap n).2.byHuman = false ∧
    (evalCore P g chk cap n).2.notional = n ∧
    (evalCore P g chk cap n).1.spent = g.spent + n ∧
    (evalCore P g chk cap n).1.pending = g.pending := by
  have hnot : ¬ P.hitlThreshold ≤ n := by omega
  simp [evalCore, h, hnot]

/-- `evaluate` appends exactly one provenance record — the one it returns
    (`finalize`, src/gate.ts:481-500). -/
theorem evalCore_records {P : Policy} {g : Gate} {chk : Checks} {cap n : Int} :
    (evalCore P g chk cap n).1.records
      = g.records ++ [(evalCore P g chk cap n).2] := by
  cases hb : hardOk P chk cap g.spent n with
  | false => simp [evalCore, hb]
  | true =>
    by_cases ht : P.hitlThreshold ≤ n
    · simp [evalCore, hb, ht]
    · simp [evalCore, hb, ht]

/-- Every `evaluate` outcome mints exactly one fresh id (`finalize`,
    src/gate.ts:493). -/
theorem evalCore_nextId {P : Policy} {g : Gate} {chk : Checks} {cap n : Int} :
    (evalCore P g chk cap n).1.nextId = g.nextId + 1 := by
  cases hb : hardOk P chk cap g.spent n with
  | false => simp [evalCore, hb]
  | true =>
    by_cases ht : P.hitlThreshold ≤ n
    · simp [evalCore, hb, ht]
    · simp [evalCore, hb, ht]

/-- **Headline evaluation theorem.** If `evaluate` returns a LOCKED
    ("allowed") decision, then on the post-roll state every hard check
    passed, the notional is *strictly below* the HITL threshold, the
    decision is not human-stamped, and the notional has been charged to
    the daily window. In particular (src/gate.ts:303) the threshold test
    is `≥`: an action *at* the threshold can never take this path. -/
theorem evalStep_locked_facts {P : Policy} {g : Gate} {now : Int}
    {chk : Checks} {cap n : Int}
    (h : (evalStep P g now chk cap n).2.st = .locked) :
    hardOk P chk cap (roll g now).spent n = true ∧
    n < P.hitlThreshold ∧
    (evalStep P g now chk cap n).2.notional = n ∧
    (evalStep P g now chk cap n).2.byHuman = false ∧
    (evalStep P g now chk cap n).1.spent = (roll g now).spent + n := by
  cases hb : hardOk P chk cap (roll g now).spent n with
  | false =>
    have hb2 := evalCore_blocked hb
    simp [evalStep, hb2] at h
  | true =>
    by_cases ht : P.hitlThreshold ≤ n
    · have hh := (evalCore_hitl hb ht).1
      simp [evalStep, hh] at h
    · have hl := evalCore_locked hb (by omega : n < P.hitlThreshold)
      exact ⟨rfl, by omega, hl.2.2.1, hl.2.1, hl.2.2.2.1⟩

/-- Corollary in words: an auto-approved (LOCKED) evaluation is always
    strictly below the HITL threshold and never carries a human-approval
    stamp — see `evalStep_locked_facts`. -/
theorem evalStep_locked_below_threshold {P : Policy} {g : Gate} {now : Int}
    {chk : Checks} {cap n : Int}
    (h : (evalStep P g now chk cap n).2.st = .locked) :
    n < P.hitlThreshold ∧ (evalStep P g now chk cap n).2.byHuman = false := by
  have hf := evalStep_locked_facts h
  exact ⟨hf.2.1, hf.2.2.2.1⟩

/-! ## `approveHuman` (src/gate.ts:328-359)

Faithful sequencing from the code:
  1. the approver identity is validated and the pending map is consulted —
     an unknown id throws *before any state changes* (modeled by returning
     `(g, none)` with the state untouched; even the window roll at :336
     has not happened yet);
  2. the pending entry is deleted (:334) — *before* the cap recheck, so a
     rejected approval still consumes the decision;
  3. the window rolls (:336) and only two caps are rechecked (:338):
     the projected daily cap and the max notional, both with strict `>`.
     The per-asset cap, allowlists, venue, confidence, leverage and price
     band are NOT rechecked here, and the policy used is the *current*
     one, which a hot-reload may have swapped since evaluation.
  4. on success the amount is charged to the daily window (:348) and a
     fresh LOCKED record is minted via `finalize` — with a *new* decision
     id, not the HITL record's id. -/

def approveStep (P : Policy) (g : Gate) (now : Int) (id : Nat) :
    Gate × Option Record :=
  match findV g.pending id with
  | none => (g, none)
  | some n =>
    let rg := roll g now
    if P.dailyCap < rg.spent + n ∨ P.maxNotional < n then
      ({ rg with pending := eraseId g.pending id,
                 nextId := rg.nextId + 1,
                 records := rg.records ++
                   [{ id := rg.nextId, st := .blocked, notional := n,
                      byHuman := false }] },
       some { id := rg.nextId, st := .blocked, notional := n, byHuman := false })
    else
      ({ rg with pending := eraseId g.pending id,
                 nextId := rg.nextId + 1,
                 spent := rg.spent + n,
                 records := rg.records ++
                   [{ id := rg.nextId, st := .locked, notional := n,
                      byHuman := true }] },
       some { id := rg.nextId, st := .locked, notional := n, byHuman := true })

/-- Unknown / already-resolved id: `approveHuman` throws and the gate
    state is completely unchanged (src/gate.ts:330-333). -/
theorem approve_unknown {P : Policy} {g : Gate} {now : Int} {id : Nat}
    (h : findV g.pending id = none) :
    approveStep P g now id = (g, none) := by
  simp [approveStep, h]

/-- In both outcomes of a found entry, the resulting pending map is the
    erased one. -/
theorem approve_pending_erased {P : Policy} {g : Gate} {now : Int} {id : Nat}
    {n : Int} (h : findV g.pending id = some n) :
    (approveStep P g now id).1.pending = eraseId g.pending id := by
  by_cases hc : P.dailyCap < (roll g now).spent + n ∨ P.maxNotional < n
  · simp [approveStep, h, hc]
  · simp [approveStep, h, hc]

/-- **One-shot approval.** After an approval attempt on a pending id, the
    id is gone from the pending map (src/gate.ts:334) — whether the
    approval locked or was cap-blocked. -/
theorem approve_consumes {P : Policy} {g : Gate} {now : Int} {id : Nat}
    {n : Int} (hnd : List.Nodup (g.pending.map Prod.fst))
    (h : findV g.pending id = some n) :
    findV (approveStep P g now id).1.pending id = none := by
  rw [approve_pending_erased h]
  exact findV_eraseId_none hnd

/-- **No double approval / no re-execution.** A second `approveHuman` on
    the same id hits the unknown-id path: it returns `none` (the throw)
    and leaves the state exactly as the first call left it. -/
theorem no_double_approve {P : Policy} {g : Gate} {now now' : Int}
    {id : Nat} {n : Int} (hnd : List.Nodup (g.pending.map Prod.fst))
    (h : findV g.pending id = some n) :
    (approveStep P (approveStep P g now id).1 now' id).2 = none ∧
    (approveStep P (approveStep P g now id).1 now' id).1
      = (approveStep P g now id).1 := by
  have hc := approve_consumes (P := P) (g := g) (now := now) (id := id)
    (n := n) hnd h
  have hu := approve_unknown (P := P) (g := (approveStep P g now id).1)
    (now := now') (id := id) hc
  exact ⟨by simpa using congrArg Prod.snd hu,
         by simpa using congrArg Prod.fst hu⟩

/-- **Approval facts (LOCKED case).** If `approveHuman` returns a LOCKED
    record, then: the id was pending with exactly the record's notional;
    the record is human-stamped; the record carries a *fresh* id (the
    gate's next counter value, not the HITL record's id); the daily
    recheck passed (`rolled spent + n ≤ dailyCap`, `n ≤ maxNotional`);
    and the notional was charged to the window. -/
theorem approve_locked_facts {P : Policy} {g : Gate} {now : Int} {id : Nat}
    {rec : Record}
    (h : (approveStep P g now id).2 = some rec) (hl : rec.st = .locked) :
    findV g.pending id = some rec.notional ∧
    rec.byHuman = true ∧
    rec.id = g.nextId ∧
    (roll g now).spent + rec.notional ≤ P.dailyCap ∧
    rec.notional ≤ P.maxNotional ∧
    (approveStep P g now id).1.spent = (roll g now).spent + rec.notional := by
  cases hfv : findV g.pending id with
  | none =>
    rw [approve_unknown hfv] at h
    simp at h
  | some n =>
    by_cases hc : P.dailyCap < (roll g now).spent + n ∨ P.maxNotional < n
    · have hb : (approveStep P g now id).2
          = some { id := (roll g now).nextId, st := .blocked, notional := n,
                   byHuman := false } := by
        simp [approveStep, hfv, hc]
      rw [hb] at h
      have hrec := Option.some.inj h
      subst hrec
      simp at hl
    · have hlk : (approveStep P g now id).2
          = some { id := (roll g now).nextId, st := .locked, notional := n,
                   byHuman := true } := by
        simp [approveStep, hfv, hc]
      rw [hlk] at h
      have hrec := Option.some.inj h
      have e_not : rec.notional = n := by rw [← hrec]
      have e_hum : rec.byHuman = true := by rw [← hrec]
      have e_id : rec.id = (roll g now).nextId := by rw [← hrec]
      have hspent : (approveStep P g now id).1.spent
          = (roll g now).spent + n := by
        simp [approveStep, hfv, hc]
      have hc' := not_or.mp hc
      have h1 := hc'.1
      have h2 := hc'.2
      refine ⟨?_, e_hum, ?_, ?_, ?_, ?_⟩
      · rw [e_not]
      · rw [e_id]; exact roll_nextId g now
      · rw [e_not]; omega
      · rw [e_not]; omega
      · rw [e_not]; exact hspent

/-- **Approval facts (cap-blocked case).** If `approveHuman` returns a
    BLOCKED record, the id was pending, the recheck failed on the current
    state's numbers (daily projection over the cap, or notional over the
    max), and no notional was charged. The pending entry is still gone
    (see `approve_consumes`). -/
theorem approve_blocked_facts {P : Policy} {g : Gate} {now : Int} {id : Nat}
    {rec : Record}
    (h : (approveStep P g now id).2 = some rec) (hl : rec.st = .blocked) :
    findV g.pending id = some rec.notional ∧
    ((roll g now).spent + rec.notional > P.dailyCap ∨
      rec.notional > P.maxNotional) ∧
    (approveStep P g now id).1.spent = (roll g now).spent := by
  cases hfv : findV g.pending id with
  | none =>
    rw [approve_unknown hfv] at h
    simp at h
  | some n =>
    by_cases hc : P.dailyCap < (roll g now).spent + n ∨ P.maxNotional < n
    · have hb : (approveStep P g now id).2
          = some { id := (roll g now).nextId, st := .blocked, notional := n,
                   byHuman := false } := by
        simp [approveStep, hfv, hc]
      rw [hb] at h
      have hrec := Option.some.inj h
      have e_not : rec.notional = n := by rw [← hrec]
      have hspent : (approveStep P g now id).1.spent
          = (roll g now).spent := by
        simp [approveStep, hfv, hc]
      refine ⟨?_, ?_, hspent⟩
      · rw [e_not]
      · rw [e_not]; exact hc
    · have hlk : (approveStep P g now id).2
          = some { id := (roll g now).nextId, st := .locked, notional := n,
                   byHuman := true } := by
        simp [approveStep, hfv, hc]
      rw [hlk] at h
      have hrec := Option.some.inj h
      subst hrec
      simp at hl

/-- `approveHuman` appends at most one record; on the throw path it
    appends none and changes nothing. -/
theorem approveStep_records {P : Policy} {g : Gate} {now : Int} {id : Nat} :
    (approveStep P g now id).1.records = g.records ∨
    ∃ rec, (approveStep P g now id).1.records = g.records ++ [rec] ∧
      (approveStep P g now id).2 = some rec := by
  cases hfv : findV g.pending id with
  | none =>
    exact Or.inl (by rw [approve_unknown hfv])
  | some n =>
    by_cases hc : P.dailyCap < (roll g now).spent + n ∨ P.maxNotional < n
    · have h2 : (approveStep P g now id).2
          = some { id := (roll g now).nextId, st := .blocked, notional := n,
                   byHuman := false } := by
        simp [approveStep, hfv, hc]
      have h1 : (approveStep P g now id).1.records
          = (roll g now).records ++
            [{ id := (roll g now).nextId, st := .blocked, notional := n,
               byHuman := false }] := by
        simp [approveStep, hfv, hc]
      exact Or.inr ⟨_, by rw [h1, roll_records], h2⟩
    · have h2 : (approveStep P g now id).2
          = some { id := (roll g now).nextId, st := .locked, notional := n,
                   byHuman := true } := by
        simp [approveStep, hfv, hc]
      have h1 : (approveStep P g now id).1.records
          = (roll g now).records ++
            [{ id := (roll g now).nextId, st := .locked, notional := n,
               byHuman := true }] := by
        simp [approveStep, hfv, hc]
      exact Or.inr ⟨_, by rw [h1, roll_records], h2⟩

/-! ## Gate invariants -/

/-- Well-formedness of the pending map: keys are fresh (below `nextId`,
    src/gate.ts:493), unique (JS `Map` keys), every entry is backed by a
    HITL_REQUIRED provenance record (the pairing made by `evaluate`,
    src/gate.ts:312), and notionals are non-negative (the sanity floor,
    src/gate.ts:402–410). -/
structure PendOk (g : Gate) : Prop where
  keys_lt : ∀ p ∈ g.pending, p.1 < g.nextId
  nodup : List.Nodup (g.pending.map Prod.fst)
  backed : ∀ p ∈ g.pending, ∃ r ∈ g.records,
    r.id = p.1 ∧ r.st = .hitlRequired ∧ r.notional = p.2
  nonneg : ∀ p ∈ g.pending, 0 ≤ p.2

/-- The full gate invariant: pending well-formedness, plus the two facts
    the product actually relies on —
    * **safety**: every LOCKED record is either below the HITL threshold
      or human-stamped (src/gate.ts:303, 348);
    * **cap soundness**: the daily total is a genuine running total,
      `0 ≤ spent ≤ dailyCap` (src/gate.ts:279, 317, 348). -/
structure Inv (P : Policy) (g : Gate) : Prop where
  pend : PendOk g
  safe : ∀ r ∈ g.records, r.st = .locked →
    r.notional < P.hitlThreshold ∨ r.byHuman = true
  cap_nonneg : 0 ≤ g.spent
  cap_le : g.spent ≤ P.dailyCap

/-- The empty gate satisfies the invariant under any non-negative-cap
    policy — including all three built-in policies (their caps / maxes
    are non-negative; see NOTES.md). -/
theorem initial_inv {P : Policy} (hP : 0 ≤ P.dailyCap) :
    Inv P (initialGate 0) := by
  refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_, nonneg := ?_ },
           safe := ?_, cap_nonneg := by show (0 : Int) ≤ 0; omega, cap_le := hP }
  · intro p hp; simp [initialGate] at hp
  · simp [initialGate]
  · intro p hp; simp [initialGate] at hp
  · intro p hp; simp [initialGate] at hp
  · intro r hr; simp [initialGate] at hr

/-- Invariance only depends on `pending`, `records`, `nextId` and the
    spent bounds; used to transport the invariant across the window
    roll. -/
theorem inv_congr {P : Policy} {g₁ g₂ : Gate}
    (hpend : g₂.pending = g₁.pending) (hrec : g₂.records = g₁.records)
    (hid : g₂.nextId = g₁.nextId)
    (hsp : 0 ≤ g₂.spent ∧ g₂.spent ≤ P.dailyCap) (h : Inv P g₁) :
    Inv P g₂ := by
  refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_, nonneg := ?_ },
           safe := ?_, cap_nonneg := hsp.1, cap_le := hsp.2 }
  · intro p hp
    rw [hpend] at hp
    rw [hid]
    exact h.pend.keys_lt p hp
  · rw [hpend]
    exact h.pend.nodup
  · intro p hp
    rw [hpend] at hp
    rw [hrec]
    exact h.pend.backed p hp
  · intro p hp
    rw [hpend] at hp
    exact h.pend.nonneg p hp
  · intro r hr hrl
    rw [hrec] at hr
    exact h.safe r hr hrl

/-- The daily-window roll preserves the invariant (a rolled window just
    restarts the spent total at 0). -/
theorem roll_inv {P : Policy} {g : Gate} (hP : 0 ≤ P.dailyCap) (h : Inv P g)
    (now : Int) : Inv P (roll g now) := by
  apply inv_congr (roll_pending g now) (roll_records g now)
    (roll_nextId g now) _ h
  rcases roll_spent_cases g now with hsp | hsp
  · rw [hsp]
    exact ⟨by omega, hP⟩
  · rw [hsp]
    exact ⟨h.cap_nonneg, h.cap_le⟩

/-- `evaluate` preserves the invariant, in all three outcome branches. -/
theorem evalCore_inv {P : Policy} {g : Gate} (h : Inv P g)
    (chk : Checks) (cap n : Int) : Inv P (evalCore P g chk cap n).1 := by
  have hrecs : (evalCore P g chk cap n).1.records
      = g.records ++ [(evalCore P g chk cap n).2] := evalCore_records
  have hnid : (evalCore P g chk cap n).1.nextId = g.nextId + 1 :=
    evalCore_nextId
  cases hb : hardOk P chk cap g.spent n with
  | false =>
    obtain ⟨hst, hspent, hpend⟩ := evalCore_blocked hb
    refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_,
                       nonneg := ?_ },
             safe := ?_, cap_nonneg := ?_, cap_le := ?_ }
    · intro p hp
      rw [hpend] at hp
      rw [hnid]
      have hlt := h.pend.keys_lt p hp
      omega
    · rw [hpend]
      exact h.pend.nodup
    · intro p hp
      rw [hpend] at hp
      obtain ⟨r, hr, hrid, hrst, hrnot⟩ := h.pend.backed p hp
      exact ⟨r, by rw [hrecs]; exact List.mem_append.mpr (Or.inl hr),
        hrid, hrst, hrnot⟩
    · intro p hp
      rw [hpend] at hp
      exact h.pend.nonneg p hp
    · intro r hr hrl
      rw [hrecs] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact h.safe r hr hrl
      · rw [List.mem_singleton] at hr
        subst hr
        rw [hst] at hrl
        cases hrl
    · rw [hspent]
      exact h.cap_nonneg
    · rw [hspent]
      exact h.cap_le
  | true =>
    by_cases ht : P.hitlThreshold ≤ n
    · obtain ⟨hst, -, hnot, hpend, hspent, hid2, -⟩ := evalCore_hitl hb ht
      refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_,
                         nonneg := ?_ },
               safe := ?_, cap_nonneg := ?_, cap_le := ?_ }
      · intro p hp
        rw [hpend] at hp
        rw [hnid]
        rcases List.mem_cons.mp hp with rfl | hpold
        · show g.nextId < g.nextId + 1
          omega
        · have hlt := h.pend.keys_lt p hpold
          omega
      · rw [hpend]
        show List.Nodup (g.nextId :: g.pending.map Prod.fst)
        refine List.nodup_cons.mpr ⟨?_, h.pend.nodup⟩
        intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨q, hq, hqf⟩ := hmem
        have hlt := h.pend.keys_lt q hq
        omega
      · intro p hp
        rw [hpend] at hp
        rcases List.mem_cons.mp hp with rfl | hpold
        · refine ⟨(evalCore P g chk cap n).2, ?_, hid2, hst, ?_⟩
          · rw [hrecs]
            exact List.mem_append.mpr
              (Or.inr (List.mem_singleton.mpr rfl))
          · exact hnot
        · obtain ⟨r, hr, hrid, hrst, hrnot⟩ := h.pend.backed p hpold
          exact ⟨r, by rw [hrecs]; exact List.mem_append.mpr (Or.inl hr),
            hrid, hrst, hrnot⟩
      · intro p hp
        rw [hpend] at hp
        rcases List.mem_cons.mp hp with rfl | hpold
        · exact hardOk_nonneg hb
        · exact h.pend.nonneg p hpold
      · intro r hr hrl
        rw [hrecs] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact h.safe r hr hrl
        · rw [List.mem_singleton] at hr
          subst hr
          rw [hst] at hrl
          cases hrl
      · rw [hspent]
        exact h.cap_nonneg
      · rw [hspent]
        exact h.cap_le
    · have hlt : n < P.hitlThreshold := by omega
      obtain ⟨hst, -, hnot, hspent, hpend⟩ := evalCore_locked hb hlt
      refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_,
                         nonneg := ?_ },
               safe := ?_, cap_nonneg := ?_, cap_le := ?_ }
      · intro p hp
        rw [hpend] at hp
        rw [hnid]
        have hlk := h.pend.keys_lt p hp
        omega
      · rw [hpend]
        exact h.pend.nodup
      · intro p hp
        rw [hpend] at hp
        obtain ⟨r, hr, hrid, hrst, hrnot⟩ := h.pend.backed p hp
        exact ⟨r, by rw [hrecs]; exact List.mem_append.mpr (Or.inl hr),
          hrid, hrst, hrnot⟩
      · intro p hp
        rw [hpend] at hp
        exact h.pend.nonneg p hp
      · intro r hr hrl
        rw [hrecs] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact h.safe r hr hrl
        · rw [List.mem_singleton] at hr
          subst hr
          exact Or.inl (by rw [hnot]; exact hlt)
      · rw [hspent]
        have hnn := hardOk_nonneg hb
        have hsp0 := h.cap_nonneg
        omega
      · rw [hspent]
        exact (hardOk_components hb).1.2

/-- `evaluate` (with the window roll) preserves the invariant. -/
theorem evalStep_inv {P : Policy} (hP : 0 ≤ P.dailyCap) {g : Gate}
    (h : Inv P g) (now : Int) (chk : Checks) (cap n : Int) :
    Inv P (evalStep P g now chk cap n).1 :=
  evalCore_inv (roll_inv hP h now) chk cap n

/-- `approveHuman` preserves the invariant, in both outcome branches;
    the throw path changes nothing (see `approve_unknown`). -/
theorem approveStep_inv {P : Policy} (hP : 0 ≤ P.dailyCap) {g : Gate}
    (h : Inv P g) (now : Int) (id : Nat) :
    Inv P (approveStep P g now id).1 := by
  cases hfv : findV g.pending id with
  | none =>
    rw [approve_unknown hfv]
    exact h
  | some n =>
    have hmem : (id, n) ∈ g.pending := findV_mem hfv
    have hn_nonneg : 0 ≤ n := h.pend.nonneg _ hmem
    have hR : Inv P (roll g now) := roll_inv hP h now
    have hpend : (approveStep P g now id).1.pending = eraseId g.pending id :=
      approve_pending_erased hfv
    by_cases hc : P.dailyCap < (roll g now).spent + n ∨ P.maxNotional < n
    · have hrecs : (approveStep P g now id).1.records
          = g.records ++
            [{ id := (roll g now).nextId, st := .blocked, notional := n,
               byHuman := false }] := by
        have h1 : (approveStep P g now id).1.records
            = (roll g now).records ++
              [{ id := (roll g now).nextId, st := .blocked, notional := n,
                 byHuman := false }] := by
          simp [approveStep, hfv, hc]
        rwa [roll_records] at h1
      have hspent : (approveStep P g now id).1.spent = (roll g now).spent := by
        simp [approveStep, hfv, hc]
      have hnid : (approveStep P g now id).1.nextId = g.nextId + 1 := by
        have h1 : (approveStep P g now id).1.nextId
            = (roll g now).nextId + 1 := by
          simp [approveStep, hfv, hc]
        rwa [roll_nextId] at h1
      refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_,
                         nonneg := ?_ },
               safe := ?_, cap_nonneg := ?_, cap_le := ?_ }
      · intro p hp
        rw [hpend] at hp
        have hlt := h.pend.keys_lt p (mem_eraseId hp)
        rw [hnid]
        omega
      · rw [hpend]
        exact nodup_eraseId h.pend.nodup
      · intro p hp
        rw [hpend] at hp
        obtain ⟨r, hr, hrid, hrst, hrnot⟩ :=
          h.pend.backed p (mem_eraseId hp)
        exact ⟨r, by rw [hrecs]; exact List.mem_append.mpr (Or.inl hr),
          hrid, hrst, hrnot⟩
      · intro p hp
        rw [hpend] at hp
        exact h.pend.nonneg p (mem_eraseId hp)
      · intro r hr hrl
        rw [hrecs] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact h.safe r hr hrl
        · rw [List.mem_singleton] at hr
          subst hr
          simp at hrl
      · rw [hspent]
        exact hR.cap_nonneg
      · rw [hspent]
        exact hR.cap_le
    · have hrecs : (approveStep P g now id).1.records
          = g.records ++
            [{ id := (roll g now).nextId, st := .locked, notional := n,
               byHuman := true }] := by
        have h1 : (approveStep P g now id).1.records
            = (roll g now).records ++
              [{ id := (roll g now).nextId, st := .locked, notional := n,
                 byHuman := true }] := by
          simp [approveStep, hfv, hc]
        rwa [roll_records] at h1
      have hspent : (approveStep P g now id).1.spent
          = (roll g now).spent + n := by
        simp [approveStep, hfv, hc]
      have hnid : (approveStep P g now id).1.nextId = g.nextId + 1 := by
        have h1 : (approveStep P g now id).1.nextId
            = (roll g now).nextId + 1 := by
          simp [approveStep, hfv, hc]
        rwa [roll_nextId] at h1
      have hc' := not_or.mp hc
      have h1le := hc'.1
      refine { pend := { keys_lt := ?_, nodup := ?_, backed := ?_,
                         nonneg := ?_ },
               safe := ?_, cap_nonneg := ?_, cap_le := ?_ }
      · intro p hp
        rw [hpend] at hp
        have hlt := h.pend.keys_lt p (mem_eraseId hp)
        rw [hnid]
        omega
      · rw [hpend]
        exact nodup_eraseId h.pend.nodup
      · intro p hp
        rw [hpend] at hp
        obtain ⟨r, hr, hrid, hrst, hrnot⟩ :=
          h.pend.backed p (mem_eraseId hp)
        exact ⟨r, by rw [hrecs]; exact List.mem_append.mpr (Or.inl hr),
          hrid, hrst, hrnot⟩
      · intro p hp
        rw [hpend] at hp
        exact h.pend.nonneg p (mem_eraseId hp)
      · intro r hr hrl
        rw [hrecs] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact h.safe r hr hrl
        · rw [List.mem_singleton] at hr
          subst hr
          exact Or.inr rfl
      · rw [hspent]
        have hnn := hR.cap_nonneg
        omega
      · rw [hspent]
        omega

/-! ## Reachability and the headline corollaries -/

/-- Reachable gate states: the empty gate closed under `evaluate` and
    `approveHuman` steps (the gate's entire public mutation surface,
    modulo policy hot-reload — see NOTES.md). -/
inductive Reach (P : Policy) : Gate → Prop where
  | init : Reach P (initialGate 0)
  | eval {g : Gate} (now : Int) (chk : Checks) (cap n : Int) :
      Reach P g → Reach P (evalStep P g now chk cap n).1
  | approve {g : Gate} (now : Int) (id : Nat) :
      Reach P g → Reach P (approveStep P g now id).1

/-- Every reachable state satisfies the invariant. -/
theorem reach_inv {P : Policy} (hP : 0 ≤ P.dailyCap) {g : Gate}
    (h : Reach P g) : Inv P g := by
  induction h with
  | init => exact initial_inv hP
  | eval now chk cap n _ ih => exact evalStep_inv hP ih now chk cap n
  | approve now id _ ih => exact approveStep_inv hP ih now id

/-- **HEADLINE 1 — no unapproved execution.** In every reachable state,
    every LOCKED record either is below the HITL threshold or carries a
    recorded human approval. Contrapositive: an at/above-threshold
    action can never appear LOCKED without `byHuman = true`. -/
theorem no_unapproved_execution {P : Policy} (hP : 0 ≤ P.dailyCap)
    {g : Gate} (hR : Reach P g) {r : Record} (hr : r ∈ g.records)
    (hl : r.st = .locked) :
    r.notional < P.hitlThreshold ∨ r.byHuman = true :=
  (reach_inv hP hR).safe r hr hl

/-- **HEADLINE 2 — pending entries are genuine HITL records.** Every id
    sitting in the pending map is backed, in the same state's provenance
    list, by a HITL_REQUIRED record with the pending id and notional —
    so `approveHuman` can only ever act on a decision that `evaluate`
    actually escalated. -/
theorem pending_backed {P : Policy} (hP : 0 ≤ P.dailyCap) {g : Gate}
    (hR : Reach P g) {id : Nat} {n : Int} (hf : findV g.pending id = some n) :
    ∃ r ∈ g.records, r.id = id ∧ r.st = .hitlRequired ∧ r.notional = n :=
  (reach_inv hP hR).pend.backed _ (findV_mem hf)

/-- **HEADLINE 3 — every human-approved LOCKED record traces back to a
    genuine HITL escalation.** If `approveHuman` on a reachable state
    returns a LOCKED record, the record is human-stamped and the same
    pre-state holds a HITL_REQUIRED provenance record with the approved
    id and the same notional: approvals cannot be forged, replayed
    (see `no_double_approve`), or attached to actions that never crossed
    the threshold path. -/
theorem approve_locked_traces {P : Policy} (hP : 0 ≤ P.dailyCap)
    {g : Gate} (hR : Reach P g) {now : Int} {id : Nat} {rec : Record}
    (hres : (approveStep P g now id).2 = some rec) (hl : rec.st = .locked) :
    rec.byHuman = true ∧
    ∃ r ∈ g.records, r.id = id ∧ r.st = .hitlRequired ∧
      r.notional = rec.notional := by
  have hInv := reach_inv hP hR
  obtain ⟨hf, hbh, -, -, -, -⟩ := approve_locked_facts hres hl
  have hmem : (id, rec.notional) ∈ g.pending := findV_mem hf
  obtain ⟨r, hr, hrid, hrst, hrnot⟩ := hInv.pend.backed _ hmem
  exact ⟨hbh, r, hr, hrid, hrst, hrnot⟩

/-! ## The finance-analysis adapter: reviewer binding

    `src/finance-analysis.ts` wraps the gate: `assignReviewer`
    (lines 341–356) records who may approve a pending decision —
    checking the decision is pending and, when a reviewer pool is
    configured, that the reviewer belongs to it; `approveCommentary`
    (lines 359–368) refuses unless the approver is the assigned
    reviewer, and only then calls `gate.approveHuman`. (Simplification:
    if the pending entry was consumed between assignment and approval,
    the real `approveHuman` throws; the model returns the gate's
    `none`-decision outcome instead.) -/

/-- Finance-adapter state: the gate plus the reviewer-assignment map
    (`Map<decisionId, reviewerId>` in the source). -/
structure FinanceState where
  gate : Gate
  assigned : List (Nat × String)

/-- `assignReviewer`: fails (modelled as `none`) unless the decision is
    pending in the gate and — when a pool is configured — the reviewer
    is in the pool. -/
def assignReviewer (fs : FinanceState) (pool : Option (List String))
    (id : Nat) (rev : String) : Option FinanceState :=
  match findV fs.gate.pending id with
  | none => none
  | some _ =>
    match pool with
    | some ps => if rev ∈ ps then
        some { fs with assigned := (id, rev) :: fs.assigned } else none
    | none => some { fs with assigned := (id, rev) :: fs.assigned }

/-- Assignment requires a genuinely pending decision. -/
theorem assignReviewer_pending {fs : FinanceState}
    {pool : Option (List String)} {id : Nat} {rev : String}
    {fs' : FinanceState} (h : assignReviewer fs pool id rev = some fs') :
    ∃ n, findV fs.gate.pending id = some n := by
  cases hfv : findV fs.gate.pending id with
  | none => simp [assignReviewer, hfv] at h
  | some n =>
    cases pool with
    | none => exact ⟨n, rfl⟩
    | some ps =>
      by_cases hm : rev ∈ ps
      · exact ⟨n, rfl⟩
      · simp [assignReviewer, hfv, hm] at h

/-- `approveCommentary`: the approver must equal the recorded assignee
    for this decision id; the call then delegates to the gate. -/
def approveCommentary (P : Policy) (fs : FinanceState) (now : Int)
    (id : Nat) (approver : String) : Option (Gate × Option Record) :=
  match findV fs.assigned id with
  | some rev =>
    if rev = approver then some (approveStep P fs.gate now id) else none
  | none => none

/-- **Reviewer binding.** A successful `approveCommentary` proves the
    approver is exactly the reviewer recorded for the decision — the
    adapter-level check the core gate itself does NOT perform (any
    non-empty identity may call `ChpGate.approveHuman` directly). -/
theorem approveCommentary_binding {P : Policy} {fs : FinanceState}
    {now : Int} {id : Nat} {approver : String}
    {st : Gate × Option Record}
    (h : approveCommentary P fs now id approver = some st) :
    findV fs.assigned id = some approver ∧
    st = approveStep P fs.gate now id := by
  cases hfa : findV fs.assigned id with
  | none => simp [approveCommentary, hfa] at h
  | some rev =>
    by_cases he : rev = approver
    · have h2 : approveCommentary P fs now id approver
          = some (approveStep P fs.gate now id) := by
        simp [approveCommentary, hfa, he]
      rw [h2] at h
      exact ⟨by rw [he], (Option.some.inj h).symm⟩
    · simp [approveCommentary, hfa, he] at h

/-- So a commentary approval that ends LOCKED traces back through the
    adapter binding to a genuine HITL escalation of the underlying
    gate. -/
theorem approveCommentary_traces {P : Policy} (hP : 0 ≤ P.dailyCap)
    {fs : FinanceState} (hR : Reach P fs.gate) {now : Int} {id : Nat}
    {approver : String} {st : Gate × Option Record} {rec : Record}
    (h : approveCommentary P fs now id approver = some st)
    (hrec : st.2 = some rec) (hl : rec.st = .locked) :
    findV fs.assigned id = some approver ∧ rec.byHuman = true ∧
    ∃ r ∈ fs.gate.records, r.id = id ∧ r.st = .hitlRequired ∧
      r.notional = rec.notional := by
  obtain ⟨hb, hst⟩ := approveCommentary_binding h
  subst hst
  obtain ⟨hbh, htr⟩ := approve_locked_traces hP hR hrec hl
  exact ⟨hb, hbh, htr⟩

/-! ## The Order aggregate: live transitions vs replay

    `src/domain-events.ts` has two paths over the same lifecycle. The
    live aggregate (`Order.fill` / `Order.cancel`, lines 281–293)
    throws unless the current status is `"open"`. The replay path
    (`Order.apply`, lines 323–355, used by `Order.fromEvents`) sets the
    status with NO guard. -/

inductive OStatus where
  | open | filled | cancelled
  deriving DecidableEq, Repr

inductive OEvent where
  | opened | fill | cancel
  deriving DecidableEq, Repr

/-- Live transition: applies only from `open`. -/
def liveApply : OStatus → OEvent → Option OStatus
  | .open, .fill => some .filled
  | .open, .cancel => some .cancelled
  | _, _ => none

/-- Replay transition: unguarded overwrite, as in `Order.apply`. -/
def replayApply : OStatus → OEvent → OStatus
  | s, .opened => s
  | _, .fill => .filled
  | _, .cancel => .cancelled

/-- Terminal states are one-way on the live path: from `filled` or
    `cancelled`, no event applies. -/
theorem live_terminal {s : OStatus} {e : OEvent} (h : s ≠ .open) :
    liveApply s e = none := by
  cases s
  · exact absurd rfl h
  · cases e <;> decide
  · cases e <;> decide

/-- Left-fold of a stream through the replay transition, starting from
    the freshly-opened state (`Order.fromEvents` requires the stream
    to start with `order.opened`, a no-op here). -/
def replayFrom (s : OStatus) : List OEvent → OStatus
  | [] => s
  | e :: t => replayFrom (replayApply s e) t

/-- Left-fold of a stream through the live transition; `none` if any
    step is rejected. -/
def liveRun (s : OStatus) : List OEvent → Option OStatus
  | [] => some s
  | e :: t => (liveApply s e).bind (fun s' => liveRun s' t)

/-- **Live vs replay divergence (concrete counterexample).** The stream
    `opened → filled → cancelled`, which the live aggregate rejects at
    the last step, replays cleanly — to `cancelled`, a state the live
    lifecycle can never reach from `filled`. -/
theorem replay_overwrites_terminal :
    replayFrom .open [.opened, .fill, .cancel] = .cancelled := by decide

/-- The same stream on the live path is rejected. -/
theorem live_rejects_same_stream :
    liveRun .open [.fill, .cancel] = none := by decide

/-! ## The audit ledger

    `AuditLedger` (`src/ledger.ts`) is append-only by construction:
    the class exposes no update/delete/rewrite method, each append
    writes exactly one new line whose `prev_sig` is the previous tail
    signature (`appendUnlocked`, lines 323–345), and `verifyLedger`
    re-derives the HMAC chain to detect edits. The HMAC itself is
    abstracted to an opaque `sig` function (keyed-hash internals are
    irrelevant to the append/linkage properties). -/

/-- One ledger line: payload, previous signature, own signature. -/
structure Entry where
  payload : String
  prevSig : Nat
  sig : Nat
  deriving DecidableEq, Repr

/-- Chain state: the last signature written (0 stands in for the
    code's GENESIS seed) and the entries so far, oldest first. -/
structure Chain where
  lastSig : Nat
  entries : List Entry

/-- Append one entry: its `prevSig` is the current tail signature and
    the tail advances to the new entry's signature. -/
def appendEntry (sig : Nat → String → Nat) (c : Chain) (payload : String) :
    Chain :=
  let s := sig c.lastSig payload
  { lastSig := s,
    entries := c.entries ++
      [{ payload := payload, prevSig := c.lastSig, sig := s }] }

theorem appendEntry_entries (sig : Nat → String → Nat) (c : Chain)
    (p : String) :
    (appendEntry sig c p).entries
      = c.entries ++
        [{ payload := p, prevSig := c.lastSig, sig := sig c.lastSig p }] :=
  rfl

/-- **Append-only growth.** Each append extends the entry list by a
    one-element suffix: every earlier state of the list is a prefix of
    every later one. Nothing already written is ever removed or
    rewritten by the model — matching the class's API surface. -/
theorem appendEntry_isPrefix (sig : Nat → String → Nat) (c : Chain)
    (p : String) :
    List.IsPrefix c.entries (appendEntry sig c p).entries :=
  ⟨[{ payload := p, prevSig := c.lastSig, sig := sig c.lastSig p }],
    by rw [appendEntry_entries]⟩

/-- **Chain linkage.** The entry an append writes points back at the
    previous tail signature, and the chain tail becomes that entry's
    signature — the invariant `verifyLedger` re-checks on read. -/
theorem appendEntry_link (sig : Nat → String → Nat) (c : Chain)
    (p : String) :
    ∃ e, (appendEntry sig c p).entries = c.entries ++ [e] ∧
      e.prevSig = c.lastSig ∧ e.sig = (appendEntry sig c p).lastSig :=
  ⟨{ payload := p, prevSig := c.lastSig, sig := sig c.lastSig p },
    appendEntry_entries sig c p, rfl, rfl⟩

end Governance
