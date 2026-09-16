import Submission.ZagierHoffmanProof.StepL12

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L13: B*_v on the iterated relation (Prop 2.12's (2.13))

`bstarRelData` is the S-level B*_v on RelData with level-validity (plug of
`bstar_pure`, paper (2.13) first line).  `RelData.BCqIter_head_one` records that the
`b`-tuples of every `BC_q`-iterate of a BinaryRel with `1`-headed `b`-tuples again
have head `1` (covering both `n = 0` and `n ≥ 1` via `BCqIter_cB_head`).
`bstar_iterated` is Prop 2.12's `B*_{s_j}` step applied to the `n`-iterate: the
fixed three-family level-`d` relation, with the merge condition `s_j + 1 ≤ q`
reduced to the hypothesis `(v : ℕ) + 1 ≤ Nat.card F`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ B*_v on a RelData with level-validity, S-level per `d`: the fixed three-family
relation (paper (2.13) first line), plug of `bstar_pure` on the bare families. -/
theorem bstarRelData (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) :
    ∀ d : ℕ,
      (∑ i : D.ιA, (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (D.depA i + 1) (by omega : 0 < D.depA i + 1) (consVec v (D.cA i)) d)) +
      (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (D.depB p + 1) (by omega : 0 < D.depB p + 1) (consVec v (D.cB p)) d)) +
      (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (D.depB p) (D.hdepB p) (headAdd v (D.hdepB p) (D.cB p)) d)) = 0 := by
  intro d
  exact bstar_pure F (depA := D.depA) (hdepA := D.hdepA) (cA := D.cA) (aA := D.aA)
    (depB := D.depB) (hdepB := D.hdepB) (hB2 := D.hB2) (cB := D.cB) (aB := D.aB)
    v (fun e => by simpa [RelData.level] using hvalid e) hv d

/-- b-heads of the `n`-iterate of a BinaryRel are `1` at every step, provided they are
`1` initially (covers `n = 0`; for `n ≥ 1` this is `BCqIter_cB_head`). -/
lemma RelData.BCqIter_head_one : ∀ (n : ℕ) (R : BinaryRel F),
    (∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) →
    ∀ p : (RelData.BCqIter F n (toData F R)).ιB,
      ((RelData.BCqIter F n (toData F R)).cB p) ⟨0, (RelData.BCqIter F n (toData F R)).hdepB p⟩ = oneExp := by
  classical
  intro n R hbhead
  cases n with
  | zero =>
      intro p
      -- (BCqIter 0 (toData R)) = toData R
      change ((toData F R).cB p) ⟨0, (toData F R).hdepB p⟩ = oneExp
      have hh : ((R.cB p) ⟨0, R.hdepB p⟩ : ℕ) = 1 := hbhead p
      apply Subtype.ext
      change (((toData F R).cB p) ⟨0, (toData F R).hdepB p⟩ : ℕ) = 1
      simpa [toData] using hh
  | succ m =>
      intro p
      -- BCqIter (m+1) (toData R) heads are oneExp (BCqIter_cB_head)
      exact RelData.BCqIter_cB_head F m (toData F R) p

/-- ★ The B*_{s_j} step applied to the `n`-iterate of a BinaryRel with `1`-headed
`b`-tuples: fixed validity at every level, merge condition `v + 1 ≤ q`. -/
theorem bstar_iterated (n : ℕ) (R : BinaryRel F) (v : ℕ+)
    (hvq : (v : ℕ) + 1 ≤ Nat.card F)
    (hbhead : ∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) :
    ∀ d : ℕ,
      (∑ i : (RelData.BCqIter F n (toData F R)).ιA,
          (((RelData.BCqIter F n (toData F R)).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
            S F ((RelData.BCqIter F n (toData F R)).depA i + 1) (by omega : 0 < (RelData.BCqIter F n (toData F R)).depA i + 1)
              (consVec v ((RelData.BCqIter F n (toData F R)).cA i)) d) +
      (∑ p : (RelData.BCqIter F n (toData F R)).ιB,
          (((RelData.BCqIter F n (toData F R)).aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
            S F ((RelData.BCqIter F n (toData F R)).depB p + 1) (by omega : 0 < (RelData.BCqIter F n (toData F R)).depB p + 1)
              (consVec v ((RelData.BCqIter F n (toData F R)).cB p)) d) +
      (∑ p : (RelData.BCqIter F n (toData F R)).ιB,
          (((RelData.BCqIter F n (toData F R)).aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
            S F ((RelData.BCqIter F n (toData F R)).depB p) ((RelData.BCqIter F n (toData F R)).hdepB p)
              (headAdd v ((RelData.BCqIter F n (toData F R)).hdepB p) ((RelData.BCqIter F n (toData F R)).cB p)) d) = 0 := by
  classical
  intro d
  let D : RelData F := RelData.BCqIter F n (toData F R)
  have hvalid : ∀ e : ℕ, RelData.level F D e = 0 := by
    intro e
    dsimp [D]
    exact BCqIter_valid F n R e
  have hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F := by
    intro p
    have hh := RelData.BCqIter_head_one F n R hbhead p
    -- hh : (D.cB p) head = oneExp ; so the value is 1
    have hv1 : ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) = 1 := by
      -- (oneExp : ℕ) = 1
      calc
        ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) = (oneExp : ℕ) := by simpa [D] using congrArg (fun t : ℕ+ => (t : ℕ)) hh
        _ = 1 := by simp [oneExp]
    omega
  exact bstarRelData F D v hvalid hv d

end ZagierHoffmanPositiveChar
