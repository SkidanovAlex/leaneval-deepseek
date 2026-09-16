import Submission.ZagierHoffmanProof.StepL6

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L7: the ζ-level bridge for binary relations (paper Remark 2.4)

`BinaryRel.zeta` is the ζ-level value of a relation: the same `K∞`-linear combination as
its level value but with each `S_e`/`S_{e+1}` replaced by `ζ_A`.  `BinaryRel.zeta_zero`
sums a valid relation over all levels: since every `b`-tuple has depth ≥ 2, its
level-0 power sum vanishes and the mixed bridge (StepL1) turns the level-wise identity
into the ζ-level identity — the paper's Remark 2.4 / the ζ-form of every relation
built by Lemma 2.9, Prop 2.10 (`BC_q`) and the `BC_q`-iteration of Prop 2.12.

`BCqIter_zeta_zero` is the engine of Prop 2.12 at the ζ level: after `n` applications
of Prop 2.10 to the relation of (2.10), the reindexed relation is ζ-valid, i.e. the
ζ-level identity (2.11)/(2.12) of the paper holds.
-/

namespace ZagierHoffmanPositiveChar

attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The ζ-level value of a binary relation:
`Σ_i (aA i)·ζ_A(cA i) + Σ_j (aB j)·ζ_A(cB j)` in `K∞`. -/
noncomputable def BinaryRel.zeta (R : BinaryRel F) : RatFunc.CompletionAtInfty F :=
  (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (R.cA i))) +
  (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (R.cB j)))

/-- ★ A valid binary relation is ζ-valid: summing its level-wise relation over all
levels yields the ζ-level identity (the sum over `d` of the Lemma 2.9 / Prop 2.12-type
relations; paper Remark 2.4).  Uses the mixed bridge — the `b`-tuples all have depth
≥ 2 (`hB2`), hence their level-0 power sum vanishes. -/
theorem BinaryRel.zeta_zero (R : BinaryRel F) : BinaryRel.zeta F R = 0 := by
  classical
  unfold BinaryRel.zeta
  exact zeta_mixed_bridge F
    (depA := R.depA) (hdepA := R.hdepA) (cA := R.cA) (aA := R.aA)
    (depB := R.depB) (hdepB := R.hdepB) (cB := R.cB) (aB := R.aB)
    (h0B := fun j => S_zero_of_depth_ge_two F (R.hdepB j) (R.hB2 j) (R.cB j))
    R.valid

/-- ★ The `BC_q`-iterated relation (any number `n` of iterations of Prop 2.10) is
ζ-valid.  This is paper (2.11)/(2.12) at the ζ level — the engine of Prop 2.12's
prefix-lowering (`n = k−j−1` applications to the relation of (2.10)). -/
theorem BCqIter_zeta_zero (n : ℕ) (R : BinaryRel F) :
    BinaryRel.zeta F
      (RelData.toBinaryRel F (RelData.BCqIter F n (toData F R)) (BCqIter_valid F n R)) = 0 := by
  exact BinaryRel.zeta_zero F
    (RelData.toBinaryRel F (RelData.BCqIter F n (toData F R)) (BCqIter_valid F n R))

end ZagierHoffmanPositiveChar
