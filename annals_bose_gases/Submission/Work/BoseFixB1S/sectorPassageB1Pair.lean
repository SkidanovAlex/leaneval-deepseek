import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.sectorPassageB1Support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.sectorPassageB1Pair` — the pair term is a *positive* payer

The localised two-body kernel is a product of nonnegative factors when its numerator is (the
potential `v ≥ 0`), so the pair term `½ Σ_{i≠j} ∫Φ² w(x_i,x_j)` of `qLHSwordB` is a *nonnegative*
contribution to the word.  Unlike the fibre term (which enters `qLHSwordB` with a minus sign and
therefore cannot pay a positive remainder), this is the payer for the *one-sided excess*
`5γWμ·(1/χ)∫Φ²(N − χs)₊` produced by `psiWeight_one_le_add_pos` on spread states.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The localised pair kernel is nonnegative** when the numerator is nonnegative at the evaluated
pair: `χ_{B(u)}(x)·(f(x−y)/((χ_M⋆χ_M)(x−y)/(ℓd)) /(χ⋆χ)(x−y))·χ_{B(u)}(y) ≥ 0`. -/
theorem wSmallPair_nonneg_B1S {M : ℕ} {ℓ d : ℝ} (u x y : EuclideanSpace ℝ (Fin 3))
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : 0 ≤ f (x - y)) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  exact mul_nonneg
    (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
      (div_nonneg
        (div_nonneg hf (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y)))
        (Submission.BoseGases.convScale_nonneg ℓ (x - y))))
    (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u y)

/-- **The one-sided excess is dominated by the count** (the input the spread payment consumes):
`(nCountB − chiMass·s)₊ ≤ ν Σ_i χ_{B(u)}(x_i)` for `s ≥ 0`. -/
theorem max_sub_mul_chi_le_nu_mul_sum {M : ℕ} (hM : 1 ≤ M) {ℓ d s : ℝ} (hs : 0 ≤ s)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : Submission.BoseGases.X n) :
    max (Work.BoseFixB1.nCountB M ℓ d u x
        - Work.SmallBoxSliding.chiMass M ℓ d u * s) 0
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
  refine max_le ?_ ?_
  · have h := nCountB_le_nu_mul_sum_chiSmallB (ℓ := ℓ) (d := d) hM u x
    have hnn : 0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u * s :=
      mul_nonneg (Work.SmallBoxSliding.chiMass_nonneg M ℓ d u) hs
    linarith
  · exact mul_nonneg
      (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
        (Submission.BoseGases.chiSmallDecay_nonneg M))
      (Finset.sum_nonneg fun i _ => Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i))

end Work.BoseFixB1S
