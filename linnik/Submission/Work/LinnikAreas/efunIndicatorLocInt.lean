/-
# Local integrability of `1_{x > 1} · E(x)`

The error term `E(x) = A(x) - x·L(1,χ)` of the divisor function `λ = 1 * χ` is a step
function: it depends on `x` only through `⌊x⌋₊`, so it is (Borel) measurable.  Under the
crude bound `‖E(x)‖ ≤ K √x` for `x ≥ 1` (the Pólya–Vinogradov type estimate available for
this application, see `Work.LinnikAreas.efunBound`) the truncated function
`x ↦ 1_{x > 1} E(x)` is dominated by the locally integrable function
`x ↦ max K 0 · √(max x 1)`, hence is itself locally integrable on `(0,∞)`.

This is the measurability/integrability input needed to form the Mellin transform and the
integrals `∫_1^∞ E(x) x^{-1-β} dx` appearing in the continuation argument.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open DirichletCharacter MeasureTheory

variable {q : ℕ} [NeZero q]

/-- `Asum χ` depends on `x` only through `⌊x⌋₊`, hence `Efun χ` is (Borel) measurable. -/
lemma measurable_Efun (χ : DirichletCharacter ℂ q) : Measurable (Efun χ) := by
  have hAsum : Asum χ = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, lam χ n) ∘ Nat.floor := rfl
  change Measurable (fun x : ℝ => Asum χ x - (x : ℂ) * LFunction χ 1)
  refine Measurable.sub ?_ ?_
  · rw [hAsum]
    exact (measurable_of_countable _).comp Nat.measurable_floor
  · exact (Complex.continuous_ofReal.mul continuous_const).measurable

theorem efunIndicatorLocInt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x) :
    MeasureTheory.LocallyIntegrableOn
      (Set.indicator (Set.Ioi (1:ℝ)) (Work.LinnikAreas.Efun χ)) (Set.Ioi 0) := by
  set K' : ℝ := max K 0 with hK'def
  have hK'nn : 0 ≤ K' := le_max_right _ _
  -- The dominating function `x ↦ K' √(max x 1)` is continuous, hence locally integrable.
  have hdom : LocallyIntegrableOn (fun t : ℝ => K' * Real.sqrt (max t 1)) (Set.Ioi 0) :=
    ((continuous_const.mul
        (Real.continuous_sqrt.comp (continuous_id.max continuous_const))).locallyIntegrable).locallyIntegrableOn _
  refine hdom.mono ((measurable_Efun χ).indicator measurableSet_Ioi).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_of_nonneg (mul_nonneg hK'nn (Real.sqrt_nonneg _))]
  by_cases ht : t ∈ Set.Ioi (1 : ℝ)
  · -- `t > 1`: the indicator is active and `hE` applies at `x = t`.
    rw [Set.indicator_of_mem ht]
    have h1t : (1 : ℝ) ≤ t := le_of_lt ht
    have h := hE t h1t
    rw [max_eq_left h1t]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.sqrt_nonneg t))
  · -- `t ≤ 1`: the indicator vanishes.
    rw [Set.indicator_of_notMem ht, norm_zero]
    exact mul_nonneg hK'nn (Real.sqrt_nonneg _)

end Work.LinnikAreas
