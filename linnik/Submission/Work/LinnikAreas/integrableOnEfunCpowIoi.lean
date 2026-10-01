import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open MeasureTheory DirichletCharacter Complex
open scoped BigOperators
noncomputable section

/-- `Asum χ` is a measurable step function: composition of the floor map with the
prefix sum. -/
lemma measurable_Asum' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Measurable fun t : ℝ => Asum χ t := by
  have h : (fun t : ℝ => Asum χ t)
      = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, lam χ n) ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [h]
  exact (measurable_of_countable _).comp Nat.floor_mono.measurable

/-- `Efun χ t = Asum χ t - t·L(1,χ)` is measurable in `t`. -/
lemma measurable_Efun_cpow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Measurable fun t : ℝ => Efun χ t :=
  (measurable_Asum' χ).sub
    (Complex.continuous_ofReal.measurable.mul measurable_const)

/-- **Integrability of `E(t) t^{-(β+1)}` on `(1, ∞)`.**

If `‖E(t)‖ ≤ K √t` for `t ≥ 1` (the standard `A(x) = x·L(1,χ) + O(√x)` input), then for
`β > 1/2` the function `t ↦ E(t) t^{-(β+1)}` is integrable on `(1, ∞)`: indeed its norm is
dominated by `K t^{-β-1/2}`, and `-β - 1/2 < -1`. -/
theorem integrableOnEfunCpowIoi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K β : ℝ} (hK : 0 ≤ K)
    (hE : ∀ t : ℝ, 1 ≤ t → ‖Work.LinnikAreas.Efun χ t‖ ≤ K * Real.sqrt t)
    (hβ : 1/2 < β) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1))) (Set.Ioi 1) := by
  have hr : -β - 1/2 < (-1 : ℝ) := by linarith
  have hbnd : IntegrableOn (fun t : ℝ => K * t ^ (-β - 1/2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hr (by norm_num : (0:ℝ) < 1)).const_mul K
  refine Integrable.mono' hbnd ?_ ?_
  · have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-((β : ℂ) + 1))) (Set.Ioi 1) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
      exact (Complex.continuousAt_ofReal_cpow_const t (-((β : ℂ) + 1))
        (Or.inr ht0)).continuousWithinAt
    exact (measurable_Efun_cpow χ).aestronglyMeasurable.mul
      (hcont.aestronglyMeasurable measurableSet_Ioi)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    calc ‖Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1))‖
        = ‖Efun χ t‖ * t ^ (-(β + 1)) := by
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp [Complex.neg_re, Complex.add_re]
      _ ≤ (K * Real.sqrt t) * t ^ (-(β + 1)) :=
          mul_le_mul_of_nonneg_right (hE t ht1) (Real.rpow_nonneg (le_of_lt ht0) _)
      _ = K * t ^ (-β - 1/2) := by
          have he : (1/2 : ℝ) + (-(β + 1)) = -β - 1/2 := by ring
          rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht0, he]

end
end Work.LinnikAreas
