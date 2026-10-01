import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

/-- The function `E(x) = A(x) - x L(1,χ)` is `O(√x)` along the reals, in the precise sense that
the truncation `1_{x>1} E(x)` is `O(x^{1/2})` at `+∞`.

The hypothesis `hE` is the unconditionally available bound (Pólya–Vinogradov-type) on the
error term; the content of the lemma is only the translation of the pointwise bound
`‖E(x)‖ ≤ K √x` for `x ≥ 1` into the asymptotic statement, the values `x ≤ 1` being irrelevant
because they are cut off by the indicator. -/
theorem efunIndicatorBigO {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x) :
    (Set.indicator (Set.Ioi (1:ℝ)) (Work.LinnikAreas.Efun χ))
      =O[Filter.atTop] (fun t : ℝ => t ^ ((1:ℝ)/2)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨K, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with t ht
  have ht1 : (1:ℝ) ≤ t := le_of_lt ht
  have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht1
  rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1:ℝ) from ht)]
  have hsqrt : Real.sqrt t = ‖t ^ ((1:ℝ)/2)‖ := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.norm_of_nonneg (Real.rpow_nonneg ht0 _)).symm
  calc ‖Work.LinnikAreas.Efun χ t‖ ≤ K * Real.sqrt t := hE t ht1
    _ = K * ‖t ^ ((1:ℝ)/2)‖ := by rw [hsqrt]

end Work.LinnikAreas
