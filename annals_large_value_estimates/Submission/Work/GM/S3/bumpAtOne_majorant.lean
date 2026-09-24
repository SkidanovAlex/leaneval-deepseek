import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

namespace Work.GM.S3

/-- **A bump at `1` majorizing `[1/8, 33/8]` with support in `[1/16, 16]`.**  (Take
`ψ x = Real.smoothTransition (16 * x - 1) * Real.smoothTransition (16 * (8 - x))`: it equals `1`
for `x ∈ [1/8, 8 - 1/16] ⊇ [1/8, 33/8]`, vanishes unless `1/16 < x < 8`, is nonnegative, has
`ψ 1 = 1`, and is `C^∞` with compact support; the `j`-th derivative bounds come from smoothness
plus compact support.  `Real.smoothTransition` and its API are in
`Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`.) -/
theorem bumpAtOne_majorant :
    ∃ ψ : ℝ → ℝ, IsBumpAtOne ψ 16 ∧ ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ x = 1 := by
  set f : ℝ → ℝ :=
    fun x => Real.smoothTransition (16 * x - 1) * Real.smoothTransition (16 * (8 - x))
  have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    rw [show f = fun x => Real.smoothTransition (16 * x - 1) *
        Real.smoothTransition (16 * (8 - x)) from rfl]
    fun_prop
  have hnonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hsupp : ∀ x, f x ≠ 0 → x ∈ Set.Icc (1 / 16 : ℝ) 16 := by
    intro x hx
    change Real.smoothTransition (16 * x - 1) * Real.smoothTransition (16 * (8 - x)) ≠ 0 at hx
    have h1 : Real.smoothTransition (16 * x - 1) ≠ 0 := fun h => hx (by rw [h, zero_mul])
    have h2 : Real.smoothTransition (16 * (8 - x)) ≠ 0 := fun h => hx (by rw [h, mul_zero])
    simp only [ne_eq, Real.smoothTransition.zero_iff_nonpos, not_le] at h1 h2
    rw [Set.mem_Icc]
    constructor <;> linarith
  have hcs : HasCompactSupport f :=
    HasCompactSupport.intro (K := Set.Icc (1 / 16 : ℝ) 16) isCompact_Icc fun x hx =>
      by_contra fun hne => hx (hsupp x hne)
  have hderiv : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |iteratedDeriv j f x| ≤ c :=
    Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth hcont hcs
  have hone : f 1 = 1 := by
    rw [show f 1 = Real.smoothTransition (16 * 1 - 1) * Real.smoothTransition (16 * (8 - 1))
      from rfl]
    rw [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 16 * 1 - 1),
      Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 16 * (8 - 1))]
    norm_num
  have hplateau : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), f x = 1 := by
    intro x hx
    rw [show f x = Real.smoothTransition (16 * x - 1) * Real.smoothTransition (16 * (8 - x))
      from rfl]
    rw [Set.mem_Icc] at hx
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 16 * x - 1),
      Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 16 * (8 - x))]
    ring
  exact ⟨f, ⟨hcont, hnonneg, hsupp, hone, hderiv⟩, hplateau⟩

end Work.GM.S3
