import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
open UpperHalfPlane ModularGroup
set_option linter.unusedSimpArgs false
namespace Work.Asymptotics.HalfFunnel

lemma ctanRegion_data (τ : ℍ) (hτ : τ ∈ ctanRegion) :
    ((3 / 8 : ℝ) < τ.re ∧ τ.re < 5 / 8 ∧ (1 : ℝ) / 2 ≤ τ.im ∧ τ.im < 5 / 8 ∧
      (τ.re - 1 / 2) ^ 2 + (τ.im - 1 / 2) ^ 2 < 1 / 64) ∨
    ((-(5 / 8) : ℝ) < τ.re ∧ τ.re < -(3 / 8) ∧ (1 : ℝ) / 2 ≤ τ.im ∧ τ.im < 5 / 8 ∧
      (τ.re + 1 / 2) ^ 2 + (τ.im - 1 / 2) ^ 2 < 1 / 64) := by
  obtain ⟨hD, h1, h2, hb⟩ := hτ
  have hcoe : ((τ : ℂ) - ctanP).re = τ.re - 1/2 ∧ ((τ : ℂ) - ctanP).im = τ.im - 1/2 := by
    constructor <;> simp [ctanP, Complex.sub_re, Complex.sub_im]
  have hcoe2 : ((τ : ℂ) - ctanM).re = τ.re + 1/2 ∧ ((τ : ℂ) - ctanM).im = τ.im - 1/2 := by
    constructor <;> simp [ctanM, Complex.sub_re, Complex.sub_im]
  rcases hb with hb | hb
  · left
    have hsq : ((τ : ℂ) - ctanP).normSq < 1/64 := by
      have h := Complex.normSq_eq_norm_sq ((τ : ℂ) - ctanP)
      nlinarith [norm_nonneg ((τ : ℂ) - ctanP)]
    rw [Complex.normSq_apply, hcoe.1, hcoe.2] at hsq
    have hre := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
    rw [hcoe.1] at hre
    have hre' := abs_lt.mp (lt_of_le_of_lt hre hb)
    have him := Complex.abs_im_le_norm ((τ : ℂ) - ctanP)
    rw [hcoe.2] at him
    have him' := abs_lt.mp (lt_of_le_of_lt him hb)
    exact ⟨by linarith [hre'.1], by linarith [hre'.2], h1, by linarith [him'.2], by simpa [sq] using hsq⟩
  · right
    have hsq : ((τ : ℂ) - ctanM).normSq < 1/64 := by
      have h := Complex.normSq_eq_norm_sq ((τ : ℂ) - ctanM)
      nlinarith [norm_nonneg ((τ : ℂ) - ctanM)]
    rw [Complex.normSq_apply, hcoe2.1, hcoe2.2] at hsq
    have hre := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
    rw [hcoe2.1] at hre
    have hre' := abs_lt.mp (lt_of_le_of_lt hre hb)
    have him := Complex.abs_im_le_norm ((τ : ℂ) - ctanM)
    rw [hcoe2.2] at him
    have him' := abs_lt.mp (lt_of_le_of_lt him hb)
    exact ⟨by linarith [hre'.1], by linarith [hre'.2], h1, by linarith [him'.2], by simpa [sq] using hsq⟩


/-- The elementary inequality behind the pole estimates: for `α² + β² < 1/64`,
`3α² + 3β² - α + 3β < 1/2`. -/
lemma pole_helper {α β : ℝ} (h : α ^ 2 + β ^ 2 < 1 / 64) :
    3 * α ^ 2 + 3 * β ^ 2 - α + 3 * β < 1 / 2 := by
  have h3 : (-α + 3 * β) ^ 2 ≤ 10 * (α ^ 2 + β ^ 2) := by nlinarith [sq_nonneg (3 * α + β)]
  have h4 : 10 * (α ^ 2 + β ^ 2) < 10 / 64 := by linarith
  have h5 : -α + 3 * β < 2 / 5 := by
    by_contra hc
    push_neg at hc
    nlinarith [h3, h4]
  linarith

/-- For `α² + β² < 1/64`, `α² + β² + α - β < 1/2`. -/
lemma pole_helper2 {α β : ℝ} (h : α ^ 2 + β ^ 2 < 1 / 64) :
    α ^ 2 + β ^ 2 + α - β < 1 / 2 := by
  have h3 : (α - β) ^ 2 ≤ 2 * (α ^ 2 + β ^ 2) := by nlinarith [sq_nonneg (α + β)]
  have h4 : 2 * (α ^ 2 + β ^ 2) < 2 / 64 := by linarith
  have h5 : α - β < 1 / 4 := by
    by_contra hc
    push_neg at hc
    nlinarith [h3, h4]
  linarith

end Work.Asymptotics.HalfFunnel
