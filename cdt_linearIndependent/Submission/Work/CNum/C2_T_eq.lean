import Mathlib
import Submission.Work.CNum.C2_setup

namespace Work.CNum

open Complex

/-- The radicand identity: `2·A·(γ - cos θ) = (2(1+c²))²·(sin²(θ/2) - σ²)`.
Equivalently, `√(2A(γ - cos θ)) = 2(1+c²)·√(sin²(θ/2) - σ²)`, where the left
side is the modulus of `√(Ra(e^{iθ}))` and the right side is `2(1+c²)·w(θ)`. -/
lemma C2_radicand (θ : ℝ) :
    2 * AR * (gamR - Real.cos θ) =
      (2 * (1 + cR ^ 2)) ^ 2 * (Real.sin (θ / 2) ^ 2 - C2σ ^ 2) := by
  have hσ : C2σ ^ 2 = 1 - 4 * cR ^ 2 / AR := by
    have h1 : C2C ^ 2 = 4 * cR ^ 2 / AR := by rw [C2C, AR, cR]; norm_num
    have h2 := one_sub_C2σ_sq
    linarith
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (θ/2)
    rw [show 2 * (θ/2) = θ by ring] at h1
    have h2 := Real.sin_sq_add_cos_sq (θ/2)
    linarith
  rw [hcos, hσ, gamR, AR]
  field_simp
  ring

theorem C2_T_eq {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    C2T θ = 2 * (1 + cR ^ 2) * C2w θ := by
  rw [C2T, C2w, C2_radicand θ, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end Work.CNum
