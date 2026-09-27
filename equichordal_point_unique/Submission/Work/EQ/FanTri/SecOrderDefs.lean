import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanSep.sqrt_step

/-!
# Second-order expansion of `invBranch a true` at `A₁ = (-1/2, 0)`: definitions

`G = invBranch a true` is the principal backward branch of the equichordal relation.  Near
`A₁` it is a holomorphic map fixing `A₁`, with differential `L(δ₁,δ₂) = (-δ₁, δ₂/λ)`,
`λ = eqLam a = (1-a)/(1+a)`.  This file fixes the notation used to prove the quantitative
second-order remainder estimate `‖G x - G y - L(x-y)‖ ≤ N(‖x-A₁‖+‖y-A₁‖)‖x-y‖`.

Write `s = sHat a = (1-a)/2` (the distance `|A₁ - O₂|`, `O₂ = (a/2,0)`) and, for a shift
`z = (z₁,z₂) = Q - A₁`, `D = sD a z = s - z₁` (so `Q.1 + a/2 = -D`) and
`R = sR a z = (D² + z₂²)^{1/2}` (the principal square root).  Then
`G(A₁+z).1 = 1/2 - z₁ - D/R`, `G(A₁+z).2 = z₂(1/R - 1)`, hence the second-order remainder
`PhiT a z = G(A₁+z) - A₁ - L z` has coordinates
`(PhiT a z).1 = 1 - D/R = z₂²/(R(R+D))`,  `(PhiT a z).2 = z₂(1/R - 1/s)`.
-/

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- `s = (1-a)/2`: the distance from `A₁ = (-1/2,0)` to `O₂ = (a/2,0)`. -/
def sHat (a : ℝ) : ℝ := (1 - a) / 2

/-- The abscissa gap `D = s - z₁` of the shift `z` from `A₁`. -/
def sD (a : ℝ) (z : ℂ × ℂ) : ℂ := (sHat a : ℂ) - z.1

/-- The principal square root `R = (D² + z₂²)^{1/2}`. -/
noncomputable def sR (a : ℝ) (z : ℂ × ℂ) : ℂ := (sD a z ^ 2 + z.2 ^ 2) ^ (1 / 2 : ℂ)

/-- The point `A₁ + z`. -/
def shiftA1 (z : ℂ × ℂ) : ℂ × ℂ := (((-1 / 2 : ℝ) : ℂ) + z.1, z.2)

/-- The second-order remainder `Φ(z) = G(A₁+z) - A₁ - L z` at `A₁`. -/
noncomputable def PhiT (a : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  invBranch a true (shiftA1 z) - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) -
    (-(z.1), z.2 / (eqLam a : ℂ))

/-- The factor `(R(R+D))⁻¹` occurring in the first coordinate of `PhiT`. -/
noncomputable def facA (a : ℝ) (z : ℂ × ℂ) : ℂ := (sR a z * (sR a z + sD a z))⁻¹

/-- The factor `R⁻¹` occurring in the second coordinate of `PhiT`. -/
noncomputable def facB (a : ℝ) (z : ℂ × ℂ) : ℂ := (sR a z)⁻¹

section Basic

variable {a : ℝ}

lemma sHat_pos {a : ℝ} (ha1 : a < 1) : 0 < sHat a := by
  rw [sHat]; linarith

lemma sHat_ne_zero {a : ℝ} (ha1 : a < 1) : sHat a ≠ 0 := (sHat_pos ha1).ne'

lemma sHat_nonneg {a : ℝ} (ha1 : a < 1) : 0 ≤ sHat a := (sHat_pos ha1).le

lemma sHat_le_half {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : sHat a ≤ 1 / 2 := by
  rw [sHat]; linarith

lemma sHat_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : sHat a < 1 := by
  have := sHat_le_half ha0 ha1; linarith

lemma two_mul_sHat {a : ℝ} : 2 * sHat a = 1 - a := by rw [sHat]; ring

/-- `1 + 1/λ = 1/s` for the equichordal eigenvalue `λ = eqLam a = (1-a)/(1+a)`. -/
lemma inv_eqLam_add_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (eqLam a)⁻¹ + 1 = (sHat a)⁻¹ := by
  have h1 : (1 + a) ≠ 0 := by linarith
  have h2 : (1 - a) ≠ 0 := by linarith
  rw [eqLam, sHat]
  field_simp
  ring

end Basic

/-! ## The elementary setup at scale `s/16` -/

/-- **Setup.** For `‖z‖ ≤ s/16` the abscissa gap `D = sD a z` lies in the cone
`{re > 0, |im| ≤ re/2}`, the ordinate is at most `‖D‖/2`, the principal square root
`R = sR a z` factors as `D · sqHalf((z₂/D)²)` (`FanSep.sqrt_step`), and `R² = D² + z₂²`. -/
theorem sD_sR_setup {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) :
    sD a z ≠ 0 ∧ 0 < (sD a z).re ∧ |(sD a z).im| ≤ (sD a z).re / 2 ∧
      ‖z.2‖ ≤ ‖sD a z‖ / 2 ∧
      sR a z = sD a z * sqHalf ((z.2 / sD a z) ^ 2) ∧ sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2 := by
  have hs0 : 0 < sHat a := sHat_pos ha1
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  have hz2 : ‖z.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le z) hz
  have hz2' : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hDre : (sD a z).re = sHat a - z.1.re := by
    simp only [sD, Complex.sub_re, Complex.ofReal_re]
  have hDim : (sD a z).im = -z.1.im := by
    simp only [sD, Complex.sub_im, Complex.ofReal_im, zero_sub]
  have hre1 : |z.1.re| ≤ sHat a / 16 := le_trans (Complex.abs_re_le_norm z.1) hz1
  have him1 : |z.1.im| ≤ sHat a / 16 := le_trans (Complex.abs_im_le_norm z.1) hz1
  have hDrepos : 0 < (sD a z).re := by
    rw [hDre]; linarith [(abs_le.mp hre1).2, hs0]
  have hDne : sD a z ≠ 0 := by
    intro h
    rw [h] at hDrepos
    simp at hDrepos
  have hDimle : |(sD a z).im| ≤ (sD a z).re / 2 := by
    have h2 : -(sHat a / 16) ≤ z.1.im := (abs_le.mp him1).1
    have h3 : z.1.im ≤ sHat a / 16 := (abs_le.mp him1).2
    have h4 : z.1.re ≤ sHat a / 16 := (abs_le.mp hre1).2
    rw [hDim, hDre, abs_le]
    constructor <;> linarith
  have hDnorm : sHat a - sHat a / 16 ≤ ‖sD a z‖ := by
    have h1 : sD a z - (sHat a : ℂ) = -z.1 := by rw [sD]; ring
    have h2 : ‖(sHat a : ℂ)‖ = sHat a := by
      simp [abs_of_pos hs0]
    have h3 := abs_norm_sub_norm_le (sD a z) ((sHat a : ℂ))
    rw [h2, h1, norm_neg] at h3
    linarith [(abs_le.mp h3).1]
  have hz2D : ‖z.2‖ ≤ ‖sD a z‖ / 2 := by
    linarith [hz2, hDnorm, hs0]
  obtain ⟨-, hsqrt, -⟩ := FanSep.sqrt_step
  have hmain : sR a z = sD a z * sqHalf ((z.2 / sD a z) ^ 2) := by
    rw [sR]
    exact hsqrt hDne hDrepos hDimle hz2D
  refine ⟨hDne, hDrepos, hDimle, hz2D, hmain, ?_⟩
  rw [hmain, mul_pow, sqHalf_sq]
  field_simp


end

end Work.EQ.FanTri
