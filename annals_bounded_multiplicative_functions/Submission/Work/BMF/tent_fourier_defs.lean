import Mathlib
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Helper definitions for the Fourier series of the tent

We collect the `1`-periodic Bernoulli polynomial of degree two
`phiR t = {t}^2 - {t} + 1/6` (with `{t} = Int.fract t`), its complex version, and a few
elementary identities for the additive character `eZ`.
-/

namespace Work.BMF

/-- The `1`-periodic Bernoulli polynomial of degree two, `t ↦ {t}² - {t} + 1/6`. -/
noncomputable def phiR (t : ℝ) : ℝ := (Int.fract t) ^ 2 - Int.fract t + 1 / 6

/-- The complex-valued version of `phiR`. -/
noncomputable def phiC (t : ℝ) : ℂ := (phiR t : ℂ)

lemma phiC_apply (t : ℝ) : phiC t = (((Int.fract t) ^ 2 - Int.fract t + 1 / 6 : ℝ) : ℂ) := rfl

lemma phiR_fract (t : ℝ) : phiR (Int.fract t) = phiR t := by
  unfold phiR
  rw [Int.fract_fract]

/-- `eZ` is a homomorphism from `(ℝ, +)` to `(ℂ, *)`. -/
lemma eZ_add (a b : ℝ) : eZ (a + b) = eZ a * eZ b := by
  unfold eZ
  rw [show (2:ℂ) * ↑Real.pi * Complex.I * ↑(a + b)
        = 2 * ↑Real.pi * Complex.I * ↑a + 2 * ↑Real.pi * Complex.I * ↑b by push_cast; ring,
      Complex.exp_add]

@[simp] lemma eZ_zero : eZ 0 = 1 := by simp [eZ]

lemma eZ_natCast_mul (n : ℕ) (t : ℝ) : eZ ((n : ℝ) * t) = eZ t ^ n := by
  unfold eZ
  rw [show (2:ℂ) * ↑Real.pi * Complex.I * ↑((n:ℝ) * t)
        = (n:ℂ) * (2 * ↑Real.pi * Complex.I * ↑t) by push_cast; ring,
      Complex.exp_nat_mul]

lemma eZ_intCast_mul (n : ℤ) (t : ℝ) : eZ ((n : ℝ) * t) = eZ t ^ n := by
  unfold eZ
  rw [show (2:ℂ) * ↑Real.pi * Complex.I * ↑((n:ℝ) * t)
        = (n:ℂ) * (2 * ↑Real.pi * Complex.I * ↑t) by push_cast; ring,
      Complex.exp_int_mul]

/-- `fourier n` evaluated at a point of the unit circle is the additive character `eZ`. -/
lemma fourier_coe_eq_eZ (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (1:ℝ)) = eZ ((n : ℝ) * x) := by
  rw [fourier_coe_apply]
  unfold eZ
  congr 1
  push_cast
  ring

/-- On the unit circle, a real number and its fractional part coincide. -/
lemma coe_fract_eq (x : ℝ) :
    ((x : ℝ) : AddCircle (1:ℝ)) = ((Int.fract x : ℝ) : AddCircle (1:ℝ)) := by
  have h : x = Int.fract x + (⌊x⌋ : ℝ) := by
    have := Int.fract_add_floor x; linarith
  conv_lhs => rw [h]
  rw [AddCircle.coe_add]
  have hz : ((⌊x⌋ : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [show (⌊x⌋ : ℝ) = (⌊x⌋ : ℤ) • (1 : ℝ) by simp]
    rw [AddCircle.coe_zsmul]
    rw [show ((1 : ℝ) : AddCircle (1:ℝ)) = 0 from AddCircle.coe_period 1]
    simp
  rw [hz, add_zero]

end Work.BMF
