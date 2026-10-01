/-
# The level factor `1 - a·p^{-s}`: zeros and partial fractions

For a prime `p` and a complex number `a` with `‖a‖ = 1`, the function

  `f(s) = 1 - a·p^{-s} = 1 - a·exp(-L·s)`,   `L = log p`,

is entire and its zeros are exactly the points of the lattice `u₀ + ℤ·P` with
`u₀ = log a / L` and `P = 2πi/L`.  This file collects the concrete constants and the
elementary identities about them that the partial-fraction computation of
`logDeriv f` needs.
-/
import Mathlib

noncomputable section

open scoped BigOperators

namespace Work.LinnikAreas.TuranOther

/-- The logarithm `L = log p` of the level `p`. -/
def lvlL (p : ℕ) : ℝ := Real.log p

/-- The level factor `1 - a·exp(-L·s)` in exponential form. -/
def lvlE (p : ℕ) (a : ℂ) : ℂ → ℂ := fun s => 1 - a * Complex.exp (-((lvlL p : ℂ) * s))

/-- A zero of `s ↦ 1 - a·exp(-L·s)`: the point `u₀ = log a / L`. -/
def lvlRoot (p : ℕ) (a : ℂ) : ℂ := Complex.log a / (lvlL p : ℂ)

/-- The lattice spacing `P = 2πi/L` of the zero set. -/
def lvlPeriod (p : ℕ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I / (lvlL p : ℂ)

/-- The scaling constant `c = iL/(2π)`, chosen so that `2πi·c = -L`. -/
def lvlC (p : ℕ) : ℂ := Complex.I * (lvlL p : ℂ) / (2 * (Real.pi : ℂ))

/-- The `n`-th lattice point `u_n = u₀ + n·P`. -/
def lvlZero (p : ℕ) (a : ℂ) (n : ℤ) : ℂ := lvlRoot p a + (n : ℂ) * lvlPeriod p

variable {p : ℕ}

lemma lvlL_pos (hp : p.Prime) : 0 < lvlL p :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

lemma lvlL_ne_zero (hp : p.Prime) : lvlL p ≠ 0 := (lvlL_pos hp).ne'

lemma lvlL_pos_of_two_le {p : ℕ} (hp : 2 ≤ p) : 0 < lvlL p :=
  Real.log_pos (by exact_mod_cast hp)

/-- `p^{-s} = exp(-L·s)` for a prime `p`. -/
lemma cpow_eq_exp_lvlL (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ (-s) = Complex.exp (-((lvlL p : ℂ) * s)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero)]
  have hlog : Complex.log ((p : ℝ) : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_log (by positivity)]
  have hpc : ((p : ℂ)) = ((p : ℝ) : ℂ) := by norm_num
  rw [hpc, hlog, lvlL]
  ring

/-- The level factor in exponential form is the statement's `1 - a·p^{-s}`. -/
lemma lvlE_eq (hp : p.Prime) (a : ℂ) :
    lvlE p a = fun s : ℂ => 1 - a * (p : ℂ) ^ (-s) := by
  funext s
  rw [lvlE, cpow_eq_exp_lvlL hp]

lemma lvlE_apply (p : ℕ) (a : ℂ) (s : ℂ) :
    lvlE p a s = 1 - a * Complex.exp (-((lvlL p : ℂ) * s)) := rfl

lemma differentiable_lvlE (p : ℕ) (a : ℂ) : Differentiable ℂ (lvlE p a) := by
  unfold lvlE
  fun_prop

lemma analyticAt_lvlE (p : ℕ) (a : ℂ) (s : ℂ) : AnalyticAt ℂ (lvlE p a) s :=
  (differentiable_lvlE p a).analyticAt s

/-- `L·u₀ = log a`. -/
lemma lvlL_mul_lvlRoot (hL : lvlL p ≠ 0) (a : ℂ) :
    (lvlL p : ℂ) * lvlRoot p a = Complex.log a := by
  rw [lvlRoot, mul_div_cancel₀]
  exact_mod_cast hL

/-- `exp(L·u₀) = a` when `a ≠ 0`. -/
lemma exp_lvlL_mul_lvlRoot (hL : lvlL p ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    Complex.exp ((lvlL p : ℂ) * lvlRoot p a) = a := by
  rw [lvlL_mul_lvlRoot hL a, Complex.exp_log ha]

/-- `Re u₀ = 0` when `‖a‖ = 1`. -/
lemma lvlRoot_re {a : ℂ} (ha : ‖a‖ = 1) : (lvlRoot p a).re = 0 := by
  rw [lvlRoot, Complex.div_re]
  simp [Complex.log_re, ha, Complex.ofReal_re, Complex.ofReal_im]

/-- `L·P = 2πi`. -/
lemma lvlL_mul_lvlPeriod (hL : lvlL p ≠ 0) :
    (lvlL p : ℂ) * lvlPeriod p = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [lvlPeriod, mul_div_cancel₀]
  exact_mod_cast hL

lemma lvlPeriod_ne_zero (hL : lvlL p ≠ 0) : lvlPeriod p ≠ 0 := by
  intro h
  have h2 := lvlL_mul_lvlPeriod (p := p) hL
  rw [h, mul_zero] at h2
  have hpi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero]
  exact hpi h2.symm

/-- `2πi·c = -L`. -/
lemma two_pi_I_mul_lvlC (p : ℕ) :
    (2 * (Real.pi : ℂ) * Complex.I) * lvlC p = -((lvlL p : ℂ)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [lvlC]
  field_simp
  ring_nf
  simp [Complex.I_mul_I]

lemma lvlC_ne_zero (hL : lvlL p ≠ 0) : lvlC p ≠ 0 := by
  intro h
  have h2 := two_pi_I_mul_lvlC p
  rw [h, mul_zero] at h2
  have hLc : (lvlL p : ℂ) = 0 := by
    have : -((lvlL p : ℂ)) = 0 := h2.symm
    simpa using this
  exact hL (by exact_mod_cast hLc)

/-- `exp(L·u_n) = a`: every lattice point is a zero. -/
lemma exp_lvlL_mul_lvlZero (hL : lvlL p ≠ 0) {a : ℂ} (ha : a ≠ 0) (n : ℤ) :
    Complex.exp ((lvlL p : ℂ) * lvlZero p a n) = a := by
  have h2 : (lvlL p : ℂ) * lvlZero p a n
      = (lvlL p : ℂ) * lvlRoot p a + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [lvlZero]
    linear_combination (n : ℂ) * (lvlL_mul_lvlPeriod (p := p) hL)
  rw [h2, Complex.exp_add, lvlL_mul_lvlRoot hL a, Complex.exp_log ha, Complex.exp_int_mul]
  have : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by ring⟩
  rw [this, one_zpow, mul_one]

/-- Every lattice point is a zero of the level factor. -/
lemma lvlE_lvlZero (hL : lvlL p ≠ 0) {a : ℂ} (ha : a ≠ 0) (n : ℤ) :
    lvlE p a (lvlZero p a n) = 0 := by
  rw [lvlE_apply, Complex.exp_neg, exp_lvlL_mul_lvlZero hL ha n, mul_inv_cancel₀ ha]
  ring

/-- The lattice points are distinct. -/
lemma lvlZero_injective (hL : lvlL p ≠ 0) (a : ℂ) :
    Function.Injective (lvlZero p a) := by
  intro m n h
  have h' : (m : ℂ) * lvlPeriod p = (n : ℂ) * lvlPeriod p := by
    simpa [lvlZero] using add_left_cancel h
  have h'' : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ (lvlPeriod_ne_zero (p := p) hL) h'
  exact_mod_cast h''

end Work.LinnikAreas.TuranOther

namespace Work.LinnikAreas.TuranOther

variable {p : ℕ}

lemma lvlC_mul_lvlPeriod (hL : lvlL p ≠ 0) : lvlC p * lvlPeriod p = -1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hLc : (lvlL p : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [lvlC, lvlPeriod]
  field_simp
  ring_nf
  simp

lemma lvlC_ne_zero' (hL : lvlL p ≠ 0) : lvlC p ≠ 0 := by
  intro h
  have := lvlC_mul_lvlPeriod (p := p) hL
  rw [h, zero_mul] at this
  norm_num at this

/-- `P = -c⁻¹`. -/
lemma lvlPeriod_eq_neg_inv_lvlC (hL : lvlL p ≠ 0) : lvlPeriod p = -(lvlC p)⁻¹ := by
  rw [show -(lvlC p)⁻¹ = -1 / lvlC p by simp [div_eq_mul_inv]]
  rw [eq_div_iff (lvlC_ne_zero' hL), mul_comm]
  exact lvlC_mul_lvlPeriod hL

/-- `2πi·(c·s) = -L·s`. -/
lemma two_pi_I_mul_lvlC_mul (p : ℕ) (s : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I) * (lvlC p * s) = -((lvlL p : ℂ) * s) := by
  rw [← mul_assoc, two_pi_I_mul_lvlC]
  ring

lemma lvlC_mul_re (p : ℕ) (X : ℂ) :
    (lvlC p * X).re = -(lvlL p / (2 * Real.pi)) * X.im := by
  rw [lvlC]
  have h : Complex.I * (lvlL p : ℂ) / (2 * (Real.pi : ℂ)) * X
      = ((lvlL p / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * X) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

lemma lvlC_mul_im (p : ℕ) (X : ℂ) :
    (lvlC p * X).im = lvlL p / (2 * Real.pi) * X.re := by
  rw [lvlC]
  have h : Complex.I * (lvlL p : ℂ) / (2 * (Real.pi : ℂ)) * X
      = ((lvlL p / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * X) := by
    push_cast; ring
  rw [h, Complex.im_ofReal_mul, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- `c·(t - u₀)` lies in the upper half plane when `‖a‖ = 1` and `1 < t.re`. -/
lemma lvlC_mul_im_pos (hp : p.Prime) {a : ℂ} (ha : ‖a‖ = 1) {t : ℂ} (ht : 1 < t.re) :
    0 < (lvlC p * (t - lvlRoot p a)).im := by
  rw [lvlC_mul_im, Complex.sub_re, lvlRoot_re ha, sub_zero]
  have hL := lvlL_pos hp
  have hpi := Real.pi_pos
  positivity

/-- The affine change of variable: `t - u_n = c⁻¹·(c·(t-u₀) + n)`. -/
lemma sub_lvlZero_eq (hL : lvlL p ≠ 0) (a : ℂ) (n : ℤ) (t : ℂ) :
    t - lvlZero p a n = (lvlC p)⁻¹ * (lvlC p * (t - lvlRoot p a) + (n : ℂ)) := by
  rw [lvlZero, lvlPeriod_eq_neg_inv_lvlC hL]
  have hc := lvlC_ne_zero' hL
  field_simp
  ring

end Work.LinnikAreas.TuranOther
