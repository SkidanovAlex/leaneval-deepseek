/-
# The cusp asymptotics of `E₄`, `E₆` and `E₂|₂S` on the imaginary axis

The CKMRV kernels `K^{(d)}`, `K̂^{(d)}` (`d = 8, 24`) are built out of the classical modular
forms evaluated at `it` (CKMRV Section 4.4, `Work.Kernels.Kernels`).  Near the cusp `t → 0`
each weight-`k` form blows up like `t^{-k}`; this file records the *one-sided* (upper) bounds

  `‖E₄(it)‖ ≤ C t^{-4}`,  `‖E₆(it)‖ ≤ C t^{-6}`,  `‖E₂|₂S(it)‖ ≤ C t^{-2}`   (`0 < t ≤ 1`)

in the form needed by the cusp analysis of the contour integral.

`Work.Asymptotics.Eisenstein_atZero` already supplies *two-sided* bounds of the same shape, but
only for `t ≤ T` with an unspecified (and possibly very small) threshold `T`; here we need the
bound on the whole range `0 < t ≤ 1`.  Two independent devices give this:

* for `E₄` and `E₆` Mathlib's `ModularFormClass.exists_bound`, applied to the modular forms
  `E₄` and `E₆` of level one, reads `‖E_k τ‖ ≤ C * max 1 ((im τ)^{-k})`; on the imaginary axis
  with `t ≤ 1` the maximum is `t^{-k}`, giving the bound directly;

* for `E₂|₂S` we use the definition `E₂|₂S = (E₂ ∣₂ S)(z) = E₂(-1/z) z^{-2}`, so that at
  `z = it` the argument becomes `-1/(it) = i/t`, whose imaginary part `1/t` is `≥ 1`; there
  `E₂` is bounded by the explicit growth estimate `E2Fun_growth_explicit` (five times the
  partial sums of the divisor series, i.e. `193 * (1 + (im τ)^{-3})`).
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Eisenstein_atZero

noncomputable section

open UpperHalfPlane ModularForm ModularGroup
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-- For `0 < t ≤ 1` the maximum `max 1 (1 / t ^ (n : ℤ))` is the reciprocal power `(t ^ n)⁻¹`;
this is the step which converts Mathlib's bound `‖f τ‖ ≤ C * max 1 (1 / τ.im ^ k)` for a level
one modular form into the cusp bound at `t → 0`. -/
private lemma max_one_one_div_zpow {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    max 1 (1 / t ^ (n : ℤ)) = (t ^ n)⁻¹ := by
  rw [zpow_natCast, one_div, max_eq_right]
  exact (one_le_inv₀ (pow_pos ht n)).mpr (pow_le_one₀ ht.le ht1)

/-- **Explicit global growth bound for `E₂`.**  The weight-two Eisenstein series satisfies
`‖E₂ τ‖ ≤ 193 * (1 + (im τ)^{-3})` on all of `ℍ`; this is the growth estimate underlying
`Work.Kernels.ClassicalFacts.E2Fun_mem_InP`, recorded here with its explicit constants so that
it can be evaluated at the point `i/t` below (where `im = 1/t ≥ 1` and the bound is `≤ 386`). -/
private lemma E2Fun_growth_explicit (τ : UpperHalfPlane) :
    ‖E2Fun τ‖ ≤ 193 * (1 + (τ.im)⁻¹ ^ 3) := by
  have h1 := Work.Kernels.ClassicalFacts.e2_norm_le_tsum τ
  have hr0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * Real.pi * τ.im)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, τ.im_pos]
  have h2 := Work.Kernels.ClassicalFacts.e2_tsum_sigma_le
    (Real.exp (-(2 * Real.pi * τ.im))) hr0 hr1
  have h3 := Work.Kernels.ClassicalFacts.e2_one_sub_exp_neg_cube_le' τ.im τ.im_pos
  have hkey : ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
        Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ) ≤ 8 + (τ.im⁻¹) ^ 3 := by
    calc ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
            Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ)
        ≤ Real.exp (-(2 * Real.pi * τ.im)) /
            (1 - Real.exp (-(2 * Real.pi * τ.im))) ^ 3 := h2
      _ = Real.exp (-(2 * Real.pi * τ.im)) *
            ((1 - Real.exp (-(2 * Real.pi * τ.im)))⁻¹) ^ 3 := by
          rw [div_eq_mul_inv, inv_pow]
      _ ≤ 1 * ((1 - Real.exp (-(2 * Real.pi * τ.im)))⁻¹) ^ 3 := by
          refine mul_le_mul_of_nonneg_right hr1.le ?_
          positivity
      _ = ((1 - Real.exp (-(2 * Real.pi * τ.im)))⁻¹) ^ 3 := one_mul _
      _ ≤ 8 + (τ.im⁻¹) ^ 3 := h3
  have hbound : ‖E2Fun τ‖ ≤ 193 * (1 + (τ.im⁻¹) ^ 3) := by
    have hx : (0 : ℝ) ≤ (τ.im⁻¹) ^ 3 := by positivity
    linarith
  exact hbound

/-- **The cusp asymptotics of `E₄` at `t → 0`, on the whole range `0 < t ≤ 1`.** -/
private lemma E4Fun_imagAxis_atZero_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖E4Fun (imagAxis t ht)‖ ≤ C * (t ^ 4)⁻¹ := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_bound (k := 4) (by norm_num) (ModularForm.E₄)
  refine ⟨max C 0 + 1, by positivity, fun t ht ht1 => ?_⟩
  have h1 := hC (imagAxis t ht)
  have him : (imagAxis t ht).im = t := by simp [imagAxis]
  have hmax : max 1 (1 / t ^ (4 : ℤ)) = (t ^ 4)⁻¹ := max_one_one_div_zpow ht ht1 4
  rw [him, hmax] at h1
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht 4
  calc ‖E4Fun (imagAxis t ht)‖ ≤ C * (t ^ 4)⁻¹ := h1
    _ ≤ (max C 0 + 1) * (t ^ 4)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr ht4.le)
        linarith [le_max_left C 0]

/-- **The cusp asymptotics of `E₆` at `t → 0`, on the whole range `0 < t ≤ 1`.** -/
private lemma E6Fun_imagAxis_atZero_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖E6Fun (imagAxis t ht)‖ ≤ C * (t ^ 6)⁻¹ := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_bound (k := 6) (by norm_num) (ModularForm.E₆)
  refine ⟨max C 0 + 1, by positivity, fun t ht ht1 => ?_⟩
  have h1 := hC (imagAxis t ht)
  have him : (imagAxis t ht).im = t := by simp [imagAxis]
  have hmax : max 1 (1 / t ^ (6 : ℤ)) = (t ^ 6)⁻¹ := max_one_one_div_zpow ht ht1 6
  rw [him, hmax] at h1
  have ht6 : (0 : ℝ) < t ^ 6 := pow_pos ht 6
  calc ‖E6Fun (imagAxis t ht)‖ ≤ C * (t ^ 6)⁻¹ := h1
    _ ≤ (max C 0 + 1) * (t ^ 6)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr ht6.le)
        linarith [le_max_left C 0]

/-- **The cusp asymptotics of `E₂|₂S` at `t → 0`, on the whole range `0 < t ≤ 1`.**

Since `(f ∣₂ S)(z) = f(S • z) z^{-2}` and `S • it = i/t`, we have
`‖(E₂|₂S)(it)‖ = t^{-2} ‖E₂(i/t)‖`, and `E₂` is bounded by `386` for `im ≥ 1`. -/
private lemma E2S_imagAxis_atZero_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖E2S (imagAxis t ht)‖ ≤ C * (t ^ 2)⁻¹ := by
  refine ⟨386, by norm_num, fun t ht ht1 => ?_⟩
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  -- the slash law `(E₂ ∣₂ S)(z) = E₂(S • z) z^{-2}` and `S • it = i/t`
  have hsplit : E2S (imagAxis t ht)
      = E2Fun (imagAxis t⁻¹ hs) * ((imagAxis t ht : UpperHalfPlane) : ℂ) ^ (-2 : ℤ) := by
    rw [E2S, slash_S_apply, imagAxis_smul_S t ht]
  rw [hsplit, norm_mul]
  -- the modulus of the factor `z^{-2}` at `z = it`
  have hz : ‖((imagAxis t ht : UpperHalfPlane) : ℂ) ^ (-2 : ℤ)‖ = (t ^ 2)⁻¹ := by
    rw [norm_zpow]
    have h : ‖((imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
      simp [imagAxis, abs_of_pos ht]
    rw [h, show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
  rw [hz]
  -- `E₂(i/t)` is bounded: the imaginary part `1/t` of the argument is `≥ 1`
  have hb := E2Fun_growth_explicit (imagAxis t⁻¹ hs)
  have him : (imagAxis t⁻¹ hs).im = t⁻¹ := by simp [imagAxis]
  rw [him, inv_inv] at hb
  have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.le ht1
  have h386 : ‖E2Fun (imagAxis t⁻¹ hs)‖ ≤ 386 := by linarith
  exact mul_le_mul_of_nonneg_right h386 (inv_nonneg.mpr (pow_pos ht 2).le)

/-- **The cusp asymptotics of the Eisenstein series on the imaginary axis at `t → 0`.**

The values `E₄(it)`, `E₆(it)` and `(E₂|₂S)(it)` grow at most like `t^{-4}`, `t^{-6}` and
`t^{-2}` respectively, uniformly for `0 < t ≤ 1`.  (Only the upper bounds are needed here; the
matching lower bounds are the two-sided estimates of `Work.Asymptotics.Eisenstein_atZero`.) -/
theorem norm_Eisenstein_imagAxis_atZero :
    (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ≤ C * (t ^ 4)⁻¹) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ‖Work.Kernels.E6Fun (Work.Kernels.imagAxis t ht)‖ ≤ C * (t ^ 6)⁻¹) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ‖Work.Kernels.E2S (Work.Kernels.imagAxis t ht)‖ ≤ C * (t ^ 2)⁻¹) :=
  ⟨E4Fun_imagAxis_atZero_one, E6Fun_imagAxis_atZero_one, E2S_imagAxis_atZero_one⟩

end Work.Asymptotics
