/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.Basic
import Submission.Work.Analysis.Interpolation.Basic
import Submission.Port.Aesm

/-!
# The vector-valued phase-power family

This file sets up the vector-valued (`H`-valued, `H` a complex inner product space) analogue of the
analytic family `Work.Analysis.Interpolation.analyticFamily` used for Riesz--Thorin/Stein
interpolation of `L^p` estimates, together with the elementary API needed to run Hadamard's
three-lines argument on the pairing `∑_n ⟪T f n, g n⟫` of a linear operator against a test
sequence.

The scalar family of `Work.Analysis.Interpolation.Basic` is
`c ↦ ‖c‖ ^ t * c / ‖c‖`; its vector-valued analogue must keep the *direction* of a vector and only
rescales its norm, which is what `vecPhasePow x t = ‖x‖ ^{t-1} • x` does.  The whole point is that
this rescaling is a *scalar multiple* of `x`, so that all norms and the
`‖x‖ ≡ ‖x‖ ^ (t.re)` identity of the scalar case carry over verbatim, while the holomorphic
dependence on `t` is preserved.

## Main definitions

* `Work.Analysis.IWMultiplier.vecCoef x t = ‖x‖ ^ (t - 1)` (and `0` at `x = 0`) — the scalar
  coefficient;
* `Work.Analysis.IWMultiplier.vecPhasePow x t = vecCoef x t • x` — the elementary family;
* `Work.Analysis.IWMultiplier.vecFam f t₀ t₁ z = fun n ↦ vecPhasePow (f n) ((1-z) t₀ + z t₁)` —
  the analytic family attached to a sequence;
* `Work.Analysis.IWMultiplier.pairingEnorm u v = ‖∑'_n ⟪u n, v n⟫‖ₑ` and
  `Work.Analysis.IWMultiplier.pairingFamily` — notation-free wrappers used to *state* the
  Hölder and pairing-duality lemmas about the Ionescu--Wainger multiplier.

## Main results

* `norm_vecPhasePow_of_pos_re`, `enorm_vecPhasePow_of_pos_re` — the norm of the elementary family;
* `vecCoef_star`, `expFamily_ofReal_star` — the behaviour under complex conjugation of the
  parameter, which is what makes the pairing `z ↦ ∑_n ⟪T (f_z) n, g_z n⟫` holomorphic;
* `differentiable_vecCoef_expFamily`, `differentiable_vecPhasePow_expFamily` — entireness in `z`;
* `enorm_vecFam`, `lintegral_enorm_vecFam_rpow`, `eLpNorm_vecFam_re_zero`,
  `eLpNorm_vecFam_re_one` — the `L^p` norm of the family on the two boundary lines of the strip.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace Work.Analysis.IWMultiplier

open Work.Analysis.Interpolation

/-! ## The elementary vector-valued family -/

section Defs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The scalar coefficient `‖x‖ ^ (t - 1)` attached to a vector `x` (and `0` at `x = 0`). -/
noncomputable def vecCoef (x : H) (t : ℂ) : ℂ :=
  if x = 0 then 0 else ((‖x‖ : ℂ)) ^ (t - 1)

/-- The elementary vector-valued phase-power family `x ↦ ‖x‖ ^ (t - 1) • x`: a scalar multiple of
`x` whose norm is `‖x‖ ^ t.re` when `0 < t.re`, and which reduces to `x` at `t = 1`. -/
noncomputable def vecPhasePow (x : H) (t : ℂ) : H := vecCoef x t • x

/-- The analytic family attached to a sequence `f : ℤ → H` and to the affine exponent family
`z ↦ (1 - z) t₀ + z t₁` of *real* exponents `t₀, t₁`. -/
noncomputable def vecFam (f : ℤ → H) (t₀ t₁ : ℝ) (z : ℂ) : ℤ → H :=
  fun n => vecPhasePow (f n) (expFamily (t₀ : ℂ) (t₁ : ℂ) z)

/-- The `enorm` of the `ℂ`-inner-product pairing of two sequences; a notation-free wrapper. -/
noncomputable def pairingEnorm (u v : ℤ → H) : ENNReal :=
  ‖∑' n : ℤ, ⟪u n, v n⟫_ℂ‖ₑ

end Defs

section Basic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem vecCoef_zero (t : ℂ) : vecCoef (0 : H) t = 0 := by
  simp [vecCoef]

@[simp] theorem vecPhasePow_zero (t : ℂ) : vecPhasePow (0 : H) t = 0 := by
  simp [vecPhasePow]

theorem vecPhasePow_eq_smul (x : H) (t : ℂ) : vecPhasePow x t = vecCoef x t • x := rfl

@[simp] theorem vecPhasePow_one (x : H) : vecPhasePow x 1 = x := by
  by_cases hx : x = 0
  · rw [hx, vecPhasePow_zero]
  · rw [vecPhasePow, vecCoef, if_neg hx, sub_self, Complex.cpow_zero, one_smul]

theorem norm_vecCoef (x : H) (t : ℂ) :
    ‖vecCoef x t‖ = if x = 0 then 0 else ‖x‖ ^ (t.re - 1) := by
  by_cases hx : x = 0
  · subst hx; simp [vecCoef]
  · rw [vecCoef, if_neg hx, if_neg hx,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hx), Complex.sub_re, Complex.one_re]

theorem norm_vecPhasePow_of_pos_re {x : H} {t : ℂ} (ht : 0 < t.re) :
    ‖vecPhasePow x t‖ = ‖x‖ ^ t.re := by
  by_cases hx : x = 0
  · rw [hx, vecPhasePow_zero, norm_zero, Real.zero_rpow (ne_of_gt ht)]
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : (t - 1).re = t.re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    calc ‖vecPhasePow x t‖ = ‖vecCoef x t‖ * ‖x‖ := by
          rw [vecPhasePow, norm_smul]
      _ = ‖x‖ ^ (t.re - 1) * ‖x‖ := by rw [norm_vecCoef x t, if_neg hx]
      _ = ‖x‖ ^ (t.re - 1) * ‖x‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖x‖ ^ ((t.re - 1) + 1) := (Real.rpow_add hr _ _).symm
      _ = ‖x‖ ^ t.re := by ring_nf

theorem enorm_vecPhasePow_of_pos_re {x : H} {t : ℂ} (ht : 0 < t.re) :
    ‖vecPhasePow x t‖ₑ = ‖x‖ₑ ^ t.re := by
  rw [← ofReal_norm, norm_vecPhasePow_of_pos_re ht, ← ofReal_norm x,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) ht.le]

theorem enorm_vecPhasePow_of_re_eq_zero {x : H} {t : ℂ} (ht : t.re = 0) :
    ‖vecPhasePow x t‖ₑ ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, vecPhasePow_zero, enorm_zero]; exact zero_le_one
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h2 : ‖x‖ ^ ((0 : ℝ) - 1) * ‖x‖ = 1 := by
      rw [show (0 : ℝ) - 1 = -1 by norm_num, Real.rpow_neg_one,
        inv_mul_cancel₀ (ne_of_gt hr)]
    rw [← ofReal_norm, vecPhasePow, norm_smul, norm_vecCoef x t, if_neg hx, ht, h2,
      ENNReal.ofReal_one]

end Basic

/-! ## Conjugation of the parameter -/

section Star

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The affine exponent family with *real* endpoints is compatible with complex conjugation of the
parameter. -/
theorem expFamily_ofReal_star (t₀ t₁ : ℝ) (z : ℂ) :
    expFamily (t₀ : ℂ) (t₁ : ℂ) (star z) = star (expFamily (t₀ : ℂ) (t₁ : ℂ) z) := by
  simp only [expFamily, ← starRingEnd_apply, map_add, map_mul, map_sub, map_one,
    Complex.conj_ofReal]

/-- The scalar coefficient of the vector-valued family is compatible with complex conjugation of
the parameter. -/
theorem vecCoef_star (x : H) (t : ℂ) : vecCoef x (star t) = star (vecCoef x t) := by
  by_cases hx : x = 0
  · simp [vecCoef, hx]
  · have hc : ((‖x‖ : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (norm_nonneg x)]
      exact Ne.symm Real.pi_ne_zero
    have h1 : star t - 1 = (starRingEnd ℂ) (t - 1) := by
      rw [← starRingEnd_apply, map_sub, map_one]
    rw [vecCoef, if_neg hx, vecCoef, if_neg hx, h1, ← starRingEnd_apply,
      Complex.cpow_conj ((‖x‖ : ℝ) : ℂ) (t - 1) hc, Complex.conj_ofReal]

theorem vecFam_star_apply (f : ℤ → H) (t₀ t₁ : ℝ) (z : ℂ) (n : ℤ) :
    vecFam f t₀ t₁ (star z) n
      = (star (vecCoef (f n) (expFamily (t₀ : ℂ) (t₁ : ℂ) z))) • f n := by
  rw [vecFam, expFamily_ofReal_star, vecPhasePow_eq_smul, vecCoef_star]

theorem vecFam_apply (f : ℤ → H) (t₀ t₁ : ℝ) (z : ℂ) (n : ℤ) :
    vecFam f t₀ t₁ z n = vecCoef (f n) (expFamily (t₀ : ℂ) (t₁ : ℂ) z) • f n := rfl

end Star

/-! ## Entireness in the parameter -/

section Diff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem differentiable_expFamily (t₀ t₁ : ℂ) :
    Differentiable ℂ fun z : ℂ => expFamily t₀ t₁ z := by
  show Differentiable ℂ fun z : ℂ => (1 - z) * t₀ + z * t₁
  exact ((differentiable_const (1 : ℂ)).sub differentiable_id).mul_const t₀ |>.add
    (differentiable_id.mul_const t₁)

theorem differentiable_vecCoef_expFamily (x : H) (t₀ t₁ : ℂ) :
    Differentiable ℂ fun z : ℂ => vecCoef x (expFamily t₀ t₁ z) := by
  by_cases hx : x = 0
  · rw [show (fun z : ℂ => vecCoef x (expFamily t₀ t₁ z)) = fun _ => (0 : ℂ) by
      funext z; rw [hx, vecCoef_zero]]
    exact differentiable_const 0
  · have hcoe : (fun z : ℂ => vecCoef x (expFamily t₀ t₁ z))
        = fun z : ℂ => ((‖x‖ : ℂ)) ^ (expFamily t₀ t₁ z - 1) := by
      funext z
      rw [vecCoef, if_neg hx]
    rw [hcoe]
    refine Differentiable.const_cpow ?_ (Or.inl ?_)
    · exact (differentiable_expFamily t₀ t₁).sub_const 1
    · simpa using (norm_ne_zero_iff.mpr hx)

theorem differentiable_vecPhasePow_expFamily (x : H) (t₀ t₁ : ℂ) :
    Differentiable ℂ fun z : ℂ => vecPhasePow x (expFamily t₀ t₁ z) := by
  by_cases hx : x = 0
  · rw [show (fun z : ℂ => vecPhasePow x (expFamily t₀ t₁ z)) = fun _ => (0 : H) by
      funext z; rw [hx, vecPhasePow_zero]]
    exact differentiable_const 0
  · have hcoe : (fun z : ℂ => vecPhasePow x (expFamily t₀ t₁ z))
        = fun z : ℂ => ((‖x‖ : ℂ) ^ (expFamily t₀ t₁ z - 1)) • x := by
      funext z
      rw [vecPhasePow, vecCoef, if_neg hx]
    rw [hcoe]
    refine Differentiable.smul_const ?_ x
    refine Differentiable.const_cpow ?_ (Or.inl ?_)
    · exact (differentiable_expFamily t₀ t₁).sub_const 1
    · simpa using (norm_ne_zero_iff.mpr hx)

end Diff

/-! ## The family at a point of the strip -/

section Fam

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem vecFam_self {f : ℤ → H} {t₀ t₁ : ℝ} {θ : ℂ}
    (h : (1 - θ) * (t₀ : ℂ) + θ * (t₁ : ℂ) = 1) : vecFam f t₀ t₁ θ = f := by
  funext n
  simp only [vecFam, expFamily]
  rw [h, vecPhasePow_one]

theorem enorm_vecFam {f : ℤ → H} {t₀ t₁ : ℝ} {z : ℂ}
    (hz : 0 < (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re) (n : ℤ) :
    ‖vecFam f t₀ t₁ z n‖ₑ = ‖f n‖ₑ ^ (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re :=
  enorm_vecPhasePow_of_pos_re hz

theorem enorm_vecFam_le_one {f : ℤ → H} {t₀ t₁ : ℝ} {z : ℂ}
    (hz : (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re = 0) (n : ℤ) :
    ‖vecFam f t₀ t₁ z n‖ₑ ≤ 1 :=
  enorm_vecPhasePow_of_re_eq_zero hz

theorem lintegral_enorm_vecFam_rpow {μ : Measure ℤ} {f : ℤ → H} {t₀ t₁ : ℝ} {z : ℂ} {r u : ℝ}
    (hr : 0 < r) (hz : (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re = r) :
    ∫⁻ n, ‖vecFam f t₀ t₁ z n‖ₑ ^ u ∂μ = ∫⁻ n, ‖f n‖ₑ ^ (u * r) ∂μ := by
  refine lintegral_congr fun n => ?_
  rw [enorm_vecFam (by rw [hz]; exact hr) n, hz, ← ENNReal.rpow_mul, mul_comm]

theorem eLpNorm_vecFam_re_zero {μ : Measure ℤ} {f : ℤ → H} {p₀ p₁ p : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : 0 < p) {z : ℂ} (hz : z.re = 0) :
    eLpNorm (vecFam f (p / p₀) (p / p₁) z) (ENNReal.ofReal p₀) μ
      = (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / p₀) := by
  have hr : 0 < p / p₀ := by positivity
  have hre : (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).re = p / p₀ := by
    rw [expFamily_ofReal_re, hz]; ring
  have hmul : p₀ * (p / p₀) = p := by field_simp
  have hexp : (1 / p) * (p / p₀) = 1 / p₀ := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p₀)
      (f := vecFam f (p / p₀) (p / p₁) z) (ENNReal.ofReal_ne_zero_iff.mpr hp₀)
      ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p) (f := f)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp₀.le, ENNReal.toReal_ofReal hp.le,
    lintegral_enorm_vecFam_rpow (μ := μ) hr hre, hmul,
    ← ENNReal.rpow_mul, hexp]

theorem eLpNorm_vecFam_re_one {μ : Measure ℤ} {f : ℤ → H} {p₀ p₁ p : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : 0 < p) {z : ℂ} (hz : z.re = 1) :
    eLpNorm (vecFam f (p / p₀) (p / p₁) z) (ENNReal.ofReal p₁) μ
      = (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / p₁) := by
  have hr : 0 < p / p₁ := by positivity
  have hre : (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).re = p / p₁ := by
    rw [expFamily_ofReal_re, hz]; ring
  have hmul : p₁ * (p / p₁) = p := by field_simp
  have hexp : (1 / p) * (p / p₁) = 1 / p₁ := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p₁)
      (f := vecFam f (p / p₀) (p / p₁) z) (ENNReal.ofReal_ne_zero_iff.mpr hp₁)
      ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p) (f := f)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp₁.le, ENNReal.toReal_ofReal hp.le,
    lintegral_enorm_vecFam_rpow (μ := μ) hr hre, hmul,
    ← ENNReal.rpow_mul, hexp]


theorem eLpNorm_vecFam_re_zero_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : ℤ → H} {p₀ p : ℝ} (t₀ t₁ : ℝ) (ht : t₀ = p / p₀) (hp₀ : 0 < p₀) (hp : 0 < p)
    {μ : Measure ℤ} {z : ℂ} (hz : z.re = 0) :
    eLpNorm (vecFam f t₀ t₁ z) (ENNReal.ofReal p₀) μ
      = (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / p₀) := by
  have hr : 0 < p / p₀ := by positivity
  have hre : (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re = p / p₀ := by
    rw [ht, expFamily_ofReal_re, hz]; ring
  have hmul : p₀ * (p / p₀) = p := by field_simp
  have hexp : (1 / p) * (p / p₀) = 1 / p₀ := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p₀)
      (f := vecFam f t₀ t₁ z) (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p) (f := f)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp₀.le, ENNReal.toReal_ofReal hp.le,
    lintegral_enorm_vecFam_rpow (μ := μ) hr hre, hmul, ← ENNReal.rpow_mul, hexp]

theorem eLpNorm_vecFam_re_one_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : ℤ → H} {p₁ p : ℝ} (t₀ t₁ : ℝ) (ht : t₁ = p / p₁) (hp₁ : 0 < p₁) (hp : 0 < p)
    {μ : Measure ℤ} {z : ℂ} (hz : z.re = 1) :
    eLpNorm (vecFam f t₀ t₁ z) (ENNReal.ofReal p₁) μ
      = (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / p₁) := by
  have hr : 0 < p / p₁ := by positivity
  have hre : (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re = p / p₁ := by
    rw [ht, expFamily_ofReal_re, hz]; ring
  have hmul : p₁ * (p / p₁) = p := by field_simp
  have hexp : (1 / p) * (p / p₁) = 1 / p₁ := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p₁)
      (f := vecFam f t₀ t₁ z) (ENNReal.ofReal_ne_zero_iff.mpr hp₁) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p) (f := f)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp₁.le, ENNReal.toReal_ofReal hp.le,
    lintegral_enorm_vecFam_rpow (μ := μ) hr hre, hmul, ← ENNReal.rpow_mul, hexp]

end Fam

end Work.Analysis.IWMultiplier
