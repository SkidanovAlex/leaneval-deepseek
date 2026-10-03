/-
Copyright (c) 2026 The Annals formalisation team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Interpolation

/-!
# Interpolation of `Lᵖ` estimates: the analytic families

This is the first module of the chapter `Work.Analysis.Interpolation`, which builds
Riesz--Thorin interpolation and Stein's multilinear interpolation of `Lᵖ` estimates, in the
extended-seminorm (`MeasureTheory.eLpNorm`) formulation used throughout
Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022).

The seed module `Submission.Interpolation` (namespace `Interp`) contains the two elementary
facts: Hölder interpolation of the `ℒᵖ` integral (`Interp.lintegral_enorm_rpow_interp`) and
log-convexity of the `Lᵖ` seminorm (`Interp.eLpNorm_interp`).  Here we set up the *analytic
families* to which Hadamard's three-lines theorem (`Mathlib.Analysis.Complex.Hadamard`) is
applied.

## The construction

For a complex number `c` and a complex parameter `t` put
`phasePow c t = ‖c‖ ^ t * c / ‖c‖` (and `0` for `c = 0`).  This is the elementary
"multiplicative rescaling" of `c` by the complex power `‖c‖ ^ t`: it has modulus
`‖c‖ ^ (re t)` and equals `c` when `t = 1`.  For a *finite* (simple) function `f` and an
affine family of exponents `z ↦ (1 - z) t₀ + z t₁`, the function
`analyticFamily f t₀ t₁ z = fun x ↦ phasePow (f x) ((1 - z) t₀ + z t₁)`
is a finite linear combination of the indicators of the level sets of `f` with coefficients
that are entire functions of `z`; this is what makes the three-lines argument work for an
arbitrary (merely) bilinear form.

## Main definitions

* `Work.Analysis.Interpolation.phase`, `phasePow`: the phase and the elementary family;
* `Work.Analysis.Interpolation.expFamily`: the affine exponent family `(1-z) t₀ + z t₁`;
* `Work.Analysis.Interpolation.analyticFamily`: the analytic family of functions;
* `Work.Analysis.Interpolation.bilinearFamily`: the scalar family `z ↦ Λ f_z g_z`.

## Main results

* `phasePow_one`, `norm_phasePow`, `enorm_phasePow`, `differentiable_phasePow`,
  `differentiable_phasePow_expFamily`;
* `analyticFamily_self`, `enorm_analyticFamily`,
  `lintegral_enorm_analyticFamily_rpow` (the `ℒᵖ` integral of the family, in terms of the
  integral of `f` itself);
* exponent arithmetic: `interp_self`, `expFamily_interp_self`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Work
namespace Analysis
namespace Interpolation

variable {α : Type*} [MeasurableSpace α]

/-! ## The elementary family `c ↦ ‖c‖ ^ t · c/‖c‖` -/

/-- The phase of a complex number: its direction, and `0` at `0`. -/
noncomputable def phase (c : ℂ) : ℂ := if c = 0 then 0 else c / (‖c‖ : ℂ)

/-- The elementary analytic family `c ↦ ‖c‖ ^ t * c / ‖c‖` of a complex number.  It has
modulus `‖c‖ ^ t.re` and reduces to `c` when `t = 1`. -/
noncomputable def phasePow (c t : ℂ) : ℂ := (‖c‖ : ℂ) ^ t * phase c

@[simp] lemma phase_zero : phase 0 = 0 := by simp [phase]

lemma phase_eq_of_ne_zero {c : ℂ} (hc : c ≠ 0) : phase c = c / (‖c‖ : ℂ) := by
  simp [phase, hc]

@[simp] lemma norm_phase_of_ne_zero {c : ℂ} (hc : c ≠ 0) : ‖phase c‖ = 1 := by
  have h : ‖(((‖c‖ : ℝ)) : ℂ)‖ = ‖c‖ := by simp
  rw [phase_eq_of_ne_zero hc, norm_div, h, div_self (ne_of_gt (norm_pos_iff.mpr hc))]

lemma norm_phase_le_one (c : ℂ) : ‖phase c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc, phase]
  · simp [norm_phase_of_ne_zero hc]

lemma enorm_phase_le_one (c : ℂ) : ‖phase c‖ₑ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc, phase]
  · rw [← ofReal_norm, norm_phase_of_ne_zero hc, ENNReal.ofReal_one]

lemma enorm_phase_of_ne_zero {c : ℂ} (hc : c ≠ 0) : ‖phase c‖ₑ = 1 := by
  rw [← ofReal_norm, norm_phase_of_ne_zero hc, ENNReal.ofReal_one]

/-- `phase c`, rescaled by `‖c‖`, gives back `c`. -/
lemma phase_mul_norm {c : ℂ} (hc : c ≠ 0) : phase c * (‖c‖ : ℂ) = c := by
  rw [phase_eq_of_ne_zero hc, div_mul_cancel₀]
  simpa using norm_ne_zero_iff.mpr hc

lemma norm_mul_phase {c : ℂ} (hc : c ≠ 0) : (‖c‖ : ℂ) * phase c = c := by
  rw [mul_comm, phase_mul_norm hc]

/-- The elementary family at `t = 1` is the identity. -/
@[simp] lemma phasePow_one (c : ℂ) : phasePow c 1 = c := by
  by_cases hc : c = 0
  · simp [hc, phasePow, phase]
  · rw [phasePow, Complex.cpow_one, norm_mul_phase hc]

@[simp] lemma phasePow_zero_left (t : ℂ) : phasePow 0 t = 0 := by
  simp [phasePow, phase]

lemma norm_phasePow_of_pos_re {c t : ℂ} (ht : 0 < t.re) :
    ‖phasePow c t‖ = ‖c‖ ^ t.re := by
  by_cases hc : c = 0
  · subst hc
    rw [phasePow_zero_left, norm_zero, Real.zero_rpow (ne_of_gt ht)]
  · rw [phasePow, norm_mul, norm_phase_of_ne_zero hc, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]

lemma enorm_phasePow_of_pos_re {c t : ℂ} (ht : 0 < t.re) :
    ‖phasePow c t‖ₑ = ‖c‖ₑ ^ t.re := by
  rw [← ofReal_norm, ← ofReal_norm, norm_phasePow_of_pos_re ht,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg c) ht.le]

/-- The norm of the elementary family, for a nonzero `c` and an arbitrary exponent. -/
lemma norm_phasePow {c : ℂ} (hc : c ≠ 0) (t : ℂ) :
    ‖phasePow c t‖ = ‖c‖ ^ t.re := by
  rw [phasePow, norm_mul, norm_phase_of_ne_zero hc, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]

/-- The extended norm of the elementary family, for a nonzero `c` and an arbitrary exponent. -/
lemma enorm_phasePow {c : ℂ} (hc : c ≠ 0) (t : ℂ) :
    ‖phasePow c t‖ₑ = ‖c‖ₑ ^ t.re := by
  rw [← ofReal_norm, norm_phasePow hc t, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hc)]

/-- `t ↦ ‖c‖ ^ t * c / ‖c‖` is entire. -/
theorem differentiable_phasePow (c : ℂ) : Differentiable ℂ fun t : ℂ => phasePow c t := by
  by_cases hc : c = 0
  · subst hc
    simp only [phasePow_zero_left]
    fun_prop
  · have hne : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hc)
    have h1 : Differentiable ℂ fun t : ℂ => (((‖c‖ : ℝ) : ℂ)) ^ t :=
      fun t => DifferentiableAt.const_cpow differentiableAt_id (Or.inl hne)
    have heq : (fun t : ℂ => phasePow c t)
        = fun t : ℂ => (((‖c‖ : ℝ) : ℂ)) ^ t * phase c := by
      funext t
      rw [phasePow, phase_eq_of_ne_zero hc]
    rw [heq]
    exact h1.mul (differentiable_const (phase c))

/-! ## The affine exponent family and the analytic family of functions -/

/-- The affine family of complex exponents `z ↦ (1 - z) t₀ + z t₁`. -/
def expFamily (t₀ t₁ z : ℂ) : ℂ := (1 - z) * t₀ + z * t₁

/-- The analytic family of functions attached to `f : α → ℂ` and to the exponent family
`z ↦ (1 - z) t₀ + z t₁`. -/
noncomputable def analyticFamily (f : α → ℂ) (t₀ t₁ : ℂ) (z : ℂ) : α → ℂ :=
  fun x => phasePow (f x) (expFamily t₀ t₁ z)

lemma expFamily_apply (t₀ t₁ z : ℂ) : expFamily t₀ t₁ z = (1 - z) * t₀ + z * t₁ := rfl

@[simp] lemma expFamily_zero (t₀ t₁ : ℂ) : expFamily t₀ t₁ 0 = t₀ := by simp [expFamily]

@[simp] lemma expFamily_one (t₀ t₁ : ℂ) : expFamily t₀ t₁ 1 = t₁ := by simp [expFamily]

/-- The real part of the affine exponent family, for real exponents. -/
lemma expFamily_ofReal_re (a₀ a₁ : ℝ) (z : ℂ) :
    (expFamily (a₀ : ℂ) (a₁ : ℂ) z).re = (1 - z.re) * a₀ + z.re * a₁ := by
  simp only [expFamily, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re]
  ring

/-- The real part of the affine exponent family at a real parameter. -/
lemma expFamily_ofReal_re_ofReal (a₀ a₁ x : ℝ) :
    (expFamily (a₀ : ℂ) (a₁ : ℂ) (x : ℂ)).re = (1 - x) * a₀ + x * a₁ := by
  simp [expFamily_ofReal_re, Complex.ofReal_re]

/-- `z ↦ ‖c‖ ^ ((1-z) t₀ + z t₁) * c/‖c‖` is entire. -/
theorem differentiable_phasePow_expFamily (c t₀ t₁ : ℂ) :
    Differentiable ℂ fun z : ℂ => phasePow c (expFamily t₀ t₁ z) := by
  refine (differentiable_phasePow c).comp ?_
  show Differentiable ℂ fun z : ℂ => (1 - z) * t₀ + z * t₁
  exact ((differentiable_const (1 : ℂ)).sub differentiable_id).mul_const t₀ |>.add
    (differentiable_id.mul_const t₁)

omit [MeasurableSpace α] in
/-- The analytic family at a parameter at which the exponent equals `1` is `f` itself. -/
@[simp] lemma analyticFamily_self {f : α → ℂ} {t₀ t₁ θ : ℂ}
    (h : (1 - θ) * t₀ + θ * t₁ = 1) : analyticFamily f t₀ t₁ θ = f := by
  funext x
  rw [analyticFamily, expFamily, h, phasePow_one]

omit [MeasurableSpace α] in
/-- Pointwise extended norm of the analytic family. -/
lemma enorm_analyticFamily {f : α → ℂ} {t₀ t₁ z : ℂ} (hz : 0 < (expFamily t₀ t₁ z).re)
    (x : α) : ‖analyticFamily f t₀ t₁ z x‖ₑ = ‖f x‖ₑ ^ (expFamily t₀ t₁ z).re :=
  enorm_phasePow_of_pos_re hz

/-- The `ℒᵖ` integral of the analytic family, computed in terms of `f` itself: if the exponent
family has real part `r > 0` at `z`, then the `u`-th power integral of the family is the
`(u * r)`-th power integral of `f`.  (No measurability hypothesis is needed: both sides are
extended integrals of nonnegative functions, and the identity is pointwise.) -/
lemma lintegral_enorm_analyticFamily_rpow (μ : Measure α) {f : α → ℂ} {t₀ t₁ z : ℂ} {r u : ℝ}
    (hr : 0 < r) (hz : (expFamily t₀ t₁ z).re = r) :
    ∫⁻ x, ‖analyticFamily f t₀ t₁ z x‖ₑ ^ u ∂μ = ∫⁻ x, ‖f x‖ₑ ^ (u * r) ∂μ := by
  refine lintegral_congr fun x => ?_
  rw [enorm_analyticFamily (by rw [hz]; exact hr) x, hz, ← ENNReal.rpow_mul, mul_comm]

/-! ## The bilinear family to which the three-lines theorem is applied -/

section Bilinear

variable {β : Type*}

/-- The value at `z` of the *bilinear* analytic family attached to a pair of functions: this is the
scalar function of `z` to which Hadamard's three lines theorem is applied in Stein's interpolation
of bilinear forms (with `Λ` playing the role of the bilinear pairing). -/
noncomputable def bilinearFamily (Λ : (α → ℂ) → (β → ℂ) → ℂ) (f : α → ℂ) (g : β → ℂ)
    (t₀ t₁ u₀ u₁ : ℂ) (z : ℂ) : ℂ :=
  Λ (analyticFamily f t₀ t₁ z) (analyticFamily g u₀ u₁ z)

omit [MeasurableSpace α] in
lemma bilinearFamily_apply (Λ : (α → ℂ) → (β → ℂ) → ℂ) (f : α → ℂ) (g : β → ℂ)
    (t₀ t₁ u₀ u₁ : ℂ) (z : ℂ) :
    bilinearFamily Λ f g t₀ t₁ u₀ u₁ z = Λ (analyticFamily f t₀ t₁ z) (analyticFamily g u₀ u₁ z) :=
  rfl

omit [MeasurableSpace α] in
/-- At a point where both exponent families take the value `1`, the bilinear family is the original
pairing. -/
@[simp] lemma bilinearFamily_self {Λ : (α → ℂ) → (β → ℂ) → ℂ} {f : α → ℂ} {g : β → ℂ}
    {t₀ t₁ u₀ u₁ θ : ℂ} (h₁ : (1 - θ) * t₀ + θ * t₁ = 1) (h₂ : (1 - θ) * u₀ + θ * u₁ = 1) :
    bilinearFamily Λ f g t₀ t₁ u₀ u₁ θ = Λ f g := by
  simp only [bilinearFamily, analyticFamily_self h₁, analyticFamily_self h₂]

end Bilinear

/-! ## Arithmetic of the interpolated exponents -/

/-- If `1/p = (1-θ)/p₀ + θ/p₁` then `(1-θ)·p/p₀ + θ·p/p₁ = 1`. -/
lemma interp_self {p₀ p₁ p θ : ℝ} (hp : p ≠ 0)
    (h : 1 / p = (1 - θ) / p₀ + θ / p₁) : (1 - θ) * (p / p₀) + θ * (p / p₁) = 1 := by
  have h' : p * ((1 - θ) / p₀ + θ / p₁) = 1 := by
    rw [← h, mul_one_div, div_self hp]
  have h2 : (1 - θ) * (p / p₀) + θ * (p / p₁) = p * ((1 - θ) / p₀ + θ / p₁) := by ring
  rw [h2, h']

/-- The complex form of `interp_self`, in terms of the exponent family. -/
lemma expFamily_interp_self {p₀ p₁ p θ : ℝ} (hp : p ≠ 0)
    (h : 1 / p = (1 - θ) / p₀ + θ / p₁) :
    expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) (θ : ℂ) = 1 := by
  have hreal := interp_self hp h
  rw [expFamily, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_add]
  norm_cast

end Interpolation
end Analysis
end Work
