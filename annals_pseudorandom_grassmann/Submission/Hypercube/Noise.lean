import Mathlib
import Submission.Hypercube.CondHyp
import Submission.Commons.Analysis.Inequalities.sum_norm_mul_pow_four_le
import Submission.Commons.Analysis.Walsh.noise_char_complex

/-!
# The Hölder argument and the noise operator on the cube `𝔽₂ⁿ`

This file completes §2 of arXiv:2209.04243 (the "warm-up" chapter on `𝔽₂ⁿ`):

* `innerC` — the inner product `⟨f,g⟩ = 2^{-n} ∑_x f x · conj (g x)`, with the
  conjugate-Parseval identity `innerC_eq_sum`: `⟨f,g⟩ = ∑_S a_S · conj (b_S)` for the
  Efron–Stein coefficients `a_S` of `f` and `b_S` of `g`;
* the identity `innerC (f^{≤d}) f = ‖f^{≤d}‖₂²` (`innerC_trunc`);
* `Tρ` — the noise operator `T_ρ` (each coordinate kept with probability `ρ`), with
  `Tρ_chi` (it multiplies the character `χ_S` by `ρ^{|S|}`) and the Efron–Stein formula
  `Tρ_eq_sum`;
* `IsBool`, and **Corollary 2.14** (`holder_argument`): for a Boolean `(d,ε)`-global `f`,
  `‖f^{≤d}‖₂⁸ ≤ (800d)^d ε ‖f‖₂⁸` in fourth-power form;
* `mu_trunc_le_eps` — the `ε^{1/4}(800d)^{d/4}` form;
* **Corollary 2.15** (`noise_bound` and `noise_bound'`): `⟨T_ρ f, f⟩ ≤ (ρ^{d+1} +
  ε^{1/4}(800d)^{d/4}) ‖f‖₂²`, and its small-set-expansion form for indicator functions.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Hypercube

noncomputable section

variable {n : ℕ}

/-! ## The conjugate, and the inner product `⟨·,·⟩` -/

lemma starRingEnd_stdAddChar (a : ZMod 2) :
    (starRingEnd ℂ) (ZMod.stdAddChar a) = ZMod.stdAddChar a := by
  rw [stdAddChar_zmod_two]
  rw [map_pow]
  simp

lemma star_chi (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (starRingEnd ℂ) (chi S x) = chi S x := by
  simpa [chi, starRingEnd_stdAddChar] using
    map_prod (starRingEnd ℂ) (fun i => ZMod.stdAddChar (x i)) S

lemma walshFourier_starRingEnd (g : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    walshFourier (fun x => (starRingEnd ℂ) (g x)) S =
      (starRingEnd ℂ) (walshFourier g S) := by
  rw [walshFourier, walshFourier]
  rw [map_sum (starRingEnd ℂ) (fun x => g x * chi S x) Finset.univ]
  exact Finset.sum_congr rfl fun x _ => by rw [map_mul, star_chi]

/-- The inner product `⟨f,g⟩ = 2^{-n} ∑_x f x · conj (g x)` on the cube. -/
def innerC (f g : (Fin n → ZMod 2) → ℂ) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ x, f x * (starRingEnd ℂ) (g x)

/-- Parseval for the sesquilinear form. -/
theorem walsh_parseval_starRingEnd (f g : (Fin n → ZMod 2) → ℂ) :
    (∑ S : Finset (Fin n), walshFourier f S * (starRingEnd ℂ) (walshFourier g S)) =
      (2 : ℂ) ^ n * ∑ x : Fin n → ZMod 2, f x * (starRingEnd ℂ) (g x) := by
  have hcongr : (∑ S : Finset (Fin n),
        walshFourier f S * walshFourier (fun x => (starRingEnd ℂ) (g x)) S)
      = ∑ S : Finset (Fin n),
        walshFourier f S * (starRingEnd ℂ) (walshFourier g S) :=
    Finset.sum_congr rfl fun S _ => by rw [walshFourier_starRingEnd]
  have h := walsh_parseval f (fun x => (starRingEnd ℂ) (g x))
  rw [hcongr] at h
  exact h

lemma starRingEnd_inv_two_pow : (starRingEnd ℂ) (((2 : ℂ) ^ n)⁻¹) = ((2 : ℂ) ^ n)⁻¹ := by
  rw [map_inv₀]
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2, ← Complex.ofReal_pow, Complex.conj_ofReal]

/-- **Conjugate Parseval**: the inner product of `f` and `g` is the sum of the products of the
Efron--Stein coefficients. -/
theorem innerC_eq_sum (f g : (Fin n → ZMod 2) → ℂ) :
    innerC f g = ∑ S : Finset (Fin n),
      efronCoeff f S * (starRingEnd ℂ) (efronCoeff g S) := by
  have hc : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1 : innerC f g = ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ *
      ∑ S : Finset (Fin n),
        walshFourier f S * (starRingEnd ℂ) (walshFourier g S) := by
    rw [innerC, walsh_parseval_starRingEnd]
    rw [show ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ *
          (((2 : ℂ) ^ n) * ∑ x, f x * (starRingEnd ℂ) (g x))
        = ((2 : ℂ) ^ n)⁻¹ * ∑ x, f x * (starRingEnd ℂ) (g x) from by
      rw [mul_assoc ((2 : ℂ) ^ n)⁻¹ ((2 : ℂ) ^ n)⁻¹ (((2 : ℂ) ^ n) * _),
        ← mul_assoc ((2 : ℂ) ^ n)⁻¹ ((2 : ℂ) ^ n) _, inv_mul_cancel₀ hc, one_mul]]
  rw [h1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [efronCoeff, efronCoeff, map_mul, starRingEnd_inv_two_pow]
  ring

/-- The Efron--Stein coefficient of a truncation. -/
lemma efronCoeff_trunc (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronCoeff (trunc d f) S = if S.card ≤ d then efronCoeff f S else 0 := by
  rw [efronCoeff, walshFourier_trunc, efronCoeff]
  by_cases h : S.card ≤ d
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The projection identity**: `⟨f^{≤d}, f⟩ = ‖f^{≤d}‖₂²`. -/
theorem innerC_trunc (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) :
    innerC (trunc d f) f = (mu (trunc d f) : ℂ) := by
  rw [innerC_eq_sum]
  have hterm : ∀ S : Finset (Fin n),
      efronCoeff (trunc d f) S * (starRingEnd ℂ) (efronCoeff f S)
        = if S.card ≤ d then (Complex.normSq (efronCoeff f S) : ℂ) else 0 := by
    intro S
    rw [efronCoeff_trunc]
    by_cases h : S.card ≤ d
    · simp only [if_pos h, Complex.mul_conj]
    · simp only [if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun S _ => hterm S), ← Finset.sum_filter]
  rw [mu_trunc_eq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun S _ => by rw [Complex.normSq_eq_norm_sq]

/-! ## The noise operator `T_ρ` -/

/-- The noise operator on the cube: each coordinate is kept with probability `ρ` and otherwise
resampled uniformly. -/
def Tρ (ρ : ℝ) (f : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  fun x => ∑ y : Fin n → ZMod 2,
    (∏ i : Fin n, (if y i = x i then (((1 + ρ) / 2 : ℝ) : ℂ)
      else (((1 - ρ) / 2 : ℝ) : ℂ))) * f y

lemma Tρ_add (ρ : ℝ) (f g : (Fin n → ZMod 2) → ℂ) : Tρ ρ (f + g) = Tρ ρ f + Tρ ρ g := by
  funext x
  simp only [Tρ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma Tρ_smul (ρ : ℝ) (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) : Tρ ρ (c • f) = c • Tρ ρ f := by
  funext x
  simp only [Tρ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

lemma Tρ_sum (ρ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ℂ) :
    Tρ ρ (∑ i ∈ s, f i) = ∑ i ∈ s, Tρ ρ (f i) := by
  funext x
  simp only [Tρ, Finset.sum_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **The character is an eigenfunction of `T_ρ` with eigenvalue `ρ^{|S|}`.** -/
lemma Tρ_chi (ρ : ℝ) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    Tρ ρ (chi S) x = ((ρ : ℂ) ^ S.card) * chi S x := by
  simpa [Tρ, chi] using Commons.Analysis.Walsh.noise_char_complex ρ S x

lemma Tρ_chi_fun (ρ : ℝ) (S : Finset (Fin n)) :
    Tρ ρ (chi S) = ((ρ : ℂ) ^ S.card) • chi S := by
  funext x; rw [Tρ_chi, Pi.smul_apply, smul_eq_mul]

/-- Fourier inversion, in operator form. -/
lemma sum_efronStein_smul (f : (Fin n → ZMod 2) → ℂ) :
    f = ∑ S : Finset (Fin n), efronCoeff f S • chi S := by
  conv_lhs => rw [← sum_efronStein f]
  exact Finset.sum_congr rfl fun S _ => efronStein_eq_smul f S

/-- **The Efron--Stein formula for the noise operator**: `T_ρ` multiplies the component
`f^{=S}` by `ρ^{|S|}`. -/
theorem Tρ_eq_sum (ρ : ℝ) (f : (Fin n → ZMod 2) → ℂ) :
    Tρ ρ f = ∑ S : Finset (Fin n), (efronCoeff f S * (ρ : ℂ) ^ S.card) • chi S := by
  conv_lhs => rw [sum_efronStein_smul f]
  rw [Tρ_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Tρ_smul, Tρ_chi_fun, smul_smul]

/-- The inner product of two sums of multiples of distinct characters. -/
theorem innerC_sum_smul_chi (s : Finset (Finset (Fin n))) (a b : Finset (Fin n) → ℂ) :
    innerC (∑ T ∈ s, a T • chi T) (∑ T ∈ s, b T • chi T) = ∑ T ∈ s, a T * (starRingEnd ℂ) (b T) := by
  have hc : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hL : ∀ x : Fin n → ZMod 2,
      (∑ T ∈ s, a T • chi T) x * (starRingEnd ℂ) ((∑ T ∈ s, b T • chi T) x)
      = ∑ T ∈ s, ∑ U ∈ s, (a T * (starRingEnd ℂ) (b U)) * (chi T x * chi U x) := by
    intro x
    rw [Finset.sum_apply, Finset.sum_apply, map_sum]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, star_chi]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun U _ => by ring
  rw [innerC, Finset.sum_congr rfl (fun x _ => hL x)]
  rw [Finset.sum_comm]
  have hstep : ∀ T ∈ s, (∑ x : Fin n → ZMod 2, ∑ U ∈ s,
        (a T * (starRingEnd ℂ) (b U)) * (chi T x * chi U x))
      = a T * (starRingEnd ℂ) (b T) * (2 : ℂ) ^ n := by
    intro T hT
    rw [Finset.sum_comm, Finset.sum_eq_single T]
    · rw [← Finset.mul_sum, chi_orthogonal, if_pos rfl]
    · intro U hU hUT
      rw [← Finset.mul_sum, chi_orthogonal, if_neg (fun h => hUT h.symm), mul_zero]
    · intro h
      exact absurd hT h
  rw [Finset.sum_congr rfl hstep]
  have hfin : ∀ T : Finset (Fin n),
      ((2 : ℂ) ^ n)⁻¹ * (a T * (starRingEnd ℂ) (b T) * (2 : ℂ) ^ n)
        = a T * (starRingEnd ℂ) (b T) := by
    intro T
    rw [show ((2 : ℂ) ^ n)⁻¹ * (a T * (starRingEnd ℂ) (b T) * (2 : ℂ) ^ n)
        = (((2 : ℂ) ^ n)⁻¹ * (2 : ℂ) ^ n) * (a T * (starRingEnd ℂ) (b T)) by ring,
      inv_mul_cancel₀ hc, one_mul]
  rw [Finset.mul_sum]
  simp_rw [hfin]

/-- The inner product of `T_ρ f` with `f`. -/
theorem innerC_Tρ (ρ : ℝ) (f : (Fin n → ZMod 2) → ℂ) :
    innerC (Tρ ρ f) f = ∑ S : Finset (Fin n),
      ((ρ : ℂ) ^ S.card) * (Complex.normSq (efronCoeff f S) : ℂ) := by
  have hT : Tρ ρ f = ∑ S : Finset (Fin n), (efronCoeff f S * (ρ : ℂ) ^ S.card) • chi S :=
    Tρ_eq_sum ρ f
  have hf : f = ∑ S : Finset (Fin n), efronCoeff f S • chi S := sum_efronStein_smul f
  have key := innerC_sum_smul_chi (Finset.univ)
    (fun S => efronCoeff f S * (ρ : ℂ) ^ S.card) (fun S : Finset (Fin n) => efronCoeff f S)
  rw [← hf] at key
  rw [← hT] at key
  rw [key]
  refine Finset.sum_congr rfl fun S _ => ?_
  calc (efronCoeff f S * (ρ : ℂ) ^ S.card) * (starRingEnd ℂ) (efronCoeff f S)
      = ((ρ : ℂ) ^ S.card) * (efronCoeff f S * (starRingEnd ℂ) (efronCoeff f S)) := by ring
    _ = ((ρ : ℂ) ^ S.card) * (Complex.normSq (efronCoeff f S) : ℂ) := by rw [Complex.mul_conj]

/-- The real form of `innerC_Tρ`: `⟨T_ρ f, f⟩ = ∑_S ρ^{|S|} ‖f^{=S}‖₂²`. -/
theorem re_innerC_Tρ (ρ : ℝ) (f : (Fin n → ZMod 2) → ℂ) :
    (innerC (Tρ ρ f) f).re = ∑ S : Finset (Fin n), ρ ^ S.card * ‖efronCoeff f S‖ ^ 2 := by
  have h : (∑ S : Finset (Fin n),
        ((ρ : ℂ) ^ S.card) * (Complex.normSq (efronCoeff f S) : ℂ))
      = ((∑ S : Finset (Fin n), ρ ^ S.card * ‖efronCoeff f S‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Complex.ofReal_pow, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
  rw [innerC_Tρ, h, Complex.ofReal_re]

/-- **The noise-operator bound, quantitative form**: for `0 ≤ ρ ≤ 1`, the `T_ρ`-inner product is
bounded by the high-degree part plus the degree-`d` truncation. -/
theorem noise_bound_gen (d : ℕ) (ρ : ℝ) (f : (Fin n → ZMod 2) → ℂ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (innerC (Tρ ρ f) f).re ≤ ρ ^ (d + 1) * mu f + mu (trunc d f) := by
  rw [re_innerC_Tρ]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S : Finset (Fin n) => S.card ≤ d)
    (fun S : Finset (Fin n) => ρ ^ S.card * ‖efronCoeff f S‖ ^ 2)
  rw [← hsplit]
  have h1 : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ d),
      ρ ^ S.card * ‖efronCoeff f S‖ ^ 2) ≤ mu (trunc d f) := by
    rw [mu_trunc_eq]
    refine Finset.sum_le_sum fun S _ => ?_
    calc ρ ^ S.card * ‖efronCoeff f S‖ ^ 2 ≤ 1 * ‖efronCoeff f S‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hρ0 hρ1) (sq_nonneg _)
      _ = ‖efronCoeff f S‖ ^ 2 := one_mul _
  have h2 : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ S.card ≤ d),
      ρ ^ S.card * ‖efronCoeff f S‖ ^ 2) ≤ ρ ^ (d + 1) * mu f := by
    have hstep : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ S.card ≤ d),
        ρ ^ S.card * ‖efronCoeff f S‖ ^ 2)
        ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ S.card ≤ d),
            ρ ^ (d + 1) * ‖efronCoeff f S‖ ^ 2 :=
      Finset.sum_le_sum fun S hS => by
        have hS' : d + 1 ≤ S.card := by
          have := (Finset.mem_filter.mp hS).2
          omega
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0 hρ1 hS') (sq_nonneg _)
    refine le_trans hstep ?_
    rw [mu_eq_sum_efronCoeff, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun S : Finset (Fin n) => ¬ S.card ≤ d) _)
        (fun S _ _ => sq_nonneg _))
      (pow_nonneg hρ0 _)
  linarith

/-! ## Boolean functions, the Hölder argument, and its corollaries -/

/-- A Boolean function on the cube: it takes only the values `0` and `1`. -/
def IsBool (f : (Fin n → ZMod 2) → ℂ) : Prop := ∀ x, f x = 0 ∨ f x = 1

variable {f : (Fin n → ZMod 2) → ℂ}

lemma IsBool.ofReal (hb : IsBool f) (x : Fin n → ZMod 2) : f x = ((f x).re : ℂ) := by
  rcases hb x with h | h <;> rw [h] <;> norm_num

lemma IsBool.re_nonneg (hb : IsBool f) (x : Fin n → ZMod 2) : 0 ≤ (f x).re := by
  rcases hb x with h | h <;> rw [h] <;> norm_num

lemma IsBool.norm_eq (hb : IsBool f) (x : Fin n → ZMod 2) : ‖f x‖ = (f x).re := by
  rcases hb x with h | h <;> rw [h] <;> norm_num

lemma IsBool.conj_eq (hb : IsBool f) (x : Fin n → ZMod 2) : (starRingEnd ℂ) (f x) = f x := by
  rw [hb.ofReal x, Complex.conj_ofReal]

lemma IsBool.norm_sq_eq (hb : IsBool f) (x : Fin n → ZMod 2) : ‖f x‖ ^ 2 = ‖f x‖ := by
  rcases hb x with h | h <;> rw [h] <;> norm_num

lemma IsBool.rpow_four_thirds (hb : IsBool f) (x : Fin n → ZMod 2) :
    ‖f x‖ ^ ((4 : ℝ) / 3) = ‖f x‖ := by
  rcases hb x with h | h
  · rw [h, norm_zero, Real.zero_rpow (by norm_num : ((4 : ℝ) / 3) ≠ 0)]
  · rw [h, norm_one, Real.one_rpow]

lemma sum_norm_four (g : (Fin n → ZMod 2) → ℂ) :
    (∑ x : Fin n → ZMod 2, ‖g x‖ ^ 4) = (2 : ℝ) ^ n * mu4 g := by
  rw [mu4, ← mul_assoc, mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ n) ≠ 0), one_mul]

lemma sum_rpow_four_thirds (hb : IsBool f) :
    (∑ x : Fin n → ZMod 2, ‖f x‖ ^ ((4 : ℝ) / 3)) = (2 : ℝ) ^ n * mu f := by
  have h : ∀ x : Fin n → ZMod 2, ‖f x‖ ^ ((4 : ℝ) / 3) = ‖f x‖ ^ 2 := fun x => by
    rw [hb.rpow_four_thirds x, hb.norm_sq_eq x]
  rw [Finset.sum_congr rfl (fun x _ => h x), mu, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ n) ≠ 0), one_mul]

/-- The Hölder step: `‖f^{≤d}‖₂² ≤ 2^{-n} ∑_x ‖f^{≤d} x‖ · ‖f x‖`. -/
theorem mu_le_sum_norm_mul (d : ℕ) (hb : IsBool f) :
    mu (trunc d f) ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖trunc d f x‖ * ‖f x‖ := by
  have h1 : mu (trunc d f) = ((2 : ℝ) ^ n)⁻¹ *
      ∑ x : Fin n → ZMod 2, ((trunc d f x) * f x).re := by
    rw [show mu (trunc d f) = (innerC (trunc d f) f).re from by
      rw [innerC_trunc, Complex.ofReal_re], innerC]
    simp only [hb.conj_eq]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num, ← Complex.ofReal_pow,
      ← Complex.ofReal_inv]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun x _ =>
    le_trans (Complex.re_le_norm (trunc d f x * f x)) (le_of_eq (norm_mul _ _))

/-- **Corollary 2.14 of arXiv:2209.04243** (`4`-th power form): a Boolean global function has
its degree-`d` truncation controlled by its own `2`-norm. -/
theorem holder_argument (d : ℕ) (ε : ℝ) (hb : IsBool f) (hglob : Global d ε f) :
    (mu (trunc d f)) ^ 4 ≤ (800 * d : ℝ) ^ d * ε * (mu f) ^ 4 := by
  have hBpos : 0 < (2 : ℝ) ^ n := by positivity
  have hAB := mu_le_sum_norm_mul d hb
  have hkey : mu (trunc d f) * (2 : ℝ) ^ n ≤ ∑ x : Fin n → ZMod 2, ‖trunc d f x‖ * ‖f x‖ := by
    calc mu (trunc d f) * (2 : ℝ) ^ n
        ≤ (((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖trunc d f x‖ * ‖f x‖) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hAB hBpos.le
      _ = ∑ x, ‖trunc d f x‖ * ‖f x‖ := by
          rw [mul_comm (((2 : ℝ) ^ n)⁻¹) (∑ x, ‖trunc d f x‖ * ‖f x‖), mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hBpos), mul_one]
  have hHolder := Commons.Analysis.Inequalities.sum_norm_mul_pow_four_le (Finset.univ)
    (fun x => trunc d f x) (fun x => f x)
  rw [sum_norm_four (trunc d f), sum_rpow_four_thirds hb] at hHolder
  have hA4 : (mu (trunc d f)) ^ 4 ≤ mu4 (trunc d f) * (mu f) ^ 3 := by
    have h' : (mu (trunc d f)) ^ 4 * ((2 : ℝ) ^ n) ^ 4
        ≤ (mu4 (trunc d f) * (mu f) ^ 3) * ((2 : ℝ) ^ n) ^ 4 := by
      calc (mu (trunc d f)) ^ 4 * ((2 : ℝ) ^ n) ^ 4
          = (mu (trunc d f) * (2 : ℝ) ^ n) ^ 4 := by ring
        _ ≤ (∑ x, ‖trunc d f x‖ * ‖f x‖) ^ 4 :=
            pow_le_pow_left₀ (mul_nonneg (mu_nonneg _) hBpos.le) hkey 4
        _ ≤ ((2 : ℝ) ^ n * mu4 (trunc d f)) * ((2 : ℝ) ^ n * mu f) ^ 3 := hHolder
        _ = (mu4 (trunc d f) * (mu f) ^ 3) * ((2 : ℝ) ^ n) ^ 4 := by ring
    exact le_of_mul_le_mul_right h' (pow_pos hBpos 4)
  have htrunc := trunc_hyp d f hglob
  have hAf : mu (trunc d f) ≤ mu f := mu_trunc_le d f
  have hε0 : 0 ≤ ε := le_trans (mu_nonneg f) (mu_le_of_global hglob)
  calc (mu (trunc d f)) ^ 4 ≤ mu4 (trunc d f) * (mu f) ^ 3 := hA4
    _ ≤ ((800 * d : ℝ) ^ d * ε * mu (trunc d f)) * (mu f) ^ 3 :=
        mul_le_mul_of_nonneg_right htrunc (pow_nonneg (mu_nonneg f) 3)
    _ ≤ ((800 * d : ℝ) ^ d * ε * mu f) * (mu f) ^ 3 := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (mu_nonneg f) 3)
        exact mul_le_mul_of_nonneg_left hAf (mul_nonneg (by positivity) hε0)
    _ = (800 * d : ℝ) ^ d * ε * (mu f) ^ 4 := by ring

/-- From a bound on `A ^ 4` by `K · B ^ 4` with nonnegative entries, deduce the bound on `A`
itself with the fourth root of `K`. -/
theorem pow_four_le_mul_pow_four {A B K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h : A ^ 4 ≤ K * B ^ 4) : A ≤ K ^ ((1 : ℝ) / 4) * B := by
  have hKq4 : (K ^ ((1 : ℝ) / 4)) ^ 4 = K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
    norm_num
  have hKq0 : 0 ≤ K ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hK _
  refine (pow_le_pow_iff_left₀ hA (mul_nonneg hKq0 hB) (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
  calc A ^ 4 ≤ K * B ^ 4 := h
    _ = (K ^ ((1 : ℝ) / 4) * B) ^ 4 := by rw [mul_pow, hKq4]

/-- **Corollary 2.14** in the `ε^{1/4}` form used for the noise operator. -/
theorem mu_trunc_le_eps (d : ℕ) (ε : ℝ) (hb : IsBool f) (hglob : Global d ε f) :
    mu (trunc d f) ≤ (ε * (800 * d : ℝ) ^ d) ^ ((1 : ℝ) / 4) * mu f := by
  have h4 := holder_argument d ε hb hglob
  have hA0 : 0 ≤ mu (trunc d f) := mu_nonneg _
  have hB0 : 0 ≤ mu f := mu_nonneg f
  have hε0 : 0 ≤ ε := le_trans hB0 (mu_le_of_global hglob)
  have hK0 : 0 ≤ ε * (800 * d : ℝ) ^ d := mul_nonneg hε0 (by positivity)
  have h4' : (mu (trunc d f)) ^ 4 ≤ (ε * (800 * d : ℝ) ^ d) * (mu f) ^ 4 := by
    refine le_trans h4 ?_
    rw [mul_comm ((800 * d : ℝ) ^ d) ε]
  exact pow_four_le_mul_pow_four hA0 hB0 hK0 h4'

/-- **Corollary 2.15 of arXiv:2209.04243**: the noise-stability bound for a Boolean global
function. -/
theorem noise_bound (d : ℕ) (ε ρ : ℝ) (hb : IsBool f) (hglob : Global d ε f)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (innerC (Tρ ρ f) f).re ≤
      (ρ ^ (d + 1) + (ε * (800 * d : ℝ) ^ d) ^ ((1 : ℝ) / 4)) * mu f := by
  have h1 := noise_bound_gen d ρ f hρ0 hρ1
  have h2 := mu_trunc_le_eps d ε hb hglob
  have hB0 : 0 ≤ mu f := mu_nonneg f
  nlinarith [h1, h2]

/-- **Small-set expansion on the cube** (`𝔽₂ⁿ` case of Corollary 2.15): the indicator of a set
whose indicator is `(d,ε)`-global has noise-stability at most `ρ^{d+1} + ε^{1/4}(800d)^{d/4}`. -/
theorem sse_cube (d : ℕ) (ε ρ : ℝ) (A : (Fin n → ZMod 2) → Prop) [DecidablePred A]
    (hglob : Global d ε (fun x => if A x then 1 else 0)) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (innerC (Tρ ρ (fun x => if A x then 1 else 0)) (fun x => if A x then 1 else 0)).re ≤
      (ρ ^ (d + 1) + (ε * (800 * d : ℝ) ^ d) ^ ((1 : ℝ) / 4)) *
        mu (fun x => if A x then 1 else 0) :=
  noise_bound d ε ρ (fun x => by split <;> simp) hglob hρ0 hρ1

end

end Submission.Hypercube
