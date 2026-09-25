import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size
import Submission.Work.BourgainPlan.Maximal.tsum_annulus_moment

/-!
# Pointwise translation estimate for the annulus kernel family

Let `b` be an annulus symbol family (`AnnulusSymbolSmooth b`, all members smooth), let
`K_m = 𝓕⁻ (b m)` be the `m`-th kernel and let `j : ℤ`.  This file proves the pointwise,
scale-summed translation estimate

`(∑_n ‖K_{j+n}(z - y) - K_{j+n}(z)‖²)^{1/2} ≤ C |y| / |z|²`   whenever `2|y| < |z|`.

The key point, compared with the weaker integrated bound of
`annulusLocalizedKernelHormander`, is that *each* scale `m` is estimated sharply:

`‖K_m(z - y) - K_m(z)‖ ≤ C |y| (2^{-m})² (1 + 2^{-m}|z|)^{-N}`  (`2|y| < |z|`, every `N`).

The proof of the latter has three ingredients.

* The *moment symbol* `ξ ↦ 2^m ξ b_m(ξ)` is again an annulus symbol family of the same type (the
  derivative bounds are shifted by one order, see `annulusMomentSymbol_iteratedDeriv_bound`), so
  `annulusKernel_size` applies to it.
* The derivative of `𝓕 (b m)` is the Fourier transform of the (signed) moment symbol
  (`Real.deriv_fourier`), whence `‖(𝓕 (b m))' w‖ ≤ C (2^{-m})² (1 + 2^{-m}|w|)^{-N}`.
* The mean value theorem on the segment between `-z` and `y - z` (all of whose points satisfy
  `|w| ≥ |z|/2`) converts this into the difference estimate.

The final assembly sums the squares over the scales and compares with the geometric series bound
`tsum_annulus_moment`.
-/

open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter

/-! ## 0. The Leibniz formula for `(ξ b(ξ))^{(k)}` -/

private lemma deriv_coe_complex (x : ℝ) : deriv (fun t : ℝ => (t : ℂ)) x = 1 :=
  ((hasDerivAt_id (x : ℂ)).comp_ofReal).deriv

/-- The iterated derivatives of the coercion `ℝ → ℂ`. -/
private lemma iteratedDeriv_coe_complex : ∀ (i : ℕ) (ξ : ℝ),
    iteratedDeriv i (fun x : ℝ => (x : ℂ)) ξ
      = if i = 0 then (ξ : ℂ) else if i = 1 then 1 else 0 := by
  intro i
  induction i with
  | zero => intro ξ; simp
  | succ i ih =>
    intro ξ
    rw [iteratedDeriv_succ]
    have hfun : (fun x : ℝ => iteratedDeriv i (fun y : ℝ => (y : ℂ)) x)
        = fun x : ℝ => if i = 0 then (x : ℂ) else if i = 1 then 1 else 0 := by
      funext x; exact ih x
    change deriv (fun x : ℝ => iteratedDeriv i (fun y : ℝ => (y : ℂ)) x) ξ
      = (if i + 1 = 0 then (ξ : ℂ) else if i + 1 = 1 then 1 else 0)
    rw [hfun]
    rcases i with _ | _ | i
    · have h : (fun x : ℝ => if 0 = 0 then (x : ℂ) else if 0 = 1 then 1 else 0)
          = fun x : ℝ => (x : ℂ) := by funext x; simp
      rw [h, deriv_coe_complex]
      norm_num
    · simp
    · have h1 : i + 2 ≠ 0 := by omega
      have h2 : i + 2 ≠ 1 := by omega
      have h3 : i + 2 + 1 ≠ 0 := by omega
      have h4 : i + 2 + 1 ≠ 1 := by omega
      simp only [h1, h2, h3, h4, if_false, deriv_const]

/-- **Leibniz formula**, specialised to the identity factor:
`(ξ ↦ ξ b(ξ))^{(k)} (ξ) = ξ b^{(k)}(ξ) + k b^{(k-1)}(ξ)`. -/
lemma annulusIteratedDeriv_mul_id (b : ℝ → ℂ)
    (hb : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) b) (k : ℕ) (ξ : ℝ) :
    iteratedDeriv k (fun x : ℝ => x * b x) ξ
      = ξ * iteratedDeriv k b ξ + (k : ℂ) * iteratedDeriv (k - 1) b ξ := by
  have hf : (fun x : ℝ => x * b x) = (fun x : ℝ => (x : ℂ)) * b := rfl
  have hf' : ContDiffAt ℝ (((k : ℕ) : ℕ∞)) (fun x : ℝ => (x : ℂ)) ξ :=
    Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
  have hg' : ContDiffAt ℝ (((k : ℕ) : ℕ∞)) b ξ :=
    hb.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
  have hmul := iteratedDeriv_mul (f := fun x : ℝ => (x : ℂ)) (g := b) (x := ξ) (n := k) hf' hg'
  rw [hf, hmul]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℂ) * iteratedDeriv i (fun x : ℝ => (x : ℂ)) ξ * iteratedDeriv (k - i) b ξ
        = (if i = 0 then (ξ : ℂ) * iteratedDeriv (k - i) b ξ else 0)
          + (if i = 1 then (k : ℂ) * iteratedDeriv (k - i) b ξ else 0) := by
    intro i _
    rw [iteratedDeriv_coe_complex]
    by_cases h0 : i = 0
    · subst h0
      simp [Nat.choose_zero_right]
    · by_cases h1 : i = 1
      · subst h1
        simp [Nat.choose_one_right, h0]
      · simp [h0, h1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  rcases k with _ | k
  · simp
  · rw [if_pos (by simp : (0 : ℕ) ∈ Finset.range (k + 1 + 1)),
      if_pos (by simp : (1 : ℕ) ∈ Finset.range (k + 1 + 1))]
    simp

/-! ## 1. The moment symbol `ξ ↦ 2^m ξ b_m(ξ)` -/

/-- The moment symbol of the `m`-th member of the family `b`: `ξ ↦ 2^m ξ b_m(ξ)`.
Its inverse Fourier transform is the derivative of `𝓕⁻ (b m)`. -/
noncomputable def annulusMomentSymbol (b : ℤ → ℝ → ℂ) (m : ℤ) (ξ : ℝ) : ℂ :=
  ((2 : ℝ) ^ m : ℂ) * (ξ * b m ξ)

lemma annulusMomentSymbol_support (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b) :
    ∀ m ξ, annulusMomentSymbol b m ξ ≠ 0 →
      (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2 := by
  intro m ξ h
  have hbne : b m ξ ≠ 0 := by
    intro h0
    exact h (by rw [annulusMomentSymbol, h0, mul_zero, mul_zero])
  exact hb.1 m ξ hbne

lemma annulusMomentSymbol_eq_zero (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b) (m : ℤ) :
    ∀ ξ, (2 : ℝ) ^ (1 - m) < |ξ| → annulusMomentSymbol b m ξ = 0 := by
  intro ξ hξ
  rw [annulusMomentSymbol, annulusK_eq_zero b hb m ξ hξ]
  ring

lemma annulusMomentSymbol_iteratedDeriv_eq_zero (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (m : ℤ) (k : ℕ) :
    ∀ ξ, (2 : ℝ) ^ (1 - m) < |ξ| → iteratedDeriv k (annulusMomentSymbol b m) ξ = 0 := by
  induction k with
  | zero => intro ξ hξ; rw [iteratedDeriv_zero]; exact annulusMomentSymbol_eq_zero b hb m ξ hξ
  | succ k ih =>
    intro ξ hξ
    rw [iteratedDeriv_succ]
    exact annulusK_deriv_eq_zero_of_eq_zero_on_open (isOpen_lt continuous_const continuous_abs)
      (fun x hx => ih x hx) ξ hξ

lemma annulusMomentSymbol_contDiff (b : ℤ → ℝ → ℂ)
    (hsmooth : ∀ m, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (b m)) (m : ℤ) :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (annulusMomentSymbol b m) := by
  show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun ξ : ℝ => ((2 : ℝ) ^ m : ℂ) * (ξ * b m ξ))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.mul (hsmooth m))

/-- `‖(2^m : ℂ)‖ = 2^m`. -/
lemma norm_ofReal_zpow_two (m : ℤ) : ‖(((2 : ℝ) ^ m : ℂ))‖ = (2 : ℝ) ^ m := by
  have h1 : ‖(((2 : ℝ) ^ m : ℂ))‖ = |((2 : ℝ) ^ m)| := by simp
  rw [h1, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) m)]

/-- `2^m · 2^{m k} = 2^{m (k+1)}`. -/
lemma two_zpow_mul_succ (m : ℤ) (k : ℕ) :
    (2 : ℝ) ^ m * (2 : ℝ) ^ (m * k) = (2 : ℝ) ^ (m * (k + 1)) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- `2^m · 2^{1-m} = 2`. -/
lemma two_zpow_mul_one_sub (m : ℤ) : (2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m) = 2 := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    show m + (1 - m) = (1 : ℤ) by ring, zpow_one]

lemma annulusMomentSymbol_iteratedDeriv_bound (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (b m)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ξ,
      ‖iteratedDeriv k (annulusMomentSymbol b m) ξ‖ ≤ C * (2 : ℝ) ^ (m * k) := by
  rcases k with _ | k
  · -- `k = 0`: only the size of the symbol matters
    obtain ⟨C0, hC00, hC0⟩ := hb.2 0
    refine ⟨2 * C0, by positivity, fun m ξ => ?_⟩
    have hc : iteratedDeriv 0 (annulusMomentSymbol b m) ξ = ((2 : ℝ) ^ m : ℂ) * (ξ * b m ξ) := by
      rw [iteratedDeriv_zero]
      rfl
    rw [hc, norm_mul, norm_ofReal_zpow_two, norm_mul]
    have hξ : ‖(ξ : ℂ)‖ * ‖b m ξ‖ ≤ (2 : ℝ) ^ (1 - m) * C0 := by
      by_cases hb0 : b m ξ = 0
      · rw [hb0, norm_zero, mul_zero]
        positivity
      · have h2 : |ξ| ≤ (2 : ℝ) ^ (1 - m) :=
          le_of_not_gt (fun hlt => hb0 (annulusK_eq_zero b hb m ξ hlt))
        have h3 : ‖(ξ : ℂ)‖ = |ξ| := by simp
        rw [h3]
        exact mul_le_mul h2 (by simpa using hC0 m ξ) (norm_nonneg _) (by positivity)
    calc (2 : ℝ) ^ m * (‖(ξ : ℂ)‖ * ‖b m ξ‖)
        ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ (1 - m) * C0) :=
          mul_le_mul_of_nonneg_left hξ (by positivity)
      _ = ((2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m)) * C0 := by ring
      _ = 2 * C0 := by rw [two_zpow_mul_one_sub]
      _ = (2 * C0) * (2 : ℝ) ^ (m * 0) := by simp
  · -- `k = k+1`: Leibniz, the two surviving binomial coefficients being `1` and `k+1`
    obtain ⟨Ck, hCk0, hCk⟩ := hb.2 (k + 1)
    obtain ⟨Ckm, hCkm0, hCkm⟩ := hb.2 k
    refine ⟨2 * Ck + ((k + 1 : ℕ) : ℝ) * Ckm, by positivity, fun m ξ => ?_⟩
    have hc : iteratedDeriv (k + 1) (annulusMomentSymbol b m) ξ
        = ((2 : ℝ) ^ m : ℂ) * iteratedDeriv (k + 1) (fun x : ℝ => x * b m x) ξ := by
      have h : annulusMomentSymbol b m = fun ξ : ℝ => ((2 : ℝ) ^ m : ℂ) * (ξ * b m ξ) := rfl
      rw [h, iteratedDeriv_const_mul_field]
    rw [hc, annulusIteratedDeriv_mul_id (b m) (hsmooth m) (k + 1) ξ,
      show k + 1 - 1 = k by omega, norm_mul, norm_ofReal_zpow_two]
    have hbnd : ‖(ξ : ℂ) * iteratedDeriv (k + 1) (b m) ξ
        + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k (b m) ξ‖
        ≤ |ξ| * ‖iteratedDeriv (k + 1) (b m) ξ‖
          + ((k + 1 : ℕ) : ℝ) * ‖iteratedDeriv k (b m) ξ‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, show ‖(ξ : ℂ)‖ = |ξ| from by simp]
      · rw [norm_mul, Complex.norm_natCast]
    have h1 : |ξ| * ‖iteratedDeriv (k + 1) (b m) ξ‖
        ≤ (2 : ℝ) ^ (1 - m) * (Ck * (2 : ℝ) ^ (m * (k + 1))) := by
      by_cases h0 : iteratedDeriv (k + 1) (b m) ξ = 0
      · rw [h0, norm_zero, mul_zero]
        positivity
      · have hle : |ξ| ≤ (2 : ℝ) ^ (1 - m) :=
          le_of_not_gt (fun hlt => h0 (annulusK_iteratedDeriv_eq_zero b hb m (k + 1) ξ hlt))
        exact mul_le_mul hle (hCk m ξ) (norm_nonneg _) (by positivity)
    have h2 : ((k + 1 : ℕ) : ℝ) * ‖iteratedDeriv k (b m) ξ‖
        ≤ ((k + 1 : ℕ) : ℝ) * (Ckm * (2 : ℝ) ^ (m * k)) :=
      mul_le_mul_of_nonneg_left (hCkm m ξ) (by positivity)
    calc (2 : ℝ) ^ m * ‖(ξ : ℂ) * iteratedDeriv (k + 1) (b m) ξ
          + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k (b m) ξ‖
        ≤ (2 : ℝ) ^ m * (|ξ| * ‖iteratedDeriv (k + 1) (b m) ξ‖
            + ((k + 1 : ℕ) : ℝ) * ‖iteratedDeriv k (b m) ξ‖) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ (1 - m) * (Ck * (2 : ℝ) ^ (m * (k + 1)))
            + ((k + 1 : ℕ) : ℝ) * (Ckm * (2 : ℝ) ^ (m * k))) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
      _ = (2 * Ck + ((k + 1 : ℕ) : ℝ) * Ckm) * (2 : ℝ) ^ (m * (k + 1)) := by
          have e1 : (2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m) = 2 := two_zpow_mul_one_sub m
          have e2 : (2 : ℝ) ^ m * (2 : ℝ) ^ (m * k) = (2 : ℝ) ^ (m * (k + 1)) :=
            two_zpow_mul_succ m k
          calc (2 : ℝ) ^ m * ((2 : ℝ) ^ (1 - m) * (Ck * (2 : ℝ) ^ (m * (k + 1)))
                + ((k + 1 : ℕ) : ℝ) * (Ckm * (2 : ℝ) ^ (m * k)))
              = ((2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m)) * (Ck * (2 : ℝ) ^ (m * (k + 1)))
                + ((2 : ℝ) ^ m * (2 : ℝ) ^ (m * k)) * (((k + 1 : ℕ) : ℝ) * Ckm) := by ring
            _ = 2 * (Ck * (2 : ℝ) ^ (m * (k + 1)))
                + (2 : ℝ) ^ (m * (k + 1)) * (((k + 1 : ℕ) : ℝ) * Ckm) := by rw [e1, e2]
            _ = (2 * Ck + ((k + 1 : ℕ) : ℝ) * Ckm) * (2 : ℝ) ^ (m * (k + 1)) := by ring

theorem annulusMomentSymbol_fourierInv_size (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (b m)) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m z,
      ‖FourierTransform.fourierInv (annulusMomentSymbol b m) z‖
        ≤ C * (2 : ℝ) ^ (-m) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(N : ℝ)) := by
  have hAn : AnnulusSymbolSmooth (annulusMomentSymbol b) :=
    ⟨annulusMomentSymbol_support b hb,
      fun k => annulusMomentSymbol_iteratedDeriv_bound b hb hsmooth k⟩
  exact annulusKernel_size (annulusMomentSymbol b) hAn
    (fun m => annulusMomentSymbol_contDiff b hsmooth m) N

/-- Pulling a constant out of the Fourier transform. -/
lemma fourier_const_mul (c : ℂ) (g : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourier (fun x : ℝ => c * g x) w = c * FourierTransform.fourier g w := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def, Circle.smul_def]
  ring

lemma norm_neg_two_pi_I : ‖(-2 : ℂ) * ↑Real.pi * Complex.I‖ = 2 * Real.pi := by
  have h : (-2 : ℂ) * ↑Real.pi * Complex.I = ↑(-(2 * Real.pi)) * Complex.I := by
    push_cast; ring
  rw [h, norm_mul, Complex.norm_I, mul_one,
    show ‖(↑(-(2 * Real.pi)) : ℂ)‖ = |-(2 * Real.pi)| from by simp, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem annulusMoment_fourier_bound (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (b m)) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m w,
      ‖FourierTransform.fourier (fun ξ : ℝ => (-2 * ↑Real.pi * Complex.I * ↑ξ) • b m ξ) w‖
        ≤ C * ((2 : ℝ) ^ (-m)) ^ 2 * (1 + (2 : ℝ) ^ (-m) * |w|) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hbd⟩ := annulusMomentSymbol_fourierInv_size b hb hsmooth N
  refine ⟨2 * Real.pi * C, by positivity, fun m w => ?_⟩
  have hne : (((2 : ℝ) ^ m : ℂ)) ≠ 0 :=
    (by exact_mod_cast (zpow_pos (by norm_num : (0 : ℝ) < 2) m).ne' : (((2 : ℝ) ^ m : ℂ)) ≠ 0)
  have hmul : ∀ ξ : ℝ, (-2 * ↑Real.pi * Complex.I * ↑ξ) * b m ξ
      = ((-2 * ↑Real.pi * Complex.I) * (((2 : ℝ) ^ m : ℂ))⁻¹) * annulusMomentSymbol b m ξ := by
    intro ξ
    have h1 : (((2 : ℝ) ^ m : ℂ))⁻¹ * ((2 : ℝ) ^ m : ℂ) = 1 := inv_mul_cancel₀ hne
    rw [annulusMomentSymbol]
    calc (-2 * ↑Real.pi * Complex.I * ↑ξ) * b m ξ
        = (-2 * ↑Real.pi * Complex.I) * (↑ξ * b m ξ) := by ring
      _ = ((-2 * ↑Real.pi * Complex.I) * ((((2 : ℝ) ^ m : ℂ))⁻¹ * ((2 : ℝ) ^ m : ℂ)))
            * (↑ξ * b m ξ) := by rw [h1, mul_one]
      _ = ((-2 * ↑Real.pi * Complex.I) * (((2 : ℝ) ^ m : ℂ))⁻¹)
            * (((2 : ℝ) ^ m : ℂ) * (↑ξ * b m ξ)) := by ring
  have hfac : (fun ξ : ℝ => (-2 * ↑Real.pi * Complex.I * ↑ξ) • b m ξ)
      = fun ξ : ℝ => ((-2 * ↑Real.pi * Complex.I) * (((2 : ℝ) ^ m : ℂ))⁻¹)
          * annulusMomentSymbol b m ξ := by
    funext ξ
    rw [smul_eq_mul]
    exact hmul ξ
  have hnorm : ‖(-2 * ↑Real.pi * Complex.I) * (((2 : ℝ) ^ m : ℂ))⁻¹‖
      = 2 * Real.pi * (2 : ℝ) ^ (-m) := by
    rw [norm_mul, norm_inv, norm_ofReal_zpow_two, ← zpow_neg, norm_neg_two_pi_I]
  have harg := hbd m (-w)
  rw [abs_neg] at harg
  calc ‖FourierTransform.fourier (fun ξ : ℝ => (-2 * ↑Real.pi * Complex.I * ↑ξ) • b m ξ) w‖
      = ‖((-2 * ↑Real.pi * Complex.I) * (((2 : ℝ) ^ m : ℂ))⁻¹)‖
          * ‖FourierTransform.fourier (annulusMomentSymbol b m) w‖ := by
        rw [hfac, fourier_const_mul, norm_mul]
    _ = (2 * Real.pi * (2 : ℝ) ^ (-m))
          * ‖FourierTransform.fourier (annulusMomentSymbol b m) (-(-w))‖ := by
        rw [hnorm, neg_neg]
    _ = (2 * Real.pi * (2 : ℝ) ^ (-m))
          * ‖FourierTransform.fourierInv (annulusMomentSymbol b m) (-w)‖ := by
        rw [← Real.fourierInv_eq_fourier_neg]
    _ ≤ (2 * Real.pi * (2 : ℝ) ^ (-m))
          * (C * (2 : ℝ) ^ (-m) * (1 + (2 : ℝ) ^ (-m) * |w|) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left harg (by positivity)
    _ = (2 * Real.pi * C) * ((2 : ℝ) ^ (-m)) ^ 2
          * (1 + (2 : ℝ) ^ (-m) * |w|) ^ (-(N : ℝ)) := by ring

/-! ## 2. Sharp pointwise bound for the kernel difference -/

lemma annulusMulId_integrable (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (b m)) (m : ℤ) :
    Integrable (fun x : ℝ => x • b m x) := by
  have hcont : Continuous (fun x : ℝ => x • b m x) := by
    have h1 : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
    have h2 : (fun x : ℝ => x • b m x) = fun x : ℝ => (x : ℂ) * b m x := by
      funext x; exact Complex.real_smul
    rw [h2]
    exact h1.mul (hsmooth m).continuous
  have hsupp : HasCompactSupport (fun x : ℝ => x • b m x) := by
    have h2 : HasCompactSupport (fun x : ℝ => (x : ℂ) * b m x) :=
      (annulusK_hasCompactSupport b hb m).mul_left
    have h3 : (fun x : ℝ => x • b m x) = fun x : ℝ => (x : ℂ) * b m x := by
      funext x; exact Complex.real_smul
    rw [h3]
    exact h2
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- **Sharp pointwise translation bound.**  For `2|y| < |z|`, the difference of the kernel
`K_m = 𝓕⁻ (b m)` at the two points `z - y` and `z` is bounded by
`C |y| (2^{-m})² (1 + 2^{-m}|z|)^{-3}`. -/
theorem annulusKernel_difference_bound (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (b m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m y z, 2 * |y| < |z| →
      ‖FourierTransform.fourierInv (b m) (z - y) - FourierTransform.fourierInv (b m) z‖
        ≤ C * |y| * ((2 : ℝ) ^ (-m)) ^ 2 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by
  obtain ⟨C₀, hC₀, hbd⟩ := annulusMoment_fourier_bound b hb hsmooth 3
  refine ⟨C₀ * 8, by positivity, fun m y z hyz => ?_⟩
  have hInt : Integrable (b m) := by
    simpa only [iteratedDeriv_zero] using annulusK_integrable b hb hsmooth m 0
  have hInt' : Integrable (fun x : ℝ => x • b m x) := annulusMulId_integrable b hb hsmooth m
  have hderiv : deriv (FourierTransform.fourier (b m))
      = FourierTransform.fourier (fun x : ℝ => (-2 * ↑Real.pi * Complex.I * ↑x) • b m x) :=
    Real.deriv_fourier hInt hInt'
  -- bound on the decay factor on the region `|w| ≥ |z|/2`
  have hrpow : ∀ w : ℝ, |z| / 2 ≤ |w| →
      (1 + (2 : ℝ) ^ (-m) * |w|) ^ (-(3 : ℝ))
        ≤ 8 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by
    intro w hw
    have hbase : (1 + (2 : ℝ) ^ (-m) * |z|) / 2 ≤ 1 + (2 : ℝ) ^ (-m) * |w| := by
      have h := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-m))
      linarith
    have h3 : ((1 + (2 : ℝ) ^ (-m) * |z|) / 2) ^ 3 ≤ (1 + (2 : ℝ) ^ (-m) * |w|) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hbase 3
    have hpos1 : 0 < 1 + (2 : ℝ) ^ (-m) * |z| := by positivity
    have hpos2 : 0 < 1 + (2 : ℝ) ^ (-m) * |w| := by positivity
    have ha : (1 + (2 : ℝ) ^ (-m) * |w|) ^ (-(3 : ℝ))
        = ((1 + (2 : ℝ) ^ (-m) * |w|) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hpos2.le]
      norm_num
    have hb' : (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ))
        = ((1 + (2 : ℝ) ^ (-m) * |z|) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hpos1.le]
      norm_num
    rw [ha, hb']
    have hstep : (((1 + (2 : ℝ) ^ (-m) * |z|) / 2) ^ 3)⁻¹
        = 8 * ((1 + (2 : ℝ) ^ (-m) * |z|) ^ 3)⁻¹ := by
      rw [div_pow]
      field_simp
      ring
    calc ((1 + (2 : ℝ) ^ (-m) * |w|) ^ 3)⁻¹
        ≤ (((1 + (2 : ℝ) ^ (-m) * |z|) / 2) ^ 3)⁻¹ := inv_anti₀ (by positivity) h3
      _ = 8 * ((1 + (2 : ℝ) ^ (-m) * |z|) ^ 3)⁻¹ := hstep
  have hseg : ∀ w : ℝ, |w + z| ≤ |y| →
      ‖deriv (FourierTransform.fourier (b m)) w‖
        ≤ (C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * 8) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by
    intro w hw
    have hwz : |z| / 2 ≤ |w| := by
      have h1 : |z| ≤ |z + w| + |w| := by
        have h := abs_add_le (z + w) (-w)
        rw [show z + w + -w = z by ring, abs_neg] at h
        exact h
      have h2 : |z + w| ≤ |y| := by rw [add_comm]; exact hw
      linarith
    rw [hderiv]
    calc ‖FourierTransform.fourier (fun x : ℝ => (-2 * ↑Real.pi * Complex.I * ↑x) • b m x) w‖
        ≤ C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * (1 + (2 : ℝ) ^ (-m) * |w|) ^ (-(3 : ℝ)) := hbd m w
      _ ≤ C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * (8 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hrpow w hwz) (by positivity)
      _ = (C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * 8) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by ring
  -- the mean value theorem on the segment joining `-z` and `y - z`
  have hkey : ‖FourierTransform.fourier (b m) (y - z) - FourierTransform.fourier (b m) (-z)‖
      ≤ (C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * 8) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) * |y| := by
    rcases le_total (-z) (y - z) with hle | hle
    · have hdiff : ∀ w ∈ Set.Icc (-z) (y - z),
          DifferentiableAt ℝ (FourierTransform.fourier (b m)) w :=
        fun w _ => (Real.hasDerivAt_fourier hInt hInt' w).differentiableAt
      have hbound : ∀ w ∈ Set.Icc (-z) (y - z),
          ‖deriv (FourierTransform.fourier (b m)) w‖
            ≤ (C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * 8) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by
        intro w hw
        refine hseg w ?_
        have h1 : 0 ≤ w + z := by linarith [hw.1]
        have h2 : w + z ≤ y := by linarith [hw.2]
        rw [abs_of_nonneg h1]
        linarith [h2, le_abs_self y]
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
        (convex_Icc (-z) (y - z))
        (show -z ∈ Set.Icc (-z) (y - z) from ⟨le_rfl, hle⟩)
        (show y - z ∈ Set.Icc (-z) (y - z) from ⟨hle, le_rfl⟩)
      rwa [show (y - z) - (-z) = y by ring, Real.norm_eq_abs] at hmvt
    · have hdiff : ∀ w ∈ Set.Icc (y - z) (-z),
          DifferentiableAt ℝ (FourierTransform.fourier (b m)) w :=
        fun w _ => (Real.hasDerivAt_fourier hInt hInt' w).differentiableAt
      have hbound : ∀ w ∈ Set.Icc (y - z) (-z),
          ‖deriv (FourierTransform.fourier (b m)) w‖
            ≤ (C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * 8) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by
        intro w hw
        refine hseg w ?_
        have h1 : w + z ≤ 0 := by linarith [hw.2]
        have h2 : y ≤ w + z := by linarith [hw.1]
        rw [abs_of_nonpos h1]
        linarith [h2, neg_abs_le y]
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
        (convex_Icc (y - z) (-z))
        (show -z ∈ Set.Icc (y - z) (-z) from ⟨hle, le_rfl⟩)
        (show y - z ∈ Set.Icc (y - z) (-z) from ⟨le_rfl, hle⟩)
      rwa [show (y - z) - (-z) = y by ring, Real.norm_eq_abs] at hmvt
  calc ‖FourierTransform.fourierInv (b m) (z - y) - FourierTransform.fourierInv (b m) z‖
      = ‖FourierTransform.fourier (b m) (y - z) - FourierTransform.fourier (b m) (-z)‖ := by
        rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
        norm_num
    _ ≤ (C₀ * ((2 : ℝ) ^ (-m)) ^ 2 * 8) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) * |y| := hkey
    _ = (C₀ * 8) * |y| * ((2 : ℝ) ^ (-m)) ^ 2
          * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ)) := by ring

/-! ## 3. Assembly: summing the squares over the scales -/

theorem annulusKernel_translation (b : ℤ → ℝ → ℂ) (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b) (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (j : ℤ) : ∃ C : ℝ, 0 < C ∧ ∀ y z : ℝ, 2 * |y| < |z| → (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y) - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (C * |y| / |z| ^ 2) := by
  obtain ⟨C₁, hC₁, hPt⟩ := annulusKernel_difference_bound b hb hsmooth
  obtain ⟨K, hK, hGeom⟩ := tsum_annulus_moment
  refine ⟨C₁ * Real.sqrt K + 1, by positivity, fun y z hyz => ?_⟩
  have hzpos : 0 < |z| := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 * |y|) hyz
  have hz : z ≠ 0 := abs_pos.mp hzpos
  obtain ⟨hGsumm, hGbd⟩ := hGeom z hz
  set R : ℤ → ℝ := fun m =>
    (C₁ * |y| * ((2 : ℝ) ^ (-m)) ^ 2 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ))) ^ 2 with hR
  have hRnn : ∀ m, 0 ≤ R m := fun m => sq_nonneg _
  -- pointwise ENNReal comparison
  have hpoint : ∀ n : ℤ,
      ‖FourierTransform.fourierInv (b (j + n)) (z - y)
          - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (R (j + n)) := by
    intro n
    have h := hPt (j + n) y z hyz
    have h1 : ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ
        = ENNReal.ofReal ‖FourierTransform.fourierInv (b (j + n)) (z - y)
            - FourierTransform.fourierInv (b (j + n)) z‖ := (ofReal_norm _).symm
    rw [h1, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, hR]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)
  -- the square of the geometric bound
  have hReq : ∀ m, R m = (C₁ * |y|) ^ 2
      * (((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))) := by
    intro m
    have hpos : 0 < 1 + (2 : ℝ) ^ (-m) * |z| := by positivity
    have h6 : (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))
        = ((1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ))) ^ 2 := by
      rw [show (-(6 : ℝ)) = (-3) * 2 by norm_num, Real.rpow_mul hpos.le, Real.rpow_two]
    rw [hR, h6]
    ring
  have hRsumm : Summable R := by
    rw [show R = fun m => (C₁ * |y|) ^ 2
      * (((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))) from funext hReq]
    exact hGsumm.mul_left _
  have h4 : |z| ^ (-(4 : ℝ)) = (|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg z), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, show (|z| ^ (4 : ℕ) : ℝ) = (|z| ^ 2) ^ 2 by ring, pow_two, mul_inv]
  have h5 : (C₁ * Real.sqrt K + 1) ^ 2 * |y| ^ 2 * ((|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹)
      = ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2 := by
    have hz2 : (|z| ^ 2) ≠ 0 := by positivity
    rw [div_pow, mul_pow]
    field_simp
  have hC2 : C₁ ^ 2 * K ≤ (C₁ * Real.sqrt K + 1) ^ 2 := by
    have h := Real.sq_sqrt hK.le
    nlinarith [h, Real.sqrt_nonneg K, hC₁.le, sq_nonneg (C₁ * Real.sqrt K)]
  have hRbd : ∑' m : ℤ, R m ≤ ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2 := by
    rw [show R = fun m => (C₁ * |y|) ^ 2
      * (((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))) from funext hReq,
      Summable.tsum_mul_left _ hGsumm]
    calc (C₁ * |y|) ^ 2
          * ∑' m : ℤ, ((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))
        ≤ (C₁ * |y|) ^ 2 * (K * |z| ^ (-(4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hGbd (by positivity)
      _ = C₁ ^ 2 * K * |y| ^ 2 * ((|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹) := by rw [h4]; ring
      _ ≤ (C₁ * Real.sqrt K + 1) ^ 2 * |y| ^ 2 * ((|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (by positivity))
            (by positivity)
      _ = ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2 := h5
  -- ENNReal assembly
  have hsum1 : (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ))
      ≤ ∑' n : ℤ, ENNReal.ofReal (R (j + n)) := ENNReal.tsum_le_tsum hpoint
  have hreindex : (∑' n : ℤ, ENNReal.ofReal (R (j + n))) = ∑' m : ℤ, ENNReal.ofReal (R m) := by
    simpa using Equiv.tsum_eq (Equiv.addLeft j) (fun m : ℤ => ENNReal.ofReal (R m))
  have hsum2 : (∑' m : ℤ, ENNReal.ofReal (R m)) = ENNReal.ofReal (∑' m : ℤ, R m) :=
    (ENNReal.ofReal_tsum_of_nonneg hRnn hRsumm).symm
  have hfinal : (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ))
      ≤ ENNReal.ofReal (((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2) := by
    calc _ ≤ ∑' n : ℤ, ENNReal.ofReal (R (j + n)) := hsum1
      _ = ∑' m : ℤ, ENNReal.ofReal (R m) := hreindex
      _ = ENNReal.ofReal (∑' m : ℤ, R m) := hsum2
      _ ≤ ENNReal.ofReal (((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2) :=
          ENNReal.ofReal_le_ofReal hRbd
  calc (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hfinal (by norm_num)
    _ = ENNReal.ofReal ((((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2) ^ ((1 : ℝ) / 2)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) := by
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

end Work.BourgainPlan.Maximal
