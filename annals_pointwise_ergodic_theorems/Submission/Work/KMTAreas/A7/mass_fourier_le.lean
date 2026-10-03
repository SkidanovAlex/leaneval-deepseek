import Mathlib
import Submission.Work.KMTAreas.A7.fourier_decay_identity
import Submission.Work.KMTAreas.A7.support_iteratedDeriv_subset_tsupport
import Submission.Work.KMTAreas.A7.continuous_iteratedDeriv_two_section
import Submission.Work.KMTAreas.A7.tsum_int_min_inv_sq_le

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory

namespace Work.KMTAreas.A7

/-!
# Summability of the Fourier coefficients of a compactly supported two-dimensional symbol

For a `C⁴` symbol `ψ` supported in the box `[-w₁,w₁] × [-w₂,w₂]` whose second derivatives are
controlled by `B/w₁²`, `B/w₂²` and `B/(w₁²w₂²)`, the Fourier coefficients are summable with the
quantitative bound `∑_p ‖ψ̂(p)‖ ≤ 200 B`.
-/

/-- The oscillatory phase `x ↦ exp (2πi (-(ξ x)))`. -/
def kE (ξ x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (-(ξ * x)))

lemma norm_kE (ξ x : ℝ) : ‖kE ξ x‖ = 1 := by
  have h : (2 * Real.pi * Complex.I * (-(ξ * x)) : ℂ) =
      ((2 * Real.pi * (-(ξ * x)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [kE, Complex.norm_exp, h, Complex.mul_I_re]
  simp

lemma continuous_kE (ξ : ℝ) : Continuous fun x : ℝ => kE ξ x := by
  unfold kE
  fun_prop

lemma kE_mul (a b x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (-(a * x + b * y))) = kE a x * kE b y := by
  rw [kE, kE, ← Complex.exp_add]
  congr 1
  ring

/-- The constant `(2πξ)²` attached to the frequency `ξ`. -/
def kc (ξ : ℝ) : ℂ := (((2 * Real.pi * ξ) : ℝ) : ℂ) ^ 2

lemma kc_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) : kc ξ ≠ 0 := by
  rw [kc]
  refine pow_ne_zero 2 ?_
  intro h0
  have h1 : ((2 * Real.pi * ξ : ℝ) : ℂ).re = (0 : ℂ).re := congrArg Complex.re h0
  simp only [Complex.ofReal_re, Complex.zero_re] at h1
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hξ h1

lemma norm_kc_inv (ξ : ℝ) : ‖(kc ξ)⁻¹‖ = ((2 * Real.pi * ξ) ^ 2)⁻¹ := by
  have hz : ‖(((2 * Real.pi * ξ) : ℝ) : ℂ)‖ = |2 * Real.pi * ξ| := RCLike.norm_ofReal _
  rw [kc, norm_inv, norm_pow, hz, sq_abs]

/-- The weight attached to the frequency `p` at scale `w`. -/
def kA (w : ℝ) (p : ℤ) : ℝ := if p = 0 then 1 else 1 / (2 * Real.pi * w * (p : ℝ)) ^ 2

/-- The truncated weight. -/
def kM (w : ℝ) (p : ℤ) : ℝ := min 1 (kA w p)

lemma kM_eq (w : ℝ) (p : ℤ) :
    kM w p = if p = 0 then 1 else min 1 (1 / (2 * Real.pi * w * (p : ℝ)) ^ 2) := by
  by_cases h : p = 0 <;> simp [kM, kA, h]

lemma kA_nonneg (w : ℝ) (p : ℤ) : 0 ≤ kA w p := by
  by_cases h : p = 0 <;> simp [kA, h]; positivity

lemma kM_nonneg (w : ℝ) (p : ℤ) : 0 ≤ kM w p := le_min (by norm_num) (kA_nonneg w p)

/-- The double Fourier integral at the frequency `p`. -/
def kInt (ψ : ℝ → ℝ → ℂ) (p : ℤ × ℤ) : ℂ :=
  ∫ x₁ : ℝ, ∫ x₂ : ℝ, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂

/-! ### Elementary integral manipulations -/

lemma integral_congr' {f g : ℝ → ℂ} (h : ∀ x, f x = g x) : ∫ x, f x = ∫ x, g x :=
  integral_congr_ae (Filter.Eventually.of_forall h)

lemma integral_eq_setIntegral_of_support {g : ℝ → ℂ} {a b : ℝ}
    (h : ∀ x, x ∉ Set.Icc a b → g x = 0) :
    ∫ x, g x = ∫ x in Set.Icc a b, g x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero h).symm

lemma integral_integral_eq_setIntegral_of_support {g : ℝ → ℝ → ℂ} {a b c d : ℝ}
    (h₁ : ∀ x₁, x₁ ∉ Set.Icc a b → ∀ x₂, g x₁ x₂ = 0)
    (h₂ : ∀ x₁ x₂, x₂ ∉ Set.Icc c d → g x₁ x₂ = 0) :
    ∫ x₁, ∫ x₂, g x₁ x₂ = ∫ x₁ in Set.Icc a b, ∫ x₂ in Set.Icc c d, g x₁ x₂ := by
  have h1 : (∫ x₁, ∫ x₂, g x₁ x₂) = ∫ x₁, ∫ x₂ in Set.Icc c d, g x₁ x₂ :=
    integral_congr' (fun x₁ => integral_eq_setIntegral_of_support (fun x₂ hx₂ => h₂ x₁ x₂ hx₂))
  rw [h1]
  exact integral_eq_setIntegral_of_support (fun x₁ hx₁ => by
    have hz : (fun x₂ => g x₁ x₂) = fun _ => 0 := funext (fun x₂ => h₁ x₁ hx₁ x₂)
    rw [hz]; simp)

lemma norm_setIntegral_Icc_le {g : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ C) :
    ‖∫ x in Set.Icc a b, g x‖ ≤ C * (b - a) := by
  have hfin : volume (Set.Icc a b) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h1 : ‖∫ x in Set.Icc a b, g x ∂volume‖ ≤ C * volume.real (Set.Icc a b) :=
    norm_setIntegral_le_of_norm_le_const hfin h
  rwa [show volume.real (Set.Icc a b) = b - a by
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]] at h1

lemma norm_setIntegral_Icc_Icc_le {g : ℝ → ℝ → ℂ} {a b c d C : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ‖g x y‖ ≤ C) :
    ‖∫ x in Set.Icc a b, ∫ y in Set.Icc c d, g x y‖ ≤ (C * (d - c)) * (b - a) := by
  refine norm_setIntegral_Icc_le hab (fun x hx => ?_)
  exact norm_setIntegral_Icc_le hcd (fun y hy => h x hx y hy)

/-! ### Support and integrability of iterated derivatives -/

lemma iteratedDeriv_eq_zero_of_forall_ne {f : ℝ → ℂ} {x w : ℝ} (n : ℕ)
    (h : ∀ y, w < |y| → f y = 0) (hx : w < |x|) : iteratedDeriv n f x = 0 := by
  have h1 : Function.support f ⊆ Set.Icc (-w) w := by
    intro y hy
    exact Set.mem_Icc.mpr (abs_le.mp (le_of_not_gt (fun hgt => hy (h y hgt))))
  have h2 : x ∉ Set.Icc (-w) w := fun hx' => absurd (abs_le.mpr hx') (not_le.mpr hx)
  have h3 : x ∉ tsupport f := fun hmem => h2 (closure_minimal h1 isClosed_Icc hmem)
  exact Function.notMem_support.mp
    (fun hmem => h3 (support_iteratedDeriv_subset_tsupport f n hmem))

lemma iteratedDeriv_eq_zero_of_forall_eq_zero {f : ℝ → ℂ} (n : ℕ) (h : ∀ z, f z = 0) (x : ℝ) :
    iteratedDeriv n f x = 0 := by
  have hz : f = fun _ => (0 : ℂ) := funext h
  rw [hz]
  simp

lemma integrable_derivs_of_hasCompactSupport {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    Integrable f ∧ Integrable (deriv f) ∧ Integrable (fun x => iteratedDeriv 2 f x) := by
  have h2eq : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  refine ⟨hf.continuous.integrable_of_hasCompactSupport hc, ?_, ?_⟩
  · have hcs : HasCompactSupport (iteratedDeriv 1 f) := by
      rw [iteratedDeriv_one]; exact hc.deriv
    have h1 : Integrable (iteratedDeriv 1 f) :=
      (hf.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport hcs
    simpa only [iteratedDeriv_one] using h1
  · have hcs : HasCompactSupport (iteratedDeriv 2 f) := by rw [h2eq]; exact hc.deriv.deriv
    exact (hf.continuous_iteratedDeriv 2 (by norm_num)).integrable_of_hasCompactSupport hcs

/-- The Fourier decay identity in the vocabulary of this file. -/
lemma fourier_decay_identity' (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f) (h1 : Integrable (deriv f))
    (h2 : Integrable (fun x : ℝ => iteratedDeriv 2 f x)) (ξ : ℝ) :
    kc ξ * (∫ x, f x * kE ξ x) = -(∫ x, iteratedDeriv 2 f x * kE ξ x) := by
  have h := fourier_decay_identity f hf h0 h1 h2 ξ
  simpa [kc, kE] using h

/-- The function `(x₁,x₂) ↦ ∂₁²ψ(x₁,x₂)` is `C²` when `ψ` is `C⁴`. -/
lemma contDiff_secD2 {Ψ : ℝ × ℝ → ℂ} (h : ContDiff ℝ 4 Ψ) :
    ContDiff ℝ 2 fun p : ℝ × ℝ => iteratedDeriv 2 (fun y : ℝ => Ψ (y, p.2)) p.1 := by
  have hΨ : Differentiable ℝ Ψ := h.differentiable (by norm_num)
  let Φ : ℝ × ℝ → ℂ := fun p => fderiv ℝ Ψ p (1, 0)
  have hΦcd : ContDiff ℝ 3 Φ := contDiff_secD (n := 3) h
  have hΦd : Differentiable ℝ Φ := hΦcd.differentiable (by norm_num)
  have hsec : ContDiff ℝ 2 (fun p : ℝ × ℝ => fderiv ℝ Φ p (1, 0)) :=
    contDiff_secD (n := 2) hΦcd
  have hfun : (fun p : ℝ × ℝ => iteratedDeriv 2 (fun y : ℝ => Ψ (y, p.2)) p.1)
      = fun p : ℝ × ℝ => fderiv ℝ Φ p (1, 0) := by
    funext p
    obtain ⟨x₁, x₂⟩ := p
    have h1 : deriv (fun y : ℝ => Ψ (y, x₂)) = fun y => Φ (y, x₂) :=
      deriv_section_eq Ψ hΨ x₂
    have h3 : deriv (fun y : ℝ => Φ (y, x₂)) = fun y => fderiv ℝ Φ (y, x₂) (1, 0) :=
      deriv_section_eq Φ hΦd x₂
    rw [show iteratedDeriv 2 (fun y : ℝ => Ψ (y, x₂))
        = deriv (deriv (fun y : ℝ => Ψ (y, x₂))) from by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one],
      h1, h3]
  rw [hfun]
  exact hsec

/-! ### Summability and the bound for the one-dimensional weights -/

lemma min_inv_sq_le_two_div (x : ℝ) (hx : x ≠ 0) : min 1 (1 / x ^ 2) ≤ 2 / (1 + x ^ 2) := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  rcases le_or_gt (x ^ 2) 1 with h | h
  · have h1 : (1 : ℝ) ≤ 2 / (1 + x ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact le_trans (min_le_left _ _) h1
  · have h1 : 1 / x ^ 2 ≤ 2 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ hx2 (by positivity)]; nlinarith
    exact le_trans (min_le_right _ _) h1

lemma summable_kM (w : ℝ) (hw : 0 < w) : Summable (fun p : ℤ => kM w p) := by
  have hs : 0 < 2 * Real.pi * w := by positivity
  obtain ⟨hS, -⟩ := tsum_one_div_one_add_sq_mul_le (2 * Real.pi * w) hs 0
  have hS' : Summable (fun p : ℤ => 1 / (1 + (2 * Real.pi * w * (p : ℝ)) ^ 2)) := by
    simpa using hS
  refine Summable.of_nonneg_of_le (fun p => kM_nonneg w p) (fun p => ?_) (hS'.mul_left 2)
  by_cases hp : p = 0
  · subst hp
    simp [kM, kA]
  · rw [kM, kA, if_neg hp]
    have hx : 2 * Real.pi * w * (p : ℝ) ≠ 0 :=
      mul_ne_zero (ne_of_gt hs) (by exact_mod_cast hp)
    have hh : min 1 (1 / (2 * Real.pi * w * (p : ℝ)) ^ 2) ≤
        2 / (1 + (2 * Real.pi * w * (p : ℝ)) ^ 2) := min_inv_sq_le_two_div _ hx
    rw [mul_one_div]
    exact hh

lemma tsum_kM_le (w : ℝ) (hw : 0 < w) : (∑' p : ℤ, kM w p) ≤ 3 + 1 / w := by
  rw [show (∑' p : ℤ, kM w p) = ∑' p : ℤ,
      (if p = 0 then 1 else min 1 (1 / (2 * Real.pi * w * (p : ℝ)) ^ 2)) from
    tsum_congr (fun p => kM_eq w p)]
  exact tsum_int_min_inv_sq_le w hw

/-! ### One-dimensional integration by parts for the sections of the symbol -/

lemma section_ibp₁ (g : ℝ → ℝ → ℂ) (hCd : ∀ x₂, ContDiff ℝ 2 (fun y : ℝ => g y x₂))
    (hCs : ∀ x₂, HasCompactSupport (fun y : ℝ => g y x₂)) (ξ : ℝ) (hξ : ξ ≠ 0) (x₂ : ℝ) :
    (∫ x₁, g x₁ x₂ * kE ξ x₁) =
      -(kc ξ)⁻¹ * (∫ x₁, iteratedDeriv 2 (fun y => g y x₂) x₁ * kE ξ x₁) := by
  obtain ⟨hi0, hi1, hi2⟩ := integrable_derivs_of_hasCompactSupport (hCd x₂) (hCs x₂)
  have hid := fourier_decay_identity' (fun y : ℝ => g y x₂) (hCd x₂) hi0 hi1 hi2 ξ
  have hcne : kc ξ ≠ 0 := kc_ne_zero hξ
  calc (∫ x₁, g x₁ x₂ * kE ξ x₁)
      = (kc ξ)⁻¹ * (kc ξ * (∫ x₁, g x₁ x₂ * kE ξ x₁)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    _ = (kc ξ)⁻¹ * (-(∫ x₁, iteratedDeriv 2 (fun y => g y x₂) x₁ * kE ξ x₁)) := by rw [hid]
    _ = -(kc ξ)⁻¹ * (∫ x₁, iteratedDeriv 2 (fun y => g y x₂) x₁ * kE ξ x₁) := by ring

lemma section_ibp₂ (g : ℝ → ℝ → ℂ) (hCd : ∀ x₁, ContDiff ℝ 2 (fun y : ℝ => g x₁ y))
    (hCs : ∀ x₁, HasCompactSupport (fun y : ℝ => g x₁ y)) (ξ : ℝ) (hξ : ξ ≠ 0) (x₁ : ℝ) :
    (∫ x₂, g x₁ x₂ * kE ξ x₂) =
      -(kc ξ)⁻¹ * (∫ x₂, iteratedDeriv 2 (fun y => g x₁ y) x₂ * kE ξ x₂) := by
  obtain ⟨hi0, hi1, hi2⟩ := integrable_derivs_of_hasCompactSupport (hCd x₁) (hCs x₁)
  have hid := fourier_decay_identity' (fun y : ℝ => g x₁ y) (hCd x₁) hi0 hi1 hi2 ξ
  have hcne : kc ξ ≠ 0 := kc_ne_zero hξ
  calc (∫ x₂, g x₁ x₂ * kE ξ x₂)
      = (kc ξ)⁻¹ * (kc ξ * (∫ x₂, g x₁ x₂ * kE ξ x₂)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    _ = (kc ξ)⁻¹ * (-(∫ x₂, iteratedDeriv 2 (fun y => g x₁ y) x₂ * kE ξ x₂)) := by rw [hid]
    _ = -(kc ξ)⁻¹ * (∫ x₂, iteratedDeriv 2 (fun y => g x₁ y) x₂ * kE ξ x₂) := by ring

/-! ### Elementary consequences of the support hypothesis -/

lemma lt_abs_of_not_mem_Icc {w x : ℝ} (hw : 0 < w) (hx : x ∉ Set.Icc (-w) w) : w < |x| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma not_mem_Icc_of_lt_abs {w x : ℝ} (h : w < |x|) : x ∉ Set.Icc (-w) w :=
  fun hx => absurd (abs_le.mpr hx) (not_le.mpr h)

lemma ψ_eq_zero₁ (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₁ : 0 < w₁)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₁ ∉ Set.Icc (-w₁) w₁) : ψ x₁ x₂ = 0 := by
  by_contra hne
  exact absurd (hsupp x₁ x₂ hne).1 (not_le.mpr (lt_abs_of_not_mem_Icc hw₁ hx))

lemma ψ_eq_zero₂ (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₂ ∉ Set.Icc (-w₂) w₂) : ψ x₁ x₂ = 0 := by
  by_contra hne
  exact absurd (hsupp x₁ x₂ hne).2 (not_le.mpr (lt_abs_of_not_mem_Icc hw₂ hx))

lemma d1_eq_zero (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₁ : 0 < w₁)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₁ ∉ Set.Icc (-w₁) w₁) :
    iteratedDeriv 2 (fun y => ψ y x₂) x₁ = 0 :=
  iteratedDeriv_eq_zero_of_forall_ne 2
    (fun y hy => ψ_eq_zero₁ ψ w₁ w₂ hw₁ hsupp (not_mem_Icc_of_lt_abs hy))
    (lt_abs_of_not_mem_Icc hw₁ hx)

lemma d2_eq_zero (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₂ ∉ Set.Icc (-w₂) w₂) :
    iteratedDeriv 2 (fun y => ψ y x₂) x₁ = 0 :=
  iteratedDeriv_eq_zero_of_forall_eq_zero 2
    (fun z => ψ_eq_zero₂ ψ w₁ w₂ hw₂ hsupp hx) x₁

lemma e1_eq_zero (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₁ : 0 < w₁)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₁ ∉ Set.Icc (-w₁) w₁) :
    iteratedDeriv 2 (fun y => ψ x₁ y) x₂ = 0 :=
  iteratedDeriv_eq_zero_of_forall_eq_zero 2
    (fun z => ψ_eq_zero₁ ψ w₁ w₂ hw₁ hsupp hx) x₂

lemma e2_eq_zero (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₂ ∉ Set.Icc (-w₂) w₂) :
    iteratedDeriv 2 (fun y => ψ x₁ y) x₂ = 0 :=
  iteratedDeriv_eq_zero_of_forall_ne 2
    (fun y hy => ψ_eq_zero₂ ψ w₁ w₂ hw₂ hsupp (not_mem_Icc_of_lt_abs hy))
    (lt_abs_of_not_mem_Icc hw₂ hx)

lemma m1_eq_zero (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₁ : 0 < w₁)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₁ ∉ Set.Icc (-w₁) w₁) :
    iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ = 0 :=
  iteratedDeriv_eq_zero_of_forall_eq_zero 2
    (fun y => d1_eq_zero ψ w₁ w₂ hw₁ hsupp hx) x₂

lemma m2_eq_zero (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    {x₁ x₂ : ℝ} (hx : x₂ ∉ Set.Icc (-w₂) w₂) :
    iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ = 0 :=
  iteratedDeriv_eq_zero_of_forall_ne 2
    (fun y hy => d2_eq_zero ψ w₁ w₂ hw₂ hsupp (not_mem_Icc_of_lt_abs hy))
    (lt_abs_of_not_mem_Icc hw₂ hx)

/-! ### Regularity and support of the sections -/

lemma section_contDiff₁ (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    (x₂ : ℝ) : ContDiff ℝ 2 (fun y : ℝ => ψ y x₂) :=
  (hcd.comp (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)

lemma section_contDiff₂ (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    (x₁ : ℝ) : ContDiff ℝ 2 (fun y : ℝ => ψ x₁ y) :=
  (hcd.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)

lemma section_cs₁ (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) (x₂ : ℝ) :
    HasCompactSupport (fun y : ℝ => ψ y x₂) := by
  have hsub : Function.support (fun y : ℝ => ψ y x₂) ⊆ Set.Icc (-w₁) w₁ :=
    fun y hy => Set.mem_Icc.mpr (abs_le.mp (hsupp y x₂ hy).1)
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-w₁) w₁)) hsub

lemma section_cs₂ (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) (x₁ : ℝ) :
    HasCompactSupport (fun y : ℝ => ψ x₁ y) := by
  have hsub : Function.support (fun y : ℝ => ψ x₁ y) ⊆ Set.Icc (-w₂) w₂ :=
    fun y hy => Set.mem_Icc.mpr (abs_le.mp (hsupp x₁ y hy).2)
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-w₂) w₂)) hsub

lemma dPhi_contDiff (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    (x₁ : ℝ) : ContDiff ℝ 2 (fun y : ℝ => iteratedDeriv 2 (fun z => ψ z y) x₁) :=
  ((contDiff_secD2 hcd).comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)

lemma dPhi_cs (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) (x₁ : ℝ) :
    HasCompactSupport (fun y : ℝ => iteratedDeriv 2 (fun z => ψ z y) x₁) := by
  have hsub : Function.support (fun y : ℝ => iteratedDeriv 2 (fun z => ψ z y) x₁) ⊆
      Set.Icc (-w₂) w₂ := by
    intro y hy
    by_contra hx
    exact hy (d2_eq_zero ψ w₁ w₂ hw₂ hsupp (x₁ := x₁) (x₂ := y) hx)
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-w₂) w₂)) hsub

lemma uncurry_cont (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    (c₁ c₂ : ℝ) :
    Continuous (Function.uncurry (fun x₁ x₂ : ℝ => ψ x₁ x₂ * kE c₁ x₁ * kE c₂ x₂)) := by
  show Continuous (fun q : ℝ × ℝ => ψ q.1 q.2 * kE c₁ q.1 * kE c₂ q.2)
  exact (hcd.continuous.mul ((continuous_kE c₁).comp continuous_fst)).mul
    ((continuous_kE c₂).comp continuous_snd)

lemma uncurry_cs (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (c₁ c₂ : ℝ)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) :
    HasCompactSupport (Function.uncurry (fun x₁ x₂ : ℝ => ψ x₁ x₂ * kE c₁ x₁ * kE c₂ x₂)) := by
  have hsub : Function.support (Function.uncurry (fun x₁ x₂ : ℝ =>
      ψ x₁ x₂ * kE c₁ x₁ * kE c₂ x₂)) ⊆ Set.Icc (-w₁) w₁ ×ˢ Set.Icc (-w₂) w₂ := by
    intro q hq
    have hψq : ψ q.1 q.2 ≠ 0 := by
      intro h0
      have hz : ψ q.1 q.2 * kE c₁ q.1 * kE c₂ q.2 = 0 := by
        rw [h0]; ring
      exact hq (show (Function.uncurry
        (fun x₁ x₂ : ℝ => ψ x₁ x₂ * kE c₁ x₁ * kE c₂ x₂)) q = 0 from hz)
    obtain ⟨ha, hb⟩ := hsupp q.1 q.2 hψq
    exact ⟨Set.mem_Icc.mpr (abs_le.mp ha), Set.mem_Icc.mpr (abs_le.mp hb)⟩
  exact HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Set.Icc (-w₁) w₁ ×ˢ Set.Icc (-w₂) w₂)) hsub

lemma uncurryH_cont (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    (c₁ c₂ : ℝ) :
    Continuous (Function.uncurry
      (fun x₁ x₂ : ℝ => iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE c₁ x₁ * kE c₂ x₂)) := by
  show Continuous (fun q : ℝ × ℝ =>
    iteratedDeriv 2 (fun y => ψ y q.2) q.1 * kE c₁ q.1 * kE c₂ q.2)
  exact (((contDiff_secD2 hcd).continuous.mul
    ((continuous_kE c₁).comp continuous_fst))).mul ((continuous_kE c₂).comp continuous_snd)

lemma uncurryH_cs (ψ : ℝ → ℝ → ℂ) (w₁ w₂ : ℝ) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (c₁ c₂ : ℝ)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) :
    HasCompactSupport (Function.uncurry
      (fun x₁ x₂ : ℝ => iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE c₁ x₁ * kE c₂ x₂)) := by
  have hsub : Function.support (Function.uncurry (fun x₁ x₂ : ℝ =>
      iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE c₁ x₁ * kE c₂ x₂)) ⊆
      Set.Icc (-w₁) w₁ ×ˢ Set.Icc (-w₂) w₂ := by
    intro q hq
    have hq' : iteratedDeriv 2 (fun y => ψ y q.2) q.1 ≠ 0 := by
      intro h0
      have hz : iteratedDeriv 2 (fun y => ψ y q.2) q.1 * kE c₁ q.1 * kE c₂ q.2 = 0 := by
        rw [h0]; ring
      exact hq (show (Function.uncurry (fun x₁ x₂ : ℝ =>
        iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE c₁ x₁ * kE c₂ x₂)) q = 0 from hz)
    by_cases h1 : q.1 ∈ Set.Icc (-w₁) w₁
    · refine ⟨h1, ?_⟩
      by_contra h2
      exact hq' (d2_eq_zero ψ w₁ w₂ hw₂ hsupp h2)
    · exact absurd (d1_eq_zero ψ w₁ w₂ hw₁ hsupp h1) hq'
  exact HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Set.Icc (-w₁) w₁ ×ˢ Set.Icc (-w₂) w₂)) hsub

lemma kA_eq_one_of_eq_zero {w : ℝ} {p : ℤ} (h : p = 0) : kA w p = 1 :=
  show (if p = 0 then (1 : ℝ) else 1 / (2 * Real.pi * w * (p : ℝ)) ^ 2) = 1 from if_pos h

lemma kA_eq_of_ne_zero {w : ℝ} {p : ℤ} (h : p ≠ 0) :
    kA w p = 1 / (2 * Real.pi * w * (p : ℝ)) ^ 2 :=
  show (if p = 0 then (1 : ℝ) else 1 / (2 * Real.pi * w * (p : ℝ)) ^ 2) = _ from if_neg h

lemma kM_eq_one_of_one_le {w : ℝ} {p : ℤ} (h : 1 ≤ kA w p) : kM w p = 1 :=
  show min 1 (kA w p) = 1 from min_eq_left h

lemma kM_eq_self_of_le_one {w : ℝ} {p : ℤ} (h : kA w p ≤ 1) : kM w p = kA w p :=
  show min 1 (kA w p) = kA w p from min_eq_right h

/-! ### The four pointwise bounds -/

theorem massF_b1 (ψ : ℝ → ℝ → ℂ) (w₁ w₂ B : ℝ) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B) (p : ℤ × ℤ) :
    ‖kInt ψ p‖ ≤ 4 * w₁ * w₂ * B := by
  have hab1 : -w₁ ≤ w₁ := by linarith
  have hab2 : -w₂ ≤ w₂ := by linarith
  have hψ1 : ∀ x₁ x₂, x₁ ∉ Set.Icc (-w₁) w₁ → ψ x₁ x₂ = 0 :=
    fun x₁ x₂ hx => ψ_eq_zero₁ ψ w₁ w₂ hw₁ hsupp hx
  have hψ2 : ∀ x₁ x₂, x₂ ∉ Set.Icc (-w₂) w₂ → ψ x₁ x₂ = 0 :=
    fun x₁ x₂ hx => ψ_eq_zero₂ ψ w₁ w₂ hw₂ hsupp hx
  have hG : ∀ x₁ x₂, ‖ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖ = ‖ψ x₁ x₂‖ := by
    intro x₁ x₂
    rw [norm_mul, norm_mul, norm_kE, norm_kE, mul_one, mul_one]
  have hconv : kInt ψ p = ∫ x₁ in Set.Icc (-w₁) w₁, ∫ x₂ in Set.Icc (-w₂) w₂,
      ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
    unfold kInt
    exact integral_integral_eq_setIntegral_of_support
      (fun x₁ hx₁ x₂ => by rw [hψ1 x₁ x₂ hx₁, zero_mul, zero_mul])
      (fun x₁ x₂ hx₂ => by rw [hψ2 x₁ x₂ hx₂, zero_mul, zero_mul])
  rw [hconv]
  calc ‖∫ x₁ in Set.Icc (-w₁) w₁, ∫ x₂ in Set.Icc (-w₂) w₂,
        ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
      ≤ (B * (w₂ - -w₂)) * (w₁ - -w₁) := by
        refine norm_setIntegral_Icc_Icc_le hab1 hab2 (fun x₁ _ x₂ _ => ?_)
        rw [hG x₁ x₂]
        exact h00 x₁ x₂
    _ = 4 * w₁ * w₂ * B := by ring

theorem massF_b2 (ψ : ℝ → ℝ → ℂ) (w₁ w₂ B : ℝ)
    (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2)) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2) (p : ℤ × ℤ) :
    ‖kInt ψ p‖ ≤ 4 * w₁ * w₂ * B * kA w₁ p.1 := by
  have hψ1 : ∀ x₁ x₂, x₁ ∉ Set.Icc (-w₁) w₁ → ψ x₁ x₂ = 0 :=
    fun x₁ x₂ hx => ψ_eq_zero₁ ψ w₁ w₂ hw₁ hsupp hx
  have hψ2 : ∀ x₁ x₂, x₂ ∉ Set.Icc (-w₂) w₂ → ψ x₁ x₂ = 0 :=
    fun x₁ x₂ hx => ψ_eq_zero₂ ψ w₁ w₂ hw₂ hsupp hx
  have hH1 : ∀ x₁ x₂, x₁ ∉ Set.Icc (-w₁) w₁ →
      iteratedDeriv 2 (fun y => ψ y x₂) x₁ = 0 :=
    fun x₁ x₂ hx => d1_eq_zero ψ w₁ w₂ hw₁ hsupp hx
  have hH2 : ∀ x₁ x₂, x₂ ∉ Set.Icc (-w₂) w₂ →
      iteratedDeriv 2 (fun y => ψ y x₂) x₁ = 0 :=
    fun x₁ x₂ hx => d2_eq_zero ψ w₁ w₂ hw₂ hsupp hx
  have hCd1 : ∀ x₂, ContDiff ℝ 2 (fun y : ℝ => ψ y x₂) :=
    fun x₂ => section_contDiff₁ ψ hcd x₂
  have hCs1 : ∀ x₂, HasCompactSupport (fun y : ℝ => ψ y x₂) :=
    fun x₂ => section_cs₁ ψ w₁ w₂ hsupp x₂
  have hb1 : ∀ q : ℤ × ℤ, ‖kInt ψ q‖ ≤ 4 * w₁ * w₂ * B :=
    fun q => massF_b1 ψ w₁ w₂ B hw₁ hw₂ hsupp h00 q
  have hab1 : -w₁ ≤ w₁ := by linarith
  have hab2 : -w₂ ≤ w₂ := by linarith
  by_cases hp1 : p.1 = 0
  · rw [kA_eq_one_of_eq_zero hp1, mul_one]
    exact hb1 p
  · have hp1R : ((p.1 : ℝ)) ≠ 0 := fun h => hp1 (by exact_mod_cast h)
    have hkey : kInt ψ p = -(kc (p.1 : ℝ))⁻¹ *
        (∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
          kE (p.2 : ℝ) x₂) := by
      have hcont : Continuous (Function.uncurry (fun x₁ x₂ : ℝ =>
          ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)) :=
        uncurry_cont ψ hcd (p.1 : ℝ) (p.2 : ℝ)
      have hcs : HasCompactSupport (Function.uncurry (fun x₁ x₂ : ℝ =>
          ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)) :=
        uncurry_cs ψ w₁ w₂ (p.1 : ℝ) (p.2 : ℝ) hsupp
      have hfub := MeasureTheory.integral_integral_swap_of_hasCompactSupport (μ := volume) (ν := volume) hcont hcs
      have hpt : ∀ x₂, (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
          -(kc (p.1 : ℝ))⁻¹ * (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
            kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
        intro x₂
        have hA := section_ibp₁ ψ hCd1 hCs1 (p.1 : ℝ) hp1R x₂
        have hpull : (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
            (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁) * kE (p.2 : ℝ) x₂ := by
          have h1 : (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
              ∫ x₁, (fun a : ℝ => ψ a x₂ * kE (p.1 : ℝ) a) x₁ * kE (p.2 : ℝ) x₂ :=
            integral_congr' (fun x₁ => by simp)
          rw [h1, MeasureTheory.integral_mul_const]
        have hpull2 : (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
              kE (p.2 : ℝ) x₂) =
            (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁) *
              kE (p.2 : ℝ) x₂ := by
          have h1 : (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
                kE (p.2 : ℝ) x₂) =
              ∫ x₁, (fun a : ℝ => iteratedDeriv 2 (fun y => ψ y x₂) a * kE (p.1 : ℝ) a) x₁ *
                kE (p.2 : ℝ) x₂ :=
            integral_congr' (fun x₁ => by simp)
          rw [h1, MeasureTheory.integral_mul_const]
        rw [hpull, hpull2, hA]
        ring
      calc kInt ψ p = ∫ x₂, ∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
            unfold kInt; exact hfub
        _ = ∫ x₂, -(kc (p.1 : ℝ))⁻¹ * (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := integral_congr' (fun x₂ => hpt x₂)
        _ = -(kc (p.1 : ℝ))⁻¹ * ∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
            rw [MeasureTheory.integral_const_mul]
    rw [hkey, norm_mul, norm_neg]
    have hJ : ‖∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
        kE (p.2 : ℝ) x₂‖ ≤ 4 * w₁ * w₂ * (B / w₁ ^ 2) := by
      have hconv : (∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
            kE (p.2 : ℝ) x₂) =
          ∫ x₂ in Set.Icc (-w₂) w₂, ∫ x₁ in Set.Icc (-w₁) w₁,
            iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
        refine integral_integral_eq_setIntegral_of_support ?_ ?_
        · intro x₂ hx₂ x₁
          rw [hH2 x₁ x₂ hx₂, zero_mul, zero_mul]
        · intro x₂ x₁ hx₁
          rw [hH1 x₁ x₂ hx₁, zero_mul, zero_mul]
      rw [hconv]
      calc ‖∫ x₂ in Set.Icc (-w₂) w₂, ∫ x₁ in Set.Icc (-w₁) w₁,
            iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
          ≤ (B / w₁ ^ 2 * (w₁ - -w₁)) * (w₂ - -w₂) := by
            refine norm_setIntegral_Icc_Icc_le hab2 hab1 (fun x₂ _ x₁ _ => ?_)
            rw [norm_mul, norm_mul, norm_kE, norm_kE, mul_one, mul_one]
            exact h20 x₁ x₂
        _ = 4 * w₁ * w₂ * (B / w₁ ^ 2) := by ring
    calc ‖(kc (p.1 : ℝ))⁻¹‖ * ‖∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
          kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
        ≤ ‖(kc (p.1 : ℝ))⁻¹‖ * (4 * w₁ * w₂ * (B / w₁ ^ 2)) :=
          mul_le_mul_of_nonneg_left hJ (norm_nonneg _)
      _ = 4 * w₁ * w₂ * B * kA w₁ p.1 := by
          rw [norm_kc_inv, kA_eq_of_ne_zero hp1]
          field_simp

theorem massF_b3 (ψ : ℝ → ℝ → ℂ) (w₁ w₂ B : ℝ)
    (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2)) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2) (p : ℤ × ℤ) :
    ‖kInt ψ p‖ ≤ 4 * w₁ * w₂ * B * kA w₂ p.2 := by
  have hψ1 : ∀ x₁ x₂, x₁ ∉ Set.Icc (-w₁) w₁ → ψ x₁ x₂ = 0 :=
    fun x₁ x₂ hx => ψ_eq_zero₁ ψ w₁ w₂ hw₁ hsupp hx
  have hψ2 : ∀ x₁ x₂, x₂ ∉ Set.Icc (-w₂) w₂ → ψ x₁ x₂ = 0 :=
    fun x₁ x₂ hx => ψ_eq_zero₂ ψ w₁ w₂ hw₂ hsupp hx
  have hCd2 : ∀ x₁, ContDiff ℝ 2 (fun y : ℝ => ψ x₁ y) :=
    fun x₁ => section_contDiff₂ ψ hcd x₁
  have hCs2 : ∀ x₁, HasCompactSupport (fun y : ℝ => ψ x₁ y) :=
    fun x₁ => section_cs₂ ψ w₁ w₂ hsupp x₁
  have hb1 : ∀ q : ℤ × ℤ, ‖kInt ψ q‖ ≤ 4 * w₁ * w₂ * B :=
    fun q => massF_b1 ψ w₁ w₂ B hw₁ hw₂ hsupp h00 q
  have hab1 : -w₁ ≤ w₁ := by linarith
  have hab2 : -w₂ ≤ w₂ := by linarith
  by_cases hp2 : p.2 = 0
  · rw [kA_eq_one_of_eq_zero hp2, mul_one]
    exact hb1 p
  · have hp2R : ((p.2 : ℝ)) ≠ 0 := fun h => hp2 (by exact_mod_cast h)
    have hkey : kInt ψ p = -(kc (p.2 : ℝ))⁻¹ *
        (∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ *
          kE (p.2 : ℝ) x₂) := by
      have hpt : ∀ x₁, (∫ x₂, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
          -(kc (p.2 : ℝ))⁻¹ * (∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ *
            kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
        intro x₁
        have hA := section_ibp₂ ψ hCd2 hCs2 (p.2 : ℝ) hp2R x₁
        have hpull : (∫ x₂, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
            kE (p.1 : ℝ) x₁ * (∫ x₂, ψ x₁ x₂ * kE (p.2 : ℝ) x₂) := by
          have h1 : (∫ x₂, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
              ∫ x₂, kE (p.1 : ℝ) x₁ * (ψ x₁ x₂ * kE (p.2 : ℝ) x₂) :=
            integral_congr' (fun x₂ => by ring)
          rw [h1, MeasureTheory.integral_const_mul]
        have hpull2 : (∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ *
              kE (p.2 : ℝ) x₂) =
            kE (p.1 : ℝ) x₁ * (∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ *
              kE (p.2 : ℝ) x₂) := by
          have h1 : (∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ *
                kE (p.2 : ℝ) x₂) =
              ∫ x₂, kE (p.1 : ℝ) x₁ * (iteratedDeriv 2 (fun y => ψ x₁ y) x₂ *
                kE (p.2 : ℝ) x₂) :=
            integral_congr' (fun x₂ => by ring)
          rw [h1, MeasureTheory.integral_const_mul]
        rw [hpull, hpull2, hA]
        ring
      calc kInt ψ p = ∫ x₁, ∫ x₂, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := rfl
        _ = ∫ x₁, -(kc (p.2 : ℝ))⁻¹ * (∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := integral_congr' (fun x₁ => hpt x₁)
        _ = -(kc (p.2 : ℝ))⁻¹ * ∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
            rw [MeasureTheory.integral_const_mul]
    rw [hkey, norm_mul, norm_neg]
    have hJ : ‖∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ *
        kE (p.2 : ℝ) x₂‖ ≤ 4 * w₁ * w₂ * (B / w₂ ^ 2) := by
      have hconv : (∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ *
            kE (p.2 : ℝ) x₂) =
          ∫ x₁ in Set.Icc (-w₁) w₁, ∫ x₂ in Set.Icc (-w₂) w₂,
            iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
        refine integral_integral_eq_setIntegral_of_support ?_ ?_
        · intro x₁ hx₁ x₂
          rw [e1_eq_zero ψ w₁ w₂ hw₁ hsupp hx₁, zero_mul, zero_mul]
        · intro x₁ x₂ hx₂
          rw [e2_eq_zero ψ w₁ w₂ hw₂ hsupp hx₂, zero_mul, zero_mul]
      rw [hconv]
      calc ‖∫ x₁ in Set.Icc (-w₁) w₁, ∫ x₂ in Set.Icc (-w₂) w₂,
            iteratedDeriv 2 (fun y => ψ x₁ y) x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
          ≤ (B / w₂ ^ 2 * (w₂ - -w₂)) * (w₁ - -w₁) := by
            refine norm_setIntegral_Icc_Icc_le hab1 hab2 (fun x₁ _ x₂ _ => ?_)
            rw [norm_mul, norm_mul, norm_kE, norm_kE, mul_one, mul_one]
            exact h02 x₁ x₂
        _ = 4 * w₁ * w₂ * (B / w₂ ^ 2) := by ring
    calc ‖(kc (p.2 : ℝ))⁻¹‖ * ‖∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ x₁ y) x₂ *
          kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
        ≤ ‖(kc (p.2 : ℝ))⁻¹‖ * (4 * w₁ * w₂ * (B / w₂ ^ 2)) :=
          mul_le_mul_of_nonneg_left hJ (norm_nonneg _)
      _ = 4 * w₁ * w₂ * B * kA w₂ p.2 := by
          rw [norm_kc_inv, kA_eq_of_ne_zero hp2]
          field_simp

theorem massF_b4 (ψ : ℝ → ℝ → ℂ) (w₁ w₂ B : ℝ)
    (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2)) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂‖
        ≤ B / (w₁ ^ 2 * w₂ ^ 2)) (p : ℤ × ℤ) :
    ‖kInt ψ p‖ ≤ 4 * w₁ * w₂ * B * (kA w₁ p.1 * kA w₂ p.2) := by
  have hM1 : ∀ x₁ x₂, x₁ ∉ Set.Icc (-w₁) w₁ →
      iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ = 0 :=
    fun x₁ x₂ hx => m1_eq_zero ψ w₁ w₂ hw₁ hsupp hx
  have hM2 : ∀ x₁ x₂, x₂ ∉ Set.Icc (-w₂) w₂ →
      iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ = 0 :=
    fun x₁ x₂ hx => m2_eq_zero ψ w₁ w₂ hw₂ hsupp hx
  have hH1 : ∀ x₁ x₂, x₁ ∉ Set.Icc (-w₁) w₁ →
      iteratedDeriv 2 (fun y => ψ y x₂) x₁ = 0 :=
    fun x₁ x₂ hx => d1_eq_zero ψ w₁ w₂ hw₁ hsupp hx
  have hH2 : ∀ x₁ x₂, x₂ ∉ Set.Icc (-w₂) w₂ →
      iteratedDeriv 2 (fun y => ψ y x₂) x₁ = 0 :=
    fun x₁ x₂ hx => d2_eq_zero ψ w₁ w₂ hw₂ hsupp hx
  have hCd1 : ∀ x₂, ContDiff ℝ 2 (fun y : ℝ => ψ y x₂) :=
    fun x₂ => section_contDiff₁ ψ hcd x₂
  have hCs1 : ∀ x₂, HasCompactSupport (fun y : ℝ => ψ y x₂) :=
    fun x₂ => section_cs₁ ψ w₁ w₂ hsupp x₂
  have hCdPhi : ∀ x₁, ContDiff ℝ 2 (fun y : ℝ => iteratedDeriv 2 (fun z => ψ z y) x₁) :=
    fun x₁ => dPhi_contDiff ψ hcd x₁
  have hCsPhi : ∀ x₁,
      HasCompactSupport (fun y : ℝ => iteratedDeriv 2 (fun z => ψ z y) x₁) :=
    fun x₁ => dPhi_cs ψ w₁ w₂ hw₂ hsupp x₁
  have hb2 : ∀ q : ℤ × ℤ, ‖kInt ψ q‖ ≤ 4 * w₁ * w₂ * B * kA w₁ q.1 :=
    fun q => massF_b2 ψ w₁ w₂ B hcd hw₁ hw₂ hsupp h00 h20 q
  have hb3 : ∀ q : ℤ × ℤ, ‖kInt ψ q‖ ≤ 4 * w₁ * w₂ * B * kA w₂ q.2 :=
    fun q => massF_b3 ψ w₁ w₂ B hcd hw₁ hw₂ hsupp h00 h02 q
  by_cases hp1 : p.1 = 0
  · rw [kA_eq_one_of_eq_zero hp1, one_mul]
    exact hb3 p
  by_cases hp2 : p.2 = 0
  · rw [kA_eq_one_of_eq_zero hp2, mul_one]
    exact hb2 p
  have hp1R : ((p.1 : ℝ)) ≠ 0 := fun h => hp1 (by exact_mod_cast h)
  have hp2R : ((p.2 : ℝ)) ≠ 0 := fun h => hp2 (by exact_mod_cast h)
  have hkey : kInt ψ p = (kc (p.1 : ℝ))⁻¹ * (kc (p.2 : ℝ))⁻¹ *
      (∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
        kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
    have hcont : Continuous (Function.uncurry (fun x₁ x₂ : ℝ =>
        ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)) :=
      uncurry_cont ψ hcd (p.1 : ℝ) (p.2 : ℝ)
    have hcs : HasCompactSupport (Function.uncurry (fun x₁ x₂ : ℝ =>
        ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)) :=
      uncurry_cs ψ w₁ w₂ (p.1 : ℝ) (p.2 : ℝ) hsupp
    have hstep1 : kInt ψ p = ∫ x₂, ∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
      unfold kInt
      exact MeasureTheory.integral_integral_swap_of_hasCompactSupport (μ := volume) (ν := volume) hcont hcs
    have hstep2 : (∫ x₂, ∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
        -(kc (p.1 : ℝ))⁻¹ * (∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
          kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
      have hpt : ∀ x₂, (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
          -(kc (p.1 : ℝ))⁻¹ * (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
            kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
        intro x₂
        have hA := section_ibp₁ ψ hCd1 hCs1 (p.1 : ℝ) hp1R x₂
        have hpull : (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
            (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁) * kE (p.2 : ℝ) x₂ := by
          have h1 : (∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
              ∫ x₁, (fun a : ℝ => ψ a x₂ * kE (p.1 : ℝ) a) x₁ * kE (p.2 : ℝ) x₂ :=
            integral_congr' (fun x₁ => by simp)
          rw [h1, MeasureTheory.integral_mul_const]
        have hpull2 : (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
              kE (p.2 : ℝ) x₂) =
            (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁) *
              kE (p.2 : ℝ) x₂ := by
          have h1 : (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
                kE (p.2 : ℝ) x₂) =
              ∫ x₁, (fun a : ℝ => iteratedDeriv 2 (fun y => ψ y x₂) a * kE (p.1 : ℝ) a) x₁ *
                kE (p.2 : ℝ) x₂ :=
            integral_congr' (fun x₁ => by simp)
          rw [h1, MeasureTheory.integral_mul_const]
        rw [hpull, hpull2, hA]
        ring
      calc (∫ x₂, ∫ x₁, ψ x₁ x₂ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)
          = ∫ x₂, -(kc (p.1 : ℝ))⁻¹ * (∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
                kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := integral_congr' (fun x₂ => hpt x₂)
        _ = -(kc (p.1 : ℝ))⁻¹ * ∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
            rw [MeasureTheory.integral_const_mul]
    have hcontH : Continuous (Function.uncurry (fun x₁ x₂ : ℝ =>
        iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)) :=
      uncurryH_cont ψ hcd (p.1 : ℝ) (p.2 : ℝ)
    have hcsH : HasCompactSupport (Function.uncurry (fun x₁ x₂ : ℝ =>
        iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂)) :=
      uncurryH_cs ψ w₁ w₂ hw₁ hw₂ (p.1 : ℝ) (p.2 : ℝ) hsupp
    have hstep3 : (∫ x₂, ∫ x₁, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
          kE (p.2 : ℝ) x₂) =
        ∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
          kE (p.2 : ℝ) x₂ :=
      (MeasureTheory.integral_integral_swap_of_hasCompactSupport (μ := volume) (ν := volume)
        hcontH hcsH).symm
    have hstep4 : (∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
          kE (p.2 : ℝ) x₂) =
        -(kc (p.2 : ℝ))⁻¹ * (∫ x₁, ∫ x₂,
          iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
            kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
      have hpt : ∀ x₁, (∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
            kE (p.2 : ℝ) x₂) =
          -(kc (p.2 : ℝ))⁻¹ * (∫ x₂,
            iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := by
        intro x₁
        have hA := section_ibp₂ (fun a b => iteratedDeriv 2 (fun z => ψ z b) a)
          hCdPhi hCsPhi (p.2 : ℝ) hp2R x₁
        have hpull : (∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
              kE (p.2 : ℝ) x₂) =
            kE (p.1 : ℝ) x₁ * (∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
              kE (p.2 : ℝ) x₂) := by
          have h1 : (∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
                kE (p.2 : ℝ) x₂) =
              ∫ x₂, kE (p.1 : ℝ) x₁ * (iteratedDeriv 2 (fun y => ψ y x₂) x₁ *
                kE (p.2 : ℝ) x₂) :=
            integral_congr' (fun x₂ => by ring)
          rw [h1, MeasureTheory.integral_const_mul]
        have hpull2 : (∫ x₂, iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
              kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
            kE (p.1 : ℝ) x₁ * (∫ x₂,
              iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
                kE (p.2 : ℝ) x₂) := by
          have h1 : (∫ x₂, iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
                kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
              ∫ x₂, kE (p.1 : ℝ) x₁ *
                (iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
                  kE (p.2 : ℝ) x₂) :=
            integral_congr' (fun x₂ => by ring)
          rw [h1, MeasureTheory.integral_const_mul]
        rw [hpull, hpull2, hA]
        ring
      calc (∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => ψ y x₂) x₁ * kE (p.1 : ℝ) x₁ *
            kE (p.2 : ℝ) x₂)
          = ∫ x₁, -(kc (p.2 : ℝ))⁻¹ * (∫ x₂,
              iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
                kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) := integral_congr' (fun x₁ => hpt x₁)
        _ = -(kc (p.2 : ℝ))⁻¹ * ∫ x₁, ∫ x₂,
              iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
                kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
            rw [MeasureTheory.integral_const_mul]
    rw [hstep1, hstep2, hstep3, hstep4]
    ring
  rw [hkey, norm_mul, norm_mul]
  have hJ : ‖∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
      kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖ ≤ 4 * w₁ * w₂ * (B / (w₁ ^ 2 * w₂ ^ 2)) := by
    have hconv : (∫ x₁, ∫ x₂, iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
          kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂) =
        ∫ x₁ in Set.Icc (-w₁) w₁, ∫ x₂ in Set.Icc (-w₂) w₂,
          iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
            kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂ := by
      refine integral_integral_eq_setIntegral_of_support ?_ ?_
      · intro x₁ hx₁ x₂
        rw [hM1 x₁ x₂ hx₁, zero_mul, zero_mul]
      · intro x₁ x₂ hx₂
        rw [hM2 x₁ x₂ hx₂, zero_mul, zero_mul]
    rw [hconv]
    have hab1 : -w₁ ≤ w₁ := by linarith
    have hab2 : -w₂ ≤ w₂ := by linarith
    calc ‖∫ x₁ in Set.Icc (-w₁) w₁, ∫ x₂ in Set.Icc (-w₂) w₂,
          iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
            kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
        ≤ (B / (w₁ ^ 2 * w₂ ^ 2) * (w₂ - -w₂)) * (w₁ - -w₁) := by
          refine norm_setIntegral_Icc_Icc_le hab1 hab2 (fun x₁ _ x₂ _ => ?_)
          rw [norm_mul, norm_mul, norm_kE, norm_kE, mul_one, mul_one]
          exact h22 x₁ x₂
      _ = 4 * w₁ * w₂ * (B / (w₁ ^ 2 * w₂ ^ 2)) := by ring
  calc ‖(kc (p.1 : ℝ))⁻¹‖ * ‖(kc (p.2 : ℝ))⁻¹‖ * ‖∫ x₁, ∫ x₂,
        iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂ *
          kE (p.1 : ℝ) x₁ * kE (p.2 : ℝ) x₂‖
      ≤ ‖(kc (p.1 : ℝ))⁻¹‖ * ‖(kc (p.2 : ℝ))⁻¹‖ *
          (4 * w₁ * w₂ * (B / (w₁ ^ 2 * w₂ ^ 2))) :=
        mul_le_mul_of_nonneg_left hJ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 4 * w₁ * w₂ * B * (kA w₁ p.1 * kA w₂ p.2) := by
        rw [norm_kc_inv, norm_kc_inv, kA_eq_of_ne_zero hp1, kA_eq_of_ne_zero hp2]
        field_simp

theorem massF_bounds (ψ : ℝ → ℝ → ℂ) (w₁ w₂ B : ℝ)
    (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2)) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂‖
        ≤ B / (w₁ ^ 2 * w₂ ^ 2)) (p : ℤ × ℤ) :
    ‖kInt ψ p‖ ≤ 4 * w₁ * w₂ * B * (kM w₁ p.1 * kM w₂ p.2) := by
  have hb1 := massF_b1 ψ w₁ w₂ B hw₁ hw₂ hsupp h00
  have hb2 := massF_b2 ψ w₁ w₂ B hcd hw₁ hw₂ hsupp h00 h20
  have hb3 := massF_b3 ψ w₁ w₂ B hcd hw₁ hw₂ hsupp h00 h02
  have hb4 := massF_b4 ψ w₁ w₂ B hcd hw₁ hw₂ hsupp h00 h20 h02 h22
  by_cases h1 : 1 ≤ kA w₁ p.1
  · by_cases h2 : 1 ≤ kA w₂ p.2
    · have hm : kM w₁ p.1 * kM w₂ p.2 = 1 := by
        rw [kM_eq_one_of_one_le h1, kM_eq_one_of_one_le h2, one_mul]
      rw [hm, mul_one]
      exact hb1 p
    · have h2' : kA w₂ p.2 ≤ 1 := le_of_lt (lt_of_not_ge h2)
      have hm : kM w₁ p.1 * kM w₂ p.2 = kA w₂ p.2 := by
        rw [kM_eq_one_of_one_le h1, kM_eq_self_of_le_one h2', one_mul]
      rw [hm]
      exact hb3 p
  · have h1' : kA w₁ p.1 ≤ 1 := le_of_lt (lt_of_not_ge h1)
    by_cases h2 : 1 ≤ kA w₂ p.2
    · have hm : kM w₁ p.1 * kM w₂ p.2 = kA w₁ p.1 := by
        rw [kM_eq_self_of_le_one h1', kM_eq_one_of_one_le h2, mul_one]
      rw [hm]
      exact hb2 p
    · have h2' : kA w₂ p.2 ≤ 1 := le_of_lt (lt_of_not_ge h2)
      have hm : kM w₁ p.1 * kM w₂ p.2 = kA w₁ p.1 * kA w₂ p.2 := by
        rw [kM_eq_self_of_le_one h1', kM_eq_self_of_le_one h2']
      rw [hm]
      exact hb4 p

theorem massF_summ_and_bound (ψ : ℝ → ℝ → ℂ) (w₁ w₂ B : ℝ)
    (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2)) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hw₁1 : w₁ ≤ 1) (hw₂1 : w₂ ≤ 1) (hB : 0 ≤ B)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂‖
        ≤ B / (w₁ ^ 2 * w₂ ^ 2)) :
    Summable (fun p : ℤ × ℤ => ‖kInt ψ p‖) ∧ (∑' p : ℤ × ℤ, ‖kInt ψ p‖) ≤ 200 * B := by
  have hb : ∀ p : ℤ × ℤ, ‖kInt ψ p‖ ≤ 4 * w₁ * w₂ * B * (kM w₁ p.1 * kM w₂ p.2) :=
    fun p => massF_bounds ψ w₁ w₂ B hcd hw₁ hw₂ hsupp h00 h20 h02 h22 p
  have hsummM1 : Summable (fun p : ℤ => kM w₁ p) := summable_kM w₁ hw₁
  have hsummM2 : Summable (fun p : ℤ => kM w₂ p) := summable_kM w₂ hw₂
  have hsumm2 : Summable (fun p : ℤ × ℤ => kM w₁ p.1 * kM w₂ p.2) :=
    hsummM1.mul_of_nonneg hsummM2 (fun p => kM_nonneg w₁ p) (fun p => kM_nonneg w₂ p)
  have hsummR : Summable (fun p : ℤ × ℤ => 4 * w₁ * w₂ * B * (kM w₁ p.1 * kM w₂ p.2)) :=
    hsumm2.mul_left _
  have hsummL : Summable (fun p : ℤ × ℤ => ‖kInt ψ p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hb hsummR
  refine ⟨hsummL, ?_⟩
  have hA1 := tsum_kM_le w₁ hw₁
  have hA2 := tsum_kM_le w₂ hw₂
  have hnn1 : (0 : ℝ) ≤ ∑' i : ℤ, kM w₁ i := tsum_nonneg (fun i => kM_nonneg w₁ i)
  have hnn2 : (0 : ℝ) ≤ ∑' j : ℤ, kM w₂ j := tsum_nonneg (fun j => kM_nonneg w₂ j)
  have hc0 : (0 : ℝ) ≤ 4 * w₁ * w₂ * B := by positivity
  have hstep1 : (∑' p : ℤ × ℤ, ‖kInt ψ p‖)
      ≤ ∑' p : ℤ × ℤ, 4 * w₁ * w₂ * B * (kM w₁ p.1 * kM w₂ p.2) :=
    Summable.tsum_le_tsum hb hsummL hsummR
  have hstep2 : (∑' p : ℤ × ℤ, 4 * w₁ * w₂ * B * (kM w₁ p.1 * kM w₂ p.2))
      = 4 * w₁ * w₂ * B * ((∑' i : ℤ, kM w₁ i) * (∑' j : ℤ, kM w₂ j)) := by
    rw [tsum_mul_left, Summable.tsum_mul_tsum hsummM1 hsummM2 hsumm2]
  have hstep3 : 4 * w₁ * w₂ * B * ((∑' i : ℤ, kM w₁ i) * (∑' j : ℤ, kM w₂ j))
      ≤ 4 * w₁ * w₂ * B * ((3 + 1 / w₁) * (3 + 1 / w₂)) := by
    refine mul_le_mul_of_nonneg_left ?_ hc0
    exact mul_le_mul hA1 hA2 hnn2 (by positivity)
  have hstep4 : 4 * w₁ * w₂ * B * ((3 + 1 / w₁) * (3 + 1 / w₂))
      = 4 * B * ((3 * w₁ + 1) * (3 * w₂ + 1)) := by
    field_simp
  have hstep5 : 4 * B * ((3 * w₁ + 1) * (3 * w₂ + 1)) ≤ 200 * B := by
    have h7 : (0 : ℝ) ≤ 3 * w₁ + 1 := by linarith
    have h8 : (0 : ℝ) ≤ 3 * w₂ + 1 := by linarith
    have h9 : 3 * w₁ + 1 ≤ 4 := by linarith
    have h10 : 3 * w₂ + 1 ≤ 4 := by linarith
    have h11 : (3 * w₁ + 1) * (3 * w₂ + 1) ≤ 16 := by
      have := mul_le_mul h9 h10 h8 (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    nlinarith [hB, h11, h7, h8]
  linarith [hstep1, hstep2.le, hstep3, hstep4.le, hstep5]

/-! ### The two-dimensional Fourier integral in explicit form -/

lemma kInt_eq_explicit (ψ : ℝ → ℝ → ℂ) (p : ℤ × ℤ) :
    kInt ψ p = ∫ x₁ : ℝ, ∫ x₂ : ℝ, ψ x₁ x₂ * Complex.exp (2 * Real.pi * Complex.I *
        (-(((p.1 : ℝ) * x₁ + (p.2 : ℝ) * x₂) : ℂ))) := by
  unfold kInt
  refine integral_congr' (fun x₁ => integral_congr' (fun x₂ => ?_))
  simp only [kE]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-! ### The real-valued form of the mass bound -/

theorem mass_fourier_le_real (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    {w₁ w₂ B : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₁1 : w₁ ≤ 1) (hw₂1 : w₂ ≤ 1)
    (hB : 0 ≤ B)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂‖
        ≤ B / (w₁ ^ 2 * w₂ ^ 2)) :
    Summable (fun p : ℤ × ℤ => ‖∫ x₁ : ℝ, ∫ x₂ : ℝ,
        ψ x₁ x₂ * Complex.exp (2 * Real.pi * Complex.I *
          (-(((p.1 : ℝ) * x₁ + (p.2 : ℝ) * x₂) : ℂ)))‖) ∧
      (∑' p : ℤ × ℤ, ‖∫ x₁ : ℝ, ∫ x₂ : ℝ,
        ψ x₁ x₂ * Complex.exp (2 * Real.pi * Complex.I *
          (-(((p.1 : ℝ) * x₁ + (p.2 : ℝ) * x₂) : ℂ)))‖) ≤ 200 * B := by
  obtain ⟨hsum, hbound⟩ :=
    massF_summ_and_bound ψ w₁ w₂ B hcd hw₁ hw₂ hw₁1 hw₂1 hB hsupp h00 h20 h02 h22
  have hk : ∀ p : ℤ × ℤ, ‖∫ x₁ : ℝ, ∫ x₂ : ℝ, ψ x₁ x₂ * Complex.exp (2 * Real.pi *
        Complex.I * (-(((p.1 : ℝ) * x₁ + (p.2 : ℝ) * x₂) : ℂ)))‖ = ‖kInt ψ p‖ :=
    fun p => by rw [kInt_eq_explicit]
  exact ⟨by simpa only [hk] using hsum, by rw [tsum_congr hk]; exact hbound⟩

/-! ### The mass bound in `ℝ≥0∞` form -/

theorem mass_fourier_le_ennreal (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    {w₁ w₂ B : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₁1 : w₁ ≤ 1) (hw₂1 : w₂ ≤ 1) (hB : 0 ≤ B)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂‖
        ≤ B / (w₁ ^ 2 * w₂ ^ 2)) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal ‖∫ x₁ : ℝ, ∫ x₂ : ℝ,
        ψ x₁ x₂ * Complex.exp (2 * Real.pi * Complex.I *
          (-(((p.1 : ℝ) * x₁ + (p.2 : ℝ) * x₂) : ℂ)))‖)
      ≤ ENNReal.ofReal (200 * B) := by
  obtain ⟨hsum, hbound⟩ :=
    mass_fourier_le_real ψ hcd hw₁ hw₂ hw₁1 hw₂1 hB hsupp h00 h20 h02 h22
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) hsum]
  exact ENNReal.ofReal_le_ofReal hbound

/-! ### The mass bound -/

theorem mass_fourier_le (ψ : ℝ → ℝ → ℂ) (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => ψ x.1 x.2))
    {w₁ w₂ B : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₁1 : w₁ ≤ 1) (hw₂1 : w₂ ≤ 1) (hB : 0 ≤ B)
    (hsupp : ∀ x₁ x₂, ψ x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂, ‖ψ x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => ψ x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂, ‖iteratedDeriv 2 (fun y => iteratedDeriv 2 (fun z => ψ z y) x₁) x₂‖
        ≤ B / (w₁ ^ 2 * w₂ ^ 2)) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal ‖∫ x₁ : ℝ, ∫ x₂ : ℝ,
        ψ x₁ x₂ * Complex.exp (2 * Real.pi * Complex.I *
          (-(((p.1 : ℝ) * x₁ + (p.2 : ℝ) * x₂) : ℂ)))‖)
      ≤ ENNReal.ofReal (200 * B) :=
  mass_fourier_le_ennreal ψ hcd hw₁ hw₂ hw₁1 hw₂1 hB hsupp h00 h20 h02 h22

end Work.KMTAreas.A7
