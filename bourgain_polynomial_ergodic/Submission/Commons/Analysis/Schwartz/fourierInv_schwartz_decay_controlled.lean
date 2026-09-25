import Mathlib
import Submission.Commons.Analysis.Fourier.fourier_transform_min_decay

set_option linter.unusedVariables false

namespace Commons.Analysis.Schwartz

open _root_.MeasureTheory
open scoped FourierTransform

/-! ### Elementary lemmas -/

/-- `deriv` of the inclusion `ℝ → ℂ` is `1`. -/
lemma deriv_id_complex (z : ℝ) : deriv (fun s : ℝ => (s : ℂ)) z = 1 := by
  rw [show (fun s : ℝ => (s : ℂ)) = ⇑Complex.ofRealCLM from rfl]
  rw [ContinuousLinearMap.deriv]
  rfl

lemma norm_two_pi_I_complex : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  rw [show (2 * Real.pi * Complex.I : ℂ) = (↑(2 * Real.pi) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma norm_two_pi_I_mul (z : ℂ) : ‖(2 * Real.pi * Complex.I : ℂ) * z‖ = 2 * Real.pi * ‖z‖ := by
  rw [norm_mul, norm_two_pi_I_complex]

/-- The trivial bound `‖𝓕 m t‖ ≤ ∫ ‖m‖`. -/
lemma fourier_norm_le_integral (m : ℝ → ℂ) (t : ℝ) :
    ‖FourierTransform.fourier m t‖ ≤ ∫ x, ‖m x‖ := by
  rw [Real.fourier_eq']
  calc ‖∫ v, Complex.exp (↑(-2 * Real.pi * inner ℝ v t) * Complex.I) • m v‖
      ≤ ∫ v, ‖Complex.exp (↑(-2 * Real.pi * inner ℝ v t) * Complex.I) • m v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, ‖m v‖ := by
        apply integral_congr_ae; filter_upwards with v
        rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- If `m` and its second derivative are integrable with `L¹` bounds `A`, `B`, then
`‖𝓕 m t‖ ≤ (2A + 2B + 1)/(1 + t²)` for every `t`. -/
lemma fourier_decay_of_L1 (m : ℝ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hint0 : Integrable m) (hint2 : Integrable (deriv (deriv m)))
    (hdiff1 : Differentiable ℝ m) (hdiff2 : Differentiable ℝ (deriv m))
    (h0 : ∫ x, ‖m x‖ ≤ A) (h2 : ∫ x, ‖deriv (deriv m) x‖ ≤ B) (t : ℝ) :
    ‖FourierTransform.fourier m t‖ ≤ (2 * A + 2 * B + 1) / (1 + t ^ 2) := by
  rcases eq_or_ne t 0 with rfl | ht
  · have h : ‖FourierTransform.fourier m 0‖ ≤ 2 * A + 2 * B + 1 :=
      (fourier_norm_le_integral m 0).trans (h0.trans (by linarith))
    simpa using h
  · have hmin := Commons.Analysis.Fourier.fourier_transform_min_decay m A B hA hB hint0 hint2
      hdiff1 hdiff2 h0 h2 t ht
    have hpos : 0 < 1 + t ^ 2 := by positivity
    by_cases hle : |t| ≤ 1
    · -- small `t`
      have ht2le : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr hle
      have hhalf : (2 : ℝ)⁻¹ ≤ (1 + t ^ 2)⁻¹ :=
        (inv_le_inv₀ (by norm_num) hpos).mpr (by linarith)
      calc ‖FourierTransform.fourier m t‖ ≤ min A (B / (2 * Real.pi * |t|) ^ 2) := hmin
        _ ≤ A := min_le_left _ _
        _ ≤ (2 * A + 2 * B + 1) * (1 + t ^ 2)⁻¹ := by
            have h2' : A ≤ (2 * A + 2 * B + 1) * (2 : ℝ)⁻¹ := by linarith
            exact h2'.trans (mul_le_mul_of_nonneg_left hhalf (by linarith))
        _ = (2 * A + 2 * B + 1) / (1 + t ^ 2) := by rw [div_eq_mul_inv]
    · -- large `t`
      have hle' : 1 < |t| := not_le.mp hle
      have ht2ge : 1 ≤ t ^ 2 := by
        nlinarith [hle', sq_abs t]
      have ht2pos : 0 < t ^ 2 := by nlinarith
      have hC2B : 2 * B ≤ 2 * A + 2 * B + 1 := by linarith
      have hpi1 : 1 ≤ 2 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have hBle : B ≤ 2 * Real.pi ^ 2 * (2 * A + 2 * B + 1) := by
        nlinarith [hB, hC2B, hpi1]
      have hden : (2 * Real.pi * |t|) ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]; ring
      have hprod : B * (1 + t ^ 2) ≤ (2 * A + 2 * B + 1) * (4 * Real.pi ^ 2 * t ^ 2) := by
        have h1 : 1 + t ^ 2 ≤ 2 * t ^ 2 := by linarith
        have h2 : B * (1 + t ^ 2) ≤ B * (2 * t ^ 2) := mul_le_mul_of_nonneg_left h1 hB
        have h3 : B * (2 * t ^ 2) ≤ (2 * Real.pi ^ 2 * (2 * A + 2 * B + 1)) * (2 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hBle (by positivity)
        have h4 : (2 * Real.pi ^ 2 * (2 * A + 2 * B + 1)) * (2 * t ^ 2)
            = (2 * A + 2 * B + 1) * (4 * Real.pi ^ 2 * t ^ 2) := by ring
        linarith
      have hkey : B / (2 * Real.pi * |t|) ^ 2 ≤ (2 * A + 2 * B + 1) / (1 + t ^ 2) := by
        rw [hden, div_le_div_iff₀ (by positivity) hpos]
        exact hprod
      calc ‖FourierTransform.fourier m t‖ ≤ min A (B / (2 * Real.pi * |t|) ^ 2) := hmin
        _ ≤ B / (2 * Real.pi * |t|) ^ 2 := min_le_right _ _
        _ ≤ (2 * A + 2 * B + 1) / (1 + t ^ 2) := hkey

/-! ### `L¹` bounds from support and derivative bounds -/

/-- If `f` vanishes outside `[-C, C]` (with `0 ≤ C`) and is bounded by `M` there, then
`∫ ‖f‖ ≤ M * 2C`. -/
lemma integral_norm_le_of_support (f : ℝ → ℂ) (C M : ℝ) (hC : 0 ≤ C)
    (hint : Integrable f)
    (hsupp : ∀ x, x ∉ Set.Icc (-C) C → f x = 0)
    (hM : ∀ x ∈ Set.Icc (-C) C, ‖f x‖ ≤ M) :
    ∫ x, ‖f x‖ ≤ M * (2 * C) := by
  have h1 : ∫ x, ‖f x‖ = ∫ x in Set.Icc (-C) C, ‖f x‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hsupp x hx, norm_zero])).symm
  rw [h1]
  calc ∫ x in Set.Icc (-C) C, ‖f x‖ ≤ ∫ x in Set.Icc (-C) C, M := by
        apply setIntegral_mono_on
        · exact hint.norm.integrableOn
        · exact integrableOn_const (isCompact_Icc.measure_lt_top).ne (by simp)
        · exact measurableSet_Icc
        · exact hM
    _ = M * (2 * C) := by
        rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (by linarith)]
        ring

/-! ### Converting `iteratedFDeriv` bounds into `deriv` bounds -/

lemma norm_le_of_iteratedFDeriv_zero (f : ℝ → ℂ) (C : ℝ)
    (h : ∀ ξ, ‖iteratedFDeriv ℝ 0 f ξ‖ ≤ C) (y : ℝ) : ‖f y‖ ≤ C := by
  have h0 : ‖iteratedFDeriv ℝ 0 f y‖ = ‖f y‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero]
  rw [← h0]; exact h y

lemma norm_deriv_le_of_iteratedFDeriv_one (f : ℝ → ℂ) (C : ℝ)
    (h : ∀ ξ, ‖iteratedFDeriv ℝ 1 f ξ‖ ≤ C) (y : ℝ) : ‖deriv f y‖ ≤ C := by
  rw [← iteratedDeriv_one (f := f), ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact h y

lemma norm_deriv_deriv_le_of_iteratedFDeriv_two (f : ℝ → ℂ) (C : ℝ)
    (h : ∀ ξ, ‖iteratedFDeriv ℝ 2 f ξ‖ ≤ C) (y : ℝ) : ‖deriv (deriv f) y‖ ≤ C := by
  have heq : deriv (deriv f) = iteratedDeriv 2 f := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact h y

/-! ### The derivative of the inverse Fourier transform -/

/-- The Schwartz function `ξ ↦ 2πi ξ ψ ξ`. -/
noncomputable def psiDerivMap (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (2 * Real.pi * Complex.I) •
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x 1)) ψ

lemma psiDerivMap_apply (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    psiDerivMap ψ x = (2 * Real.pi * Complex.I) * ((x : ℂ) * ψ x) := by
  rw [psiDerivMap]
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply]
  · rw [Real.inner_apply, mul_one, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rfl
  · exact ((innerSL ℝ).flip 1).hasTemperateGrowth

lemma diff_deriv_schwartz (ψ : SchwartzMap ℝ ℂ) (z : ℝ) :
    DifferentiableAt ℝ (fun s => deriv (fun t => (ψ : ℝ → ℂ) t) s) z := by
  have h : deriv (fun s => (ψ : ℝ → ℂ) s) = ⇑(SchwartzMap.derivCLM ℝ ℂ ψ) := by
    funext s; rw [SchwartzMap.derivCLM_apply]
  rw [h]; exact (SchwartzMap.derivCLM ℝ ℂ ψ).differentiableAt

lemma deriv_psiDerivMap (ψ : SchwartzMap ℝ ℂ) (z : ℝ) :
    deriv (fun s => psiDerivMap ψ s) z =
      (2 * Real.pi * Complex.I) * (ψ z + (z : ℂ) * deriv (fun s => (ψ : ℝ → ℂ) s) z) := by
  have hfun : (fun s => psiDerivMap ψ s)
      = fun s : ℝ => (2 * Real.pi * Complex.I) * ((s : ℂ) * (ψ s)) := by
    funext s; exact psiDerivMap_apply ψ s
  rw [hfun]
  rw [deriv_const_mul (c := 2 * Real.pi * Complex.I)
        (d := fun s : ℝ => (s : ℂ) * (ψ : ℝ → ℂ) s) (by fun_prop)]
  congr 1
  rw [show (fun s : ℝ => (s : ℂ) * (ψ : ℝ → ℂ) s)
        = (fun s : ℝ => (s : ℂ)) * (fun s : ℝ => (ψ : ℝ → ℂ) s) from rfl]
  rw [deriv_mul (by fun_prop) ψ.differentiableAt, deriv_id_complex]
  ring

lemma deriv_deriv_psiDerivMap (ψ : SchwartzMap ℝ ℂ) (z : ℝ) :
    deriv (deriv (fun s => psiDerivMap ψ s)) z =
      (2 * Real.pi * Complex.I) *
        (2 * deriv (fun s => (ψ : ℝ → ℂ) s) z
          + (z : ℂ) * deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) z) := by
  have hd1 : deriv (fun s => psiDerivMap ψ s) =
      fun y => (2 * Real.pi * Complex.I) * (ψ y + (y : ℂ) * deriv (fun s => (ψ : ℝ → ℂ) s) y) := by
    funext y; exact deriv_psiDerivMap ψ y
  rw [hd1]
  have hG2 : (fun s : ℝ => (ψ : ℝ → ℂ) s + (s : ℂ) * deriv (fun s => (ψ : ℝ → ℂ) s) s)
      = (fun s : ℝ => (ψ : ℝ → ℂ) s)
        + (fun s : ℝ => (s : ℂ)) * (fun s : ℝ => deriv (fun t => (ψ : ℝ → ℂ) t) s) := rfl
  rw [deriv_const_mul (c := 2 * Real.pi * Complex.I)
        (d := fun s : ℝ => (ψ : ℝ → ℂ) s + (s : ℂ) * deriv (fun s => (ψ : ℝ → ℂ) s) s)
        (ψ.differentiableAt.add
          ((Complex.differentiable_ofReal.differentiableAt).mul (diff_deriv_schwartz ψ z)))]
  congr 1
  rw [hG2,
    deriv_add ψ.differentiableAt
      ((Complex.differentiable_ofReal.differentiableAt).mul (diff_deriv_schwartz ψ z)),
    deriv_mul (Complex.differentiable_ofReal.differentiableAt) (diff_deriv_schwartz ψ z),
    deriv_id_complex]
  ring

lemma derivCLM_two_coe (g : SchwartzMap ℝ ℂ) :
    ⇑(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ g))
      = deriv (deriv (fun s => (g : ℝ → ℂ) s)) := by
  have e1 : ⇑(SchwartzMap.derivCLM ℝ ℂ g) = deriv (fun s => (g : ℝ → ℂ) s) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have e2 : ⇑(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ g))
      = deriv (⇑(SchwartzMap.derivCLM ℝ ℂ g)) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  rw [e2, e1]

lemma integrable_deriv_deriv (g : SchwartzMap ℝ ℂ) :
    Integrable (deriv (deriv (fun s => (g : ℝ → ℂ) s))) := by
  rw [← derivCLM_two_coe]
  exact (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ g)).integrable

lemma differentiable_deriv (g : SchwartzMap ℝ ℂ) :
    Differentiable ℝ (deriv (fun s => (g : ℝ → ℂ) s)) := by
  have e : deriv (fun s => (g : ℝ → ℂ) s) = ⇑(SchwartzMap.derivCLM ℝ ℂ g) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  rw [e]; exact (SchwartzMap.derivCLM ℝ ℂ g).differentiable

/-! ### Support of the iterated derivatives -/

lemma tsupport_derivCLM_two_subset (g : SchwartzMap ℝ ℂ) (S : Set ℝ) (hS : IsClosed S)
    (hg : ∀ x, x ∉ S → g x = 0) :
    tsupport (⇑(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ g))) ⊆ S := by
  have hg' : Function.support (⇑g) ⊆ S := fun x hx => by
    by_contra hxs
    exact (Function.mem_support.mp hx) (hg x hxs)
  have h1 : tsupport (⇑g) ⊆ S := closure_minimal hg' hS
  have e1 : ⇑(SchwartzMap.derivCLM ℝ ℂ g) = deriv (⇑g) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  have e2 : ⇑(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ g))
      = deriv (⇑(SchwartzMap.derivCLM ℝ ℂ g)) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  rw [e2, e1]
  exact (tsupport_deriv_subset (f := deriv (⇑g))).trans
    ((tsupport_deriv_subset (f := ⇑g)).trans h1)

lemma derivCLM_two_eq_zero_of_not_mem (g : SchwartzMap ℝ ℂ) (S : Set ℝ) (hS : IsClosed S)
    (hg : ∀ x, x ∉ S → g x = 0) {x : ℝ} (hx : x ∉ S) :
    deriv (deriv (fun s => g s)) x = 0 := by
  have ht := tsupport_derivCLM_two_subset g S hS hg
  rw [← derivCLM_two_coe g]
  exact Function.notMem_support.mp
    (fun hmem => hx (ht (subset_tsupport _ hmem)))

/-! ### Pointwise bounds -/

lemma norm_psi_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) (x : ℝ) :
    ‖ψ x‖ ≤ C :=
  norm_le_of_iteratedFDeriv_zero _ C (hψj 0 (by norm_num)) x

lemma norm_deriv_psi_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) (x : ℝ) :
    ‖deriv (fun s => (ψ : ℝ → ℂ) s) x‖ ≤ C :=
  norm_deriv_le_of_iteratedFDeriv_one _ C (hψj 1 (by norm_num)) x

lemma norm_deriv_deriv_psi_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) (x : ℝ) :
    ‖deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖ ≤ C :=
  norm_deriv_deriv_le_of_iteratedFDeriv_two _ C (hψj 2 (by norm_num)) x

lemma psiDerivMap_supp (ψ : SchwartzMap ℝ ℂ) {C : ℝ}
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0) (x : ℝ) (hx : x ∉ Set.Icc (-C) C) :
    psiDerivMap ψ x = 0 := by
  rw [psiDerivMap_apply, hψsupp x hx, mul_zero, mul_zero]

lemma psiDerivMap_norm_le (ψ : SchwartzMap ℝ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-C) C) :
    ‖psiDerivMap ψ x‖ ≤ 2 * Real.pi * C ^ 2 := by
  rw [psiDerivMap_apply, norm_two_pi_I_mul, norm_mul, norm_ofReal_complex]
  have hxabs : |x| ≤ C := abs_le.mpr ⟨hx.1, hx.2⟩
  have hpsi : ‖ψ x‖ ≤ C := norm_psi_le ψ C hψj x
  have h3 : |x| * ‖ψ x‖ ≤ C * C := mul_le_mul hxabs hpsi (norm_nonneg _) hC
  calc 2 * Real.pi * (|x| * ‖ψ x‖) ≤ 2 * Real.pi * (C * C) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * Real.pi * C ^ 2 := by ring

lemma norm_deriv_deriv_psiDerivMap_le (ψ : SchwartzMap ℝ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-C) C) :
    ‖deriv (deriv (fun s => psiDerivMap ψ s)) x‖ ≤ 2 * Real.pi * (2 * C + C ^ 2) := by
  rw [deriv_deriv_psiDerivMap ψ x, norm_two_pi_I_mul]
  have hxabs : |x| ≤ C := abs_le.mpr ⟨hx.1, hx.2⟩
  have h1 : ‖deriv (fun s => (ψ : ℝ → ℂ) s) x‖ ≤ C := norm_deriv_psi_le ψ C hψj x
  have h2 : ‖deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖ ≤ C := norm_deriv_deriv_psi_le ψ C hψj x
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖2 * deriv (fun s => (ψ : ℝ → ℂ) s) x
        + (x : ℂ) * deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖
      ≤ ‖2 * deriv (fun s => (ψ : ℝ → ℂ) s) x‖
        + ‖(x : ℂ) * deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖ := norm_add_le _ _
    _ = 2 * ‖deriv (fun s => (ψ : ℝ → ℂ) s) x‖
        + |x| * ‖deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖ := by
        rw [norm_mul, norm_mul, Complex.norm_two, norm_ofReal_complex]
    _ ≤ 2 * C + C ^ 2 := by
        have h3 : |x| * ‖deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖ ≤ C * C :=
          mul_le_mul hxabs h2 (norm_nonneg _) hC
        nlinarith [h1, h3, norm_nonneg (deriv (fun s => (ψ : ℝ → ℂ) s) x), hC]

/-! ### Integral bounds -/

lemma integral_norm_psi_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 < C)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∫ x, ‖ψ x‖ ≤ 2 * C ^ 2 := by
  have h := integral_norm_le_of_support (fun x => (ψ : ℝ → ℂ) x) C C hC.le ψ.integrable
    (fun x hx => hψsupp x hx) (fun x hx => norm_psi_le ψ C hψj x)
  calc ∫ x, ‖ψ x‖ = ∫ x, ‖(fun x => (ψ : ℝ → ℂ) x) x‖ := rfl
    _ ≤ C * (2 * C) := h
    _ = 2 * C ^ 2 := by ring

lemma integral_norm_deriv_deriv_psi_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 < C)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∫ x, ‖deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖ ≤ 2 * C ^ 2 := by
  have h := integral_norm_le_of_support (fun x => deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x) C C
    hC.le (integrable_deriv_deriv ψ)
    (fun x hx => derivCLM_two_eq_zero_of_not_mem ψ (Set.Icc (-C) C) isClosed_Icc hψsupp hx)
    (fun x hx => norm_deriv_deriv_psi_le ψ C hψj x)
  calc ∫ x, ‖deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x‖
      = ∫ x, ‖(fun x => deriv (deriv (fun s => (ψ : ℝ → ℂ) s)) x) x‖ := rfl
    _ ≤ C * (2 * C) := h
    _ = 2 * C ^ 2 := by ring

lemma integral_norm_psiDerivMap_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 < C)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∫ x, ‖psiDerivMap ψ x‖ ≤ (2 * Real.pi * C ^ 2) * (2 * C) :=
  integral_norm_le_of_support (fun x => psiDerivMap ψ x) C (2 * Real.pi * C ^ 2) hC.le
    (psiDerivMap ψ).integrable
    (fun x hx => psiDerivMap_supp ψ hψsupp x hx)
    (fun x hx => psiDerivMap_norm_le ψ hC.le hψsupp hψj hx)

lemma integral_norm_deriv_deriv_psiDerivMap_le (ψ : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 < C)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∫ x, ‖deriv (deriv (fun s => psiDerivMap ψ s)) x‖
      ≤ (2 * Real.pi * (2 * C + C ^ 2)) * (2 * C) :=
  integral_norm_le_of_support (fun x => deriv (deriv (fun s => psiDerivMap ψ s)) x) C
    (2 * Real.pi * (2 * C + C ^ 2)) hC.le (integrable_deriv_deriv (psiDerivMap ψ))
    (fun x hx => derivCLM_two_eq_zero_of_not_mem (psiDerivMap ψ) (Set.Icc (-C) C) isClosed_Icc
      (fun y hy => psiDerivMap_supp ψ hψsupp y hy) hx)
    (fun x hx => norm_deriv_deriv_psiDerivMap_le ψ hC.le hψj hx)

/-! ### The main theorem -/

theorem fourierInv_schwartz_decay_controlled (C : ℝ) (hC : 0 < C) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (ψ : SchwartzMap ℝ ℂ) (hψ0 : ψ 0 = 0)
      (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
      (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) (t : ℝ),
      ‖(FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) t‖ ≤ C₁ / (1 + t ^ 2) ∧
      ‖deriv (fun s : ℝ => (FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) s) t‖
        ≤ C₁ / (1 + t ^ 2) := by
  have hKv_nn : (0 : ℝ) ≤ 2 * (2 * C ^ 2) + 2 * (2 * C ^ 2) + 1 := by positivity
  have hKd_nn : (0 : ℝ) ≤ 2 * (2 * Real.pi * C ^ 2 * (2 * C))
      + 2 * (2 * Real.pi * (2 * C + C ^ 2) * (2 * C)) + 1 := by positivity
  refine ⟨(2 * (2 * C ^ 2) + 2 * (2 * C ^ 2) + 1)
      + (2 * (2 * Real.pi * C ^ 2 * (2 * C))
        + 2 * (2 * Real.pi * (2 * C + C ^ 2) * (2 * C)) + 1), by positivity, ?_⟩
  intro ψ hψ0 hψsupp hψj t
  have hC0 : 0 ≤ C := hC.le
  -- value bound
  have hval := fourier_decay_of_L1 (fun x => (ψ : ℝ → ℂ) x) (2 * C ^ 2) (2 * C ^ 2)
    (by positivity) (by positivity) ψ.integrable (integrable_deriv_deriv ψ)
    ψ.differentiable (differentiable_deriv ψ)
    (integral_norm_psi_le ψ C hC hψsupp hψj)
    (integral_norm_deriv_deriv_psi_le ψ C hC hψsupp hψj) (-t)
  rw [show (1 : ℝ) + (-t) ^ 2 = 1 + t ^ 2 by ring] at hval
  -- derivative bound
  have hder := fourier_decay_of_L1 (fun x => psiDerivMap ψ x)
    (2 * Real.pi * C ^ 2 * (2 * C)) (2 * Real.pi * (2 * C + C ^ 2) * (2 * C))
    (by positivity) (by positivity) (psiDerivMap ψ).integrable
    (integrable_deriv_deriv (psiDerivMap ψ)) (psiDerivMap ψ).differentiable
    (differentiable_deriv (psiDerivMap ψ))
    (integral_norm_psiDerivMap_le ψ C hC hψsupp hψj)
    (integral_norm_deriv_deriv_psiDerivMap_le ψ C hC hψsupp hψj) (-t)
  rw [show (1 : ℝ) + (-t) ^ 2 = 1 + t ^ 2 by ring] at hder
  constructor
  · calc ‖(FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) t‖
        = ‖FourierTransform.fourier (fun x => (ψ : ℝ → ℂ) x) (-t)‖ := by
          rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
      _ ≤ (2 * (2 * C ^ 2) + 2 * (2 * C ^ 2) + 1) / (1 + t ^ 2) := hval
      _ ≤ ((2 * (2 * C ^ 2) + 2 * (2 * C ^ 2) + 1)
            + (2 * (2 * Real.pi * C ^ 2 * (2 * C))
              + 2 * (2 * Real.pi * (2 * C + C ^ 2) * (2 * C)) + 1)) / (1 + t ^ 2) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hid : deriv (fun s : ℝ => (FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) s) t
        = (FourierTransform.fourierInv (psiDerivMap ψ) : SchwartzMap ℝ ℂ) t := by
      have h1 : deriv (fun s : ℝ => (FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) s) t
          = LineDeriv.lineDerivOp (1 : ℝ) (FourierTransform.fourierInv ψ) t := by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
      rw [h1, SchwartzMap.lineDerivOp_fourierInv_eq ψ 1]
      rfl
    rw [hid]
    calc ‖(FourierTransform.fourierInv (psiDerivMap ψ) : SchwartzMap ℝ ℂ) t‖
        = ‖FourierTransform.fourier (fun x => psiDerivMap ψ x) (-t)‖ := by
          rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
      _ ≤ (2 * (2 * Real.pi * C ^ 2 * (2 * C))
            + 2 * (2 * Real.pi * (2 * C + C ^ 2) * (2 * C)) + 1) / (1 + t ^ 2) := hder
      _ ≤ ((2 * (2 * C ^ 2) + 2 * (2 * C ^ 2) + 1)
            + (2 * (2 * Real.pi * C ^ 2 * (2 * C))
              + 2 * (2 * Real.pi * (2 * C + C ^ 2) * (2 * C)) + 1)) / (1 + t ^ 2) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Commons.Analysis.Schwartz
