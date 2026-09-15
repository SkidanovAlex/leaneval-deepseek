import Submission.FUP.PSHDbarPos
import Submission.Commons.Analysis.Calculus.realHessian_expansion_corrected
import Submission.Commons.MeasureTheory.Integral.integral_mul_iteratedFDeriv_two_eq
import Submission.Commons.Analysis.Complex.psh_smooth_plane_laplacian_nonneg
import Submission.Commons.Analysis.Calculus.complexHessian_im_norm

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# `∂∂̄φ ≥ κ` for smooth φ

The pointwise content of `DbarDbarPos`: for a smooth `φ`, two integrations by parts turn
`∫ φ · dbarDbarTest α` into `¼ ∫ ∑_{j,k}[...]`, and the pointwise sum is exactly
`(D²φ z)![α z, α z] + (D²φ z)![I•α z, I•α z]` by
`Commons.Analysis.Calculus.realHessian_expansion_corrected`.  Hence the pointwise inequality
`4 κ z ‖w‖² ≤ (D²φ z)![w,w] + (D²φ z)![I•w, I•w]` implies `DbarDbarPos φ κ`.
-/

namespace Submission.FUP

/-- The pointwise quantity obtained from `dbarDbarTest` by moving the derivatives onto `φ`. -/
noncomputable def dbarDbarHess (φ : ℂᵈ → ℝ) (α : ℂᵈ → (Fin d → ℂ)) : ℂᵈ → ℝ :=
  fun z => ∑ j, ∑ k,
    (formTest α j k z * (dxx j k φ z + dyy j k φ z)
      - formImag α j k z * (dxy j k φ z - dyx j k φ z))

/-- `realHessian_expansion_corrected`, with the test function `α` in place of `w`. -/
lemma realHessian_eq_dbarDbarHess (φ : ℂᵈ → ℝ) (α : ℂᵈ → (Fin d → ℂ)) (z : ℂᵈ) :
    (iteratedFDeriv ℝ 2 φ z) ![α z, α z]
        + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • (α z), Complex.I • (α z)]
      = dbarDbarHess φ α z := by
  rw [Commons.Analysis.Calculus.realHessian_expansion_corrected]
  simp only [dbarDbarHess, dxx, dyy, dxy, dyx, formTest, formImag]


section IBP

/-- Integration by parts for one of the four second-order pieces of `dbarDbarTest`. -/
lemma integral_mul_dxx_eq {φ χ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ) (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) (j k : Fin d) :
    ∫ z, φ z * dxx j k χ z = ∫ z, dxx j k φ z * χ z :=
  Commons.MeasureTheory.Integral.integral_mul_iteratedFDeriv_two_eq hφ hχ hcχ _ _

lemma integral_mul_dyy_eq {φ χ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ) (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) (j k : Fin d) :
    ∫ z, φ z * dyy j k χ z = ∫ z, dyy j k φ z * χ z :=
  Commons.MeasureTheory.Integral.integral_mul_iteratedFDeriv_two_eq hφ hχ hcχ _ _

lemma integral_mul_dxy_eq {φ χ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ) (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) (j k : Fin d) :
    ∫ z, φ z * dxy j k χ z = ∫ z, dxy j k φ z * χ z :=
  Commons.MeasureTheory.Integral.integral_mul_iteratedFDeriv_two_eq hφ hχ hcχ _ _

lemma integral_mul_dyx_eq {φ χ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ) (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) (j k : Fin d) :
    ∫ z, φ z * dyx j k χ z = ∫ z, dyx j k φ z * χ z :=
  Commons.MeasureTheory.Integral.integral_mul_iteratedFDeriv_two_eq hφ hχ hcχ _ _

end IBP

section Main

/-- `dbarDbarTerm` is one summand of `dbarDbarTest`. -/
noncomputable def dbarDbarTerm (α : ℂᵈ → (Fin d → ℂ)) (j k : Fin d) : ℂᵈ → ℝ :=
  fun z => (dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
    - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z

lemma dbarDbarTest_eq (α : ℂᵈ → (Fin d → ℂ)) :
    dbarDbarTest α = fun z => (1/4) * ∑ j, ∑ k, dbarDbarTerm α j k z := rfl

/-- `dbarDbarTermH` is one summand of `dbarDbarHess` (with the derivatives moved onto `φ`). -/
noncomputable def dbarDbarTermH (φ : ℂᵈ → ℝ) (α : ℂᵈ → (Fin d → ℂ)) (j k : Fin d) :
    ℂᵈ → ℝ :=
  fun z => formTest α j k z * (dxx j k φ z + dyy j k φ z)
    - formImag α j k z * (dxy j k φ z - dyx j k φ z)

lemma dbarDbarHess_eq (φ : ℂᵈ → ℝ) (α : ℂᵈ → (Fin d → ℂ)) :
    dbarDbarHess φ α = fun z => ∑ j, ∑ k, dbarDbarTermH φ α j k z := rfl

end Main

section Integrability

/-- A continuous real function on `ℂᵈ` is bounded on every ball. -/
lemma BoundedOnCompact.of_continuous {φ : ℂᵈ → ℝ} (hφ : Continuous φ) :
    BoundedOnCompact φ := by
  intro R
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂᵈ) R).exists_bound_of_continuousOn
    hφ.continuousOn
  exact ⟨C, fun z hz => by
    have hz' : z ∈ Metric.closedBall (0 : ℂᵈ) R := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    have h := hC z hz'
    rwa [Real.norm_eq_abs] at h⟩

lemma continuous_dxx_of_contDiff_two {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ 2 χ) (j k : Fin d) :
    Continuous (fun z => dxx j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j (1:ℂ), Pi.single k (1:ℂ)]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (by norm_num)))

lemma continuous_dyy_of_contDiff_two {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ 2 χ) (j k : Fin d) :
    Continuous (fun z => dyy j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j Complex.I, Pi.single k Complex.I]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (by norm_num)))

lemma continuous_dxy_of_contDiff_two {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ 2 χ) (j k : Fin d) :
    Continuous (fun z => dxy j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j (1:ℂ), Pi.single k Complex.I]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (by norm_num)))

lemma continuous_dyx_of_contDiff_two {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ 2 χ) (j k : Fin d) :
    Continuous (fun z => dyx j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j Complex.I, Pi.single k (1:ℂ)]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (by norm_num)))

/-- `φ` times a compactly supported continuous function is integrable when `φ` is `C²`. -/
lemma integrable_phi_mul {φ g : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun z => φ z * g z) :=
  integrable_mul_of_boundedOnCompact hφ.continuous.measurable
    (BoundedOnCompact.of_continuous hφ.continuous) hg hgc

lemma integrable_formTest_mul_dxx {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    Integrable (fun z => formTest α j k z * dxx j k φ z) :=
  ((continuous_formTest hα.continuous j k).mul (continuous_dxx_of_contDiff_two hφ j k)
    ).integrable_of_hasCompactSupport (HasCompactSupport.mul_right (hasCompactSupport_formTest hsα j k))

lemma integrable_formTest_mul_dyy {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    Integrable (fun z => formTest α j k z * dyy j k φ z) :=
  ((continuous_formTest hα.continuous j k).mul (continuous_dyy_of_contDiff_two hφ j k)
    ).integrable_of_hasCompactSupport (HasCompactSupport.mul_right (hasCompactSupport_formTest hsα j k))

lemma integrable_formImag_mul_dxy {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    Integrable (fun z => formImag α j k z * dxy j k φ z) :=
  ((continuous_formImag hα.continuous j k).mul (continuous_dxy_of_contDiff_two hφ j k)
    ).integrable_of_hasCompactSupport (HasCompactSupport.mul_right (hasCompactSupport_formImag hsα j k))

lemma integrable_formImag_mul_dyx {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    Integrable (fun z => formImag α j k z * dyx j k φ z) :=
  ((continuous_formImag hα.continuous j k).mul (continuous_dyx_of_contDiff_two hφ j k)
    ).integrable_of_hasCompactSupport (HasCompactSupport.mul_right (hasCompactSupport_formImag hsα j k))

lemma integrable_dbarDbarTermH {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    Integrable (dbarDbarTermH φ α j k) := by
  have h1 := integrable_formTest_mul_dxx hφ hα hsα j k
  have h2 := integrable_formTest_mul_dyy hφ hα hsα j k
  have h3 := integrable_formImag_mul_dxy hφ hα hsα j k
  have h4 := integrable_formImag_mul_dyx hφ hα hsα j k
  have hPQ : Integrable (fun z => formTest α j k z * (dxx j k φ z + dyy j k φ z)) :=
    (h1.add h2).congr (Filter.Eventually.of_forall fun z => by
      simp only [Pi.add_apply]; ring)
  have hRS : Integrable (fun z => formImag α j k z * (dxy j k φ z - dyx j k φ z)) :=
    (h3.sub h4).congr (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  exact hPQ.sub hRS

lemma integrable_dbarDbarHess {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) :
    Integrable (dbarDbarHess φ α) := by
  rw [dbarDbarHess_eq]
  exact integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => integrable_dbarDbarTermH hφ hα hsα j k))

end Integrability


section MainIntegral

/-- Integrability bookkeeping for the four-term expression `((f₁+f₂)-f₃)+f₄`. -/
private lemma integral_add_sub_add (f₁ f₂ f₃ f₄ : ℂᵈ → ℝ)
    (h₁ : Integrable f₁) (h₂ : Integrable f₂) (h₃ : Integrable f₃) (h₄ : Integrable f₄) :
    ∫ z, ((f₁ z + f₂ z) - f₃ z) + f₄ z
      = ((∫ z, f₁ z) + ∫ z, f₂ z) - (∫ z, f₃ z) + ∫ z, f₄ z := by
  have h12 : Integrable (fun z => f₁ z + f₂ z) := h₁.add h₂
  have h123 : Integrable (fun z => (f₁ z + f₂ z) - f₃ z) := h12.sub h₃
  rw [integral_add h123 h₄, integral_sub h12 h₃, integral_add h₁ h₂]

lemma integrable_phi_mul_dbarDbarTerm {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    Integrable (fun z => φ z * dbarDbarTerm α j k z) := by
  refine (((integrable_phi_mul hφ (continuous_dxx (contDiff_formTest hα j k) j k)
        (hasCompactSupport_dxx (hasCompactSupport_formTest hsα j k) j k)).add
      (integrable_phi_mul hφ (continuous_dyy (contDiff_formTest hα j k) j k)
        (hasCompactSupport_dyy (hasCompactSupport_formTest hsα j k) j k))).sub
      (integrable_phi_mul hφ (continuous_dxy (contDiff_formImag hα j k) j k)
        (hasCompactSupport_dxy (hasCompactSupport_formImag hsα j k) j k))).add
      (integrable_phi_mul hφ (continuous_dyx (contDiff_formImag hα j k) j k)
        (hasCompactSupport_dyx (hasCompactSupport_formImag hsα j k) j k)) |>.congr ?_
  exact Filter.Eventually.of_forall fun z => by
    simp only [Pi.add_apply, Pi.sub_apply, dbarDbarTerm]; ring

/-- **Integration by parts, one summand.**  The `(j,k)`-th summand of `dbarDbarTest` pairs with
`φ` to give the `(j,k)`-th summand of `dbarDbarHess`. -/
lemma integral_mul_dbarDbarTerm {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) (j k : Fin d) :
    ∫ z, φ z * dbarDbarTerm α j k z = ∫ z, dbarDbarTermH φ α j k z := by
  have hA2 : ContDiff ℝ 2 (formTest α j k) := (contDiff_formTest hα j k).of_le (WithTop.coe_le_coe.mpr le_top)
  have hAc : HasCompactSupport (formTest α j k) := hasCompactSupport_formTest hsα j k
  have hB2 : ContDiff ℝ 2 (formImag α j k) := (contDiff_formImag hα j k).of_le (WithTop.coe_le_coe.mpr le_top)
  have hBc : HasCompactSupport (formImag α j k) := hasCompactSupport_formImag hsα j k
  set f1 : ℂᵈ → ℝ := fun z => φ z * dxx j k (formTest α j k) z with hf1
  set f2 : ℂᵈ → ℝ := fun z => φ z * dyy j k (formTest α j k) z with hf2
  set f3 : ℂᵈ → ℝ := fun z => φ z * dxy j k (formImag α j k) z with hf3
  set f4 : ℂᵈ → ℝ := fun z => φ z * dyx j k (formImag α j k) z with hf4
  set g1 : ℂᵈ → ℝ := fun z => formTest α j k z * dxx j k φ z with hg1
  set g2 : ℂᵈ → ℝ := fun z => formTest α j k z * dyy j k φ z with hg2
  set g3 : ℂᵈ → ℝ := fun z => formImag α j k z * dxy j k φ z with hg3
  set g4 : ℂᵈ → ℝ := fun z => formImag α j k z * dyx j k φ z with hg4
  have hF1 : Integrable f1 := integrable_phi_mul hφ (continuous_dxx (contDiff_formTest hα j k) j k)
    (hasCompactSupport_dxx hAc j k)
  have hF2 : Integrable f2 := integrable_phi_mul hφ (continuous_dyy (contDiff_formTest hα j k) j k)
    (hasCompactSupport_dyy hAc j k)
  have hF3 : Integrable f3 := integrable_phi_mul hφ (continuous_dxy (contDiff_formImag hα j k) j k)
    (hasCompactSupport_dxy hBc j k)
  have hF4 : Integrable f4 := integrable_phi_mul hφ (continuous_dyx (contDiff_formImag hα j k) j k)
    (hasCompactSupport_dyx hBc j k)
  have hG1 : Integrable g1 := integrable_formTest_mul_dxx hφ hα hsα j k
  have hG2 : Integrable g2 := integrable_formTest_mul_dyy hφ hα hsα j k
  have hG3 : Integrable g3 := integrable_formImag_mul_dxy hφ hα hsα j k
  have hG4 : Integrable g4 := integrable_formImag_mul_dyx hφ hα hsα j k
  have hL : ∫ z, φ z * dbarDbarTerm α j k z = ((∫ z, f1 z) + ∫ z, f2 z) - (∫ z, f3 z) + ∫ z, f4 z := by
    rw [show (fun z => φ z * dbarDbarTerm α j k z)
        = fun z => ((f1 z + f2 z) - f3 z) + f4 z from by
      funext z
      simp only [hf1, hf2, hf3, hf4, dbarDbarTerm]
      ring]
    exact integral_add_sub_add f1 f2 f3 f4 hF1 hF2 hF3 hF4
  have hR : ∫ z, dbarDbarTermH φ α j k z = ((∫ z, g1 z) + ∫ z, g2 z) - (∫ z, g3 z) + ∫ z, g4 z := by
    rw [show (fun z => dbarDbarTermH φ α j k z)
        = fun z => ((g1 z + g2 z) - g3 z) + g4 z from by
      funext z
      simp only [hg1, hg2, hg3, hg4, dbarDbarTermH]
      ring]
    exact integral_add_sub_add g1 g2 g3 g4 hG1 hG2 hG3 hG4
  have e1 : ∫ z, f1 z = ∫ z, g1 z := by
    rw [hf1, hg1, integral_mul_dxx_eq hφ hA2 hAc j k]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have e2 : ∫ z, f2 z = ∫ z, g2 z := by
    rw [hf2, hg2, integral_mul_dyy_eq hφ hA2 hAc j k]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have e3 : ∫ z, f3 z = ∫ z, g3 z := by
    rw [hf3, hg3, integral_mul_dxy_eq hφ hB2 hBc j k]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have e4 : ∫ z, f4 z = ∫ z, g4 z := by
    rw [hf4, hg4, integral_mul_dyx_eq hφ hB2 hBc j k]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  rw [hL, hR, e1, e2, e3, e4]

/-- **The integration-by-parts identity for `dbarDbarTest`.** -/
lemma integral_mul_dbarDbarTest {φ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) (hsα : HasCompactSupport α) :
    ∫ z, φ z * dbarDbarTest α z = (1/4) * ∫ z, dbarDbarHess φ α z := by
  have hpull : ∀ z, (∑ j : Fin d, ∑ k : Fin d, φ z * dbarDbarTerm α j k z)
      = φ z * ∑ j : Fin d, ∑ k : Fin d, dbarDbarTerm α j k z := by
    intro z
    simp_rw [← Finset.mul_sum]
  have hpt : ∀ z, φ z * dbarDbarTest α z
      = (1/4) * ∑ j : Fin d, ∑ k : Fin d, φ z * dbarDbarTerm α j k z := by
    intro z
    rw [hpull z, dbarDbarTest_eq]
    ring
  have hInt : ∀ j : Fin d, Integrable (fun z => ∑ k : Fin d, φ z * dbarDbarTerm α j k z) :=
    fun j => integrable_finsetSum Finset.univ
      (fun k _ => integrable_phi_mul_dbarDbarTerm hφ hα hsα j k)
  have hIntR : ∀ j : Fin d, Integrable (fun z => ∑ k : Fin d, dbarDbarTermH φ α j k z) :=
    fun j => integrable_finsetSum Finset.univ
      (fun k _ => integrable_dbarDbarTermH hφ hα hsα j k)
  have hL : ∫ z, (∑ j : Fin d, ∑ k : Fin d, φ z * dbarDbarTerm α j k z)
      = ∑ j : Fin d, ∑ k : Fin d, ∫ z, φ z * dbarDbarTerm α j k z := by
    rw [integral_finsetSum Finset.univ (fun j _ => hInt j)]
    exact Finset.sum_congr rfl fun j _ =>
      integral_finsetSum Finset.univ (fun k _ => integrable_phi_mul_dbarDbarTerm hφ hα hsα j k)
  have hR : ∫ z, (∑ j : Fin d, ∑ k : Fin d, dbarDbarTermH φ α j k z)
      = ∑ j : Fin d, ∑ k : Fin d, ∫ z, dbarDbarTermH φ α j k z := by
    rw [integral_finsetSum Finset.univ (fun j _ => hIntR j)]
    exact Finset.sum_congr rfl fun j _ =>
      integral_finsetSum Finset.univ (fun k _ => integrable_dbarDbarTermH hφ hα hsα j k)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, dbarDbarHess_eq,
    hL, hR]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    integral_mul_dbarDbarTerm hφ hα hsα j k

/-- **A smooth `φ` with a pointwise Hessian lower bound satisfies `∂∂̄φ ≥ κ`.** -/
theorem dbarDbarPos_of_hessian {φ κ : ℂᵈ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hκm : Measurable κ) (hκb : BoundedOnCompact κ) (hφb : BoundedOnCompact φ)
    (h : ∀ z w, 4 * (κ z * ∑ j, ‖w j‖ ^ 2) ≤
      (iteratedFDeriv ℝ 2 φ z) ![w, w] + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w]) :
    DbarDbarPos φ κ := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  intro α hα hsα
  have hκint : Integrable (fun z => κ z * formNormSq α z) :=
    integrable_mul_of_boundedOnCompact hκm hκb (continuous_formNormSq hα.continuous)
      (hasCompactSupport_formNormSq hsα)
  refine ⟨hκint, ?_, ?_⟩
  · exact integrable_mul_of_boundedOnCompact hφ2.continuous.measurable hφb
      (continuous_dbarDbarTest hα) (hasCompactSupport_dbarDbarTest hsα)
  · rw [integral_mul_dbarDbarTest hφ2 hα hsα]
    have hpt : ∀ z, 4 * (κ z * formNormSq α z) ≤ dbarDbarHess φ α z := by
      intro z
      rw [← realHessian_eq_dbarDbarHess φ α z]
      simpa only [formNormSq] using h z (α z)
    have hone : Integrable (fun z => 4 * (κ z * formNormSq α z)) := hκint.const_mul 4
    have htwo : Integrable (dbarDbarHess φ α) := integrable_dbarDbarHess hφ2 hα hsα
    have hmono := integral_mono hone htwo hpt
    rw [integral_const_mul] at hmono
    linarith

end MainIntegral

end Submission.FUP


