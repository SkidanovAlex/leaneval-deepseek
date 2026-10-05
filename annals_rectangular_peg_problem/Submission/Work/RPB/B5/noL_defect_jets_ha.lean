import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B5.chartJets_oneSided
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPA3.deriv_deriv_swap
import Submission.Work.RPB.B5.chart_rho_lagrangian
import Submission.Work.RPV.Defs

open Filter

namespace Work.RPB.B5

/-! ## The level point recovers a point from its reduced coordinate, level and phase -/

/-- If `K₀ x + 1 = -σ` then `x` is the point of the level `K₀ = -1 - σ` whose reduced
coordinate is `uproj x` and whose phase `q₂` is `x.1.2`. -/
theorem levelPt_uproj_eq_self (x : Work.RPV.PS) (σ : ℝ) (h : Work.RPV.K0 x + 1 = -σ) :
    Work.RPV.levelPt (Work.RPV.uproj x) σ x.1.2 = x := by
  have hexp : Complex.exp (-(x.1.2 : ℂ) * Complex.I) * Complex.exp ((x.1.2 : ℂ) * Complex.I)
      = 1 := by
    rw [← Complex.exp_add]; simp
  have hw : Complex.exp (-(x.1.2 : ℂ) * Complex.I) *
      (Complex.exp ((x.1.2 : ℂ) * Complex.I) * ((x.2.1 : ℂ) + (x.1.1 : ℂ) * Complex.I))
      = ((x.2.1 : ℂ) + (x.1.1 : ℂ) * Complex.I) := by
    rw [← mul_assoc, hexp, one_mul]
  have hnorm : ‖Complex.exp ((x.1.2 : ℂ) * Complex.I)
      * ((x.2.1 : ℂ) + (x.1.1 : ℂ) * Complex.I)‖ ^ 2 = x.2.1 ^ 2 + x.1.1 ^ 2 := by
    rw [norm_mul, Complex.norm_exp]
    have hz : (↑x.1.2 * Complex.I).re = 0 := by simp
    rw [hz, Real.exp_zero, one_mul, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hK : x.2.2 = (x.1.1 ^ 2 + x.2.1 ^ 2) / 2 - σ - 1 := by
    simp only [Work.RPV.K0] at h
    linarith
  ext <;> simp only [Work.RPV.levelPt, Work.RPV.uproj]
  · rw [hw]; simp
  · rw [hw]; simp
  · rw [hnorm]; linarith

/-! ## Smoothness of the one-variable slices of a partial derivative -/

/-- For a `C^{n+1}` function `Ψ : ℝ × ℝ → E`, both one-variable slices of the partial
derivative are `C^n`: `σ ↦ ∂₂Ψ(σ,t)` and `σ ↦ ∂₁Ψ(σ,t)`. -/
theorem contDiffAt_deriv_slices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : ℝ × ℝ → E) {n : ℕ} {σ₀ t : ℝ} (h : ContDiffAt ℝ (n + 1) Ψ (σ₀, t)) :
    ContDiffAt ℝ n (fun σ : ℝ => deriv (fun s => Ψ (σ, s)) t) σ₀ ∧
    ContDiffAt ℝ n (fun σ : ℝ => deriv (fun s => Ψ (s, t)) σ) σ₀ := by
  have hF : ContDiffAt ℝ n (fderiv ℝ Ψ) (σ₀, t) := h.fderiv_right (by norm_num)
  have hdiff : ∀ᶠ z : ℝ × ℝ in nhds (σ₀, t), HasFDerivAt Ψ (fderiv ℝ Ψ z) z := by
    filter_upwards [h.eventually (by norm_num)] with z hz
    exact (hz.differentiableAt (by norm_num)).hasFDerivAt
  have hcont : Tendsto (fun σ : ℝ => (σ, t)) (nhds σ₀) (nhds (σ₀, t)) :=
    (continuous_id.prodMk continuous_const).tendsto σ₀
  have hdiff2 : ∀ᶠ σ : ℝ in nhds σ₀, HasFDerivAt Ψ (fderiv ℝ Ψ (σ, t)) (σ, t) :=
    hcont.eventually hdiff
  constructor
  · have hV : ContDiffAt ℝ n (fun z : ℝ × ℝ => fderiv ℝ Ψ z (0, 1)) (σ₀, t) :=
      hF.clm_apply contDiffAt_const
    have hsec : ContDiffAt ℝ n (fun σ : ℝ => (σ, t)) σ₀ := by fun_prop
    have hcomp : ContDiffAt ℝ n (fun σ : ℝ => fderiv ℝ Ψ (σ, t) (0, 1)) σ₀ := by
      simpa only [Function.comp_def] using hV.comp σ₀ hsec
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hdiff2] with σ hσ
    exact Work.RPA3.deriv_prodMk_right hσ
  · have hV : ContDiffAt ℝ n (fun z : ℝ × ℝ => fderiv ℝ Ψ z (1, 0)) (σ₀, t) :=
      hF.clm_apply contDiffAt_const
    have hsec : ContDiffAt ℝ n (fun σ : ℝ => (σ, t)) σ₀ := by fun_prop
    have hcomp : ContDiffAt ℝ n (fun σ : ℝ => fderiv ℝ Ψ (σ, t) (1, 0)) σ₀ := by
      simpa only [Function.comp_def] using hV.comp σ₀ hsec
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hdiff2] with σ hσ
    exact Work.RPA3.deriv_prodMk_left hσ

/-- `ωC` of two jointly `C^n` families of complex numbers is `C^n`. -/
theorem contDiffAt_omegaC {X₁ X₂ : ℝ → ℂ} {x : ℝ} {n : WithTop ℕ∞}
    (h₁ : ContDiffAt ℝ n X₁ x) (h₂ : ContDiffAt ℝ n X₂ x) :
    ContDiffAt ℝ n (fun σ : ℝ => Work.RPV.ωC (X₁ σ) (X₂ σ)) x := by
  rw [show (fun σ : ℝ => Work.RPV.ωC (X₁ σ) (X₂ σ))
      = fun σ => (X₁ σ).re * (X₂ σ).im - (X₁ σ).im * (X₂ σ).re by
        funext σ; simp only [Work.RPV.ωC, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring]
  have h1r : ContDiffAt ℝ n (fun σ : ℝ => (X₁ σ).re) x := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      ContDiffAt.comp x ((Complex.reCLM.contDiff (n := n)).contDiffAt) h₁
  have h1i : ContDiffAt ℝ n (fun σ : ℝ => (X₁ σ).im) x := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      ContDiffAt.comp x ((Complex.imCLM.contDiff (n := n)).contDiffAt) h₁
  have h2r : ContDiffAt ℝ n (fun σ : ℝ => (X₂ σ).re) x := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      ContDiffAt.comp x ((Complex.reCLM.contDiff (n := n)).contDiffAt) h₂
  have h2i : ContDiffAt ℝ n (fun σ : ℝ => (X₂ σ).im) x := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      ContDiffAt.comp x ((Complex.imCLM.contDiff (n := n)).contDiffAt) h₂
  exact (h1r.mul h2i).sub (h1i.mul h2r)

/-! ## The main statement -/

end Work.RPB.B5
