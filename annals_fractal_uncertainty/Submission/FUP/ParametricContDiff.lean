import Submission.FUP.GkBound
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff Interval

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Smoothness of parametric interval integrals

`y ↦ ∫_a^b ψ t • F (t • y) dt` is `C^n` when `F` is `C^n` and `ψ` is continuous.  The proof is an
induction using `hasFDerivAt_intervalIntegral_of_continuous`
(`Commons.Analysis.Calculus`): the derivative of the integral is again an integral of the same
shape, with `F` replaced by `fderiv ℝ F` and `ψ` by `t ↦ ψ t * t`.

The cases `n = 0,…,3` are written separately because the codomain changes at each step
(`G`, then `E →L[ℝ] G`, …), which a single `induction` on `n` cannot express in Lean's
universe hierarchy.
-/

theorem contDiff0_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → G} {ψ : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ 0 F) (hψ : Continuous ψ) :
    ContDiff ℝ 0 (fun y : E => ∫ t in a..b, ψ t • F (t • y)) := by
  refine contDiff_zero.mpr ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := a) (s := fun _ : E => b) ?_ continuous_const
  have hFc : Continuous F := contDiff_zero.mp hF
  exact (hψ.comp continuous_snd).smul (hFc.comp (continuous_snd.smul continuous_fst))

theorem contDiff1_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → G} {ψ : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ 1 F) (hψ : Continuous ψ) :
    ContDiff ℝ 1 (fun y : E => ∫ t in a..b, ψ t • F (t • y)) := by
  rw [show (1 : ℕ∞ω) = ((0 : ℕ) : ℕ∞ω) + 1 by norm_num]
  rw [contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x : E => ∫ t in a..b, (ψ t * t) • fderiv ℝ F (t • x), ?_, ?_⟩
  · exact contDiff0_intervalIntegral (hF.fderiv_right (by norm_num)) (hψ.mul continuous_id)
  · intro x
    exact Commons.Analysis.Calculus.hasFDerivAt_intervalIntegral_of_continuous
      (f := fun (y : E) (t : ℝ) => ψ t • F (t • y))
      (f' := fun (y : E) (t : ℝ) => (ψ t * t) • fderiv ℝ F (t • y))
      (by
        have h1 : Continuous (fun p : E × ℝ => F (p.2 • p.1)) :=
          hF.continuous.comp (continuous_snd.smul continuous_fst)
        exact (hψ.comp continuous_snd).smul h1)
      (by
        have hD : Continuous (fun p : E × ℝ => fderiv ℝ F (p.2 • p.1)) :=
          (hF.continuous_fderiv (by norm_num)).comp (continuous_snd.smul continuous_fst)
        have hc : Continuous (fun p : E × ℝ => ψ p.2 * p.2) :=
          (hψ.comp continuous_snd).mul continuous_snd
        exact hc.smul hD)
      (fun y t => by
        have hdiff : DifferentiableAt ℝ F (t • y) :=
          (hF.differentiable (by norm_num)).differentiableAt
        have hinner : HasFDerivAt (fun y : E => t • y) (t • (1 : E →L[ℝ] E)) y :=
          (hasFDerivAt_id y).const_smul t
        have hcomp := (hdiff.hasFDerivAt).comp y hinner
        have hclm : (fderiv ℝ F (t • y)).comp (t • (1 : E →L[ℝ] E)) = t • fderiv ℝ F (t • y) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
        have hres := (hclm ▸ hcomp).const_smul (ψ t)
        rw [smul_smul] at hres
        exact hres)

theorem contDiff2_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → G} {ψ : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ 2 F) (hψ : Continuous ψ) :
    ContDiff ℝ 2 (fun y : E => ∫ t in a..b, ψ t • F (t • y)) := by
  rw [show (2 : ℕ∞ω) = ((1 : ℕ) : ℕ∞ω) + 1 by norm_num]
  rw [contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x : E => ∫ t in a..b, (ψ t * t) • fderiv ℝ F (t • x), ?_, ?_⟩
  · exact contDiff1_intervalIntegral (hF.fderiv_right (by norm_num)) (hψ.mul continuous_id)
  · intro x
    exact Commons.Analysis.Calculus.hasFDerivAt_intervalIntegral_of_continuous
      (f := fun (y : E) (t : ℝ) => ψ t • F (t • y))
      (f' := fun (y : E) (t : ℝ) => (ψ t * t) • fderiv ℝ F (t • y))
      (by
        have h1 : Continuous (fun p : E × ℝ => F (p.2 • p.1)) :=
          hF.continuous.comp (continuous_snd.smul continuous_fst)
        exact (hψ.comp continuous_snd).smul h1)
      (by
        have hD : Continuous (fun p : E × ℝ => fderiv ℝ F (p.2 • p.1)) :=
          (hF.continuous_fderiv (by norm_num)).comp (continuous_snd.smul continuous_fst)
        have hc : Continuous (fun p : E × ℝ => ψ p.2 * p.2) :=
          (hψ.comp continuous_snd).mul continuous_snd
        exact hc.smul hD)
      (fun y t => by
        have hdiff : DifferentiableAt ℝ F (t • y) :=
          (hF.differentiable (by norm_num)).differentiableAt
        have hinner : HasFDerivAt (fun y : E => t • y) (t • (1 : E →L[ℝ] E)) y :=
          (hasFDerivAt_id y).const_smul t
        have hcomp := (hdiff.hasFDerivAt).comp y hinner
        have hclm : (fderiv ℝ F (t • y)).comp (t • (1 : E →L[ℝ] E)) = t • fderiv ℝ F (t • y) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
        have hres := (hclm ▸ hcomp).const_smul (ψ t)
        rw [smul_smul] at hres
        exact hres)

theorem contDiff3_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → G} {ψ : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ 3 F) (hψ : Continuous ψ) :
    ContDiff ℝ 3 (fun y : E => ∫ t in a..b, ψ t • F (t • y)) := by
  rw [show (3 : ℕ∞ω) = ((2 : ℕ) : ℕ∞ω) + 1 by norm_num]
  rw [contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x : E => ∫ t in a..b, (ψ t * t) • fderiv ℝ F (t • x), ?_, ?_⟩
  · exact contDiff2_intervalIntegral (hF.fderiv_right (by norm_num)) (hψ.mul continuous_id)
  · intro x
    exact Commons.Analysis.Calculus.hasFDerivAt_intervalIntegral_of_continuous
      (f := fun (y : E) (t : ℝ) => ψ t • F (t • y))
      (f' := fun (y : E) (t : ℝ) => (ψ t * t) • fderiv ℝ F (t • y))
      (by
        have h1 : Continuous (fun p : E × ℝ => F (p.2 • p.1)) :=
          hF.continuous.comp (continuous_snd.smul continuous_fst)
        exact (hψ.comp continuous_snd).smul h1)
      (by
        have hD : Continuous (fun p : E × ℝ => fderiv ℝ F (p.2 • p.1)) :=
          (hF.continuous_fderiv (by norm_num)).comp (continuous_snd.smul continuous_fst)
        have hc : Continuous (fun p : E × ℝ => ψ p.2 * p.2) :=
          (hψ.comp continuous_snd).mul continuous_snd
        exact hc.smul hD)
      (fun y t => by
        have hdiff : DifferentiableAt ℝ F (t • y) :=
          (hF.differentiable (by norm_num)).differentiableAt
        have hinner : HasFDerivAt (fun y : E => t • y) (t • (1 : E →L[ℝ] E)) y :=
          (hasFDerivAt_id y).const_smul t
        have hcomp := (hdiff.hasFDerivAt).comp y hinner
        have hclm : (fderiv ℝ F (t • y)).comp (t • (1 : E →L[ℝ] E)) = t • fderiv ℝ F (t • y) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
        have hres := (hclm ▸ hcomp).const_smul (ψ t)
        rw [smul_smul] at hres
        exact hres)

/-- Smoothness of the windowed spherical average. -/
theorem contDiff_gwin (k : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) :
    ContDiff ℝ 3 (gwin k w) := by
  have h : ContDiff ℝ 3
      (fun y : ℝᵈ => ∫ t in (1 / 8 : ℝ)..8, winPhi t • omegaPiece k w (t • y)) :=
    contDiff3_intervalIntegral (F := omegaPiece k w) (ψ := winPhi) (a := (1 / 8 : ℝ)) (b := 8)
      (contDiff_omegaPiece (d := d) hw k (le_refl 3)) continuous_winPhi
  rw [contDiff_iff_contDiffAt] at h ⊢
  intro y
  refine (h y).congr_of_eventuallyEq ?_
  filter_upwards with z
  rw [gwin_def]
  exact intervalIntegral.integral_congr fun t _ => by rw [smul_eq_mul, mul_comm]

/-- The form needed by `norm_iteratedFDeriv_hk_le` and `norm_iteratedFDeriv_gk_le`. -/
theorem contDiffOn_gwin (k : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) :
    ContDiffOn ℝ 3 (gwin k w) (annOpen (d := d) k) :=
  (contDiff_gwin (d := d) k hw).contDiffOn

end Submission.FUP
