/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EqcBasis`: the basis entries of the second derivative, and rectangle integrals

Support module for `Sobolev/equicontinuous_deriv4_of_uniform_Hk6.lean`: the four entries of the
second Fréchet derivative of a curried function (on the standard basis of `ℝ × ℝ`) expressed
through the iterated slice derivatives `∂_z`, `∂_θ`, and the two elementary manipulations of set
integrals over a product of closed intervals.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option maxHeartbeats 1000000

set_option autoImplicit false

/-- The four entries (on the standard basis) of the second Fréchet derivative of a curried
function, in terms of the iterated slice derivatives. -/
lemma eqc_fderiv_fderiv_basis_apply {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) U) {z θ : ℝ} (hz : (z, θ) ∈ U) :
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
        = Work.Spaces.pzIter 2 G z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
        = Work.Spaces.pz (Work.Spaces.pth G) z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
        = Work.Spaces.pth (Work.Spaces.pz G) z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
        = Work.Spaces.pthIter 2 G z θ := by
  have hdat : ∀ y ∈ U, DifferentiableAt ℝ (Function.uncurry G) y := fun y hy =>
    (hG.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hfdOn : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry G)) U :=
    hG.fderiv_of_isOpen hU le_rfl
  have hdat2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ (Function.uncurry G)) y := fun y hy =>
    (hfdOn.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  -- the two curried partials
  set Az : ℝ → ℝ → ℝ := fun z' θ' => fderiv ℝ (Function.uncurry G) (z', θ') (1, 0) with hAzdef
  set Aθ : ℝ → ℝ → ℝ := fun z' θ' => fderiv ℝ (Function.uncurry G) (z', θ') (0, 1) with hAθdef
  have hAz_sm : ContDiffOn ℝ ⊤ (Function.uncurry Az) U := hfdOn.clm_apply contDiffOn_const
  have hAθ_sm : ContDiffOn ℝ ⊤ (Function.uncurry Aθ) U := hfdOn.clm_apply contDiffOn_const
  have hAz_diff : DifferentiableAt ℝ (Function.uncurry Az) (z, θ) :=
    (hAz_sm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hAθ_diff : DifferentiableAt ℝ (Function.uncurry Aθ) (z, θ) :=
    (hAθ_sm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hAz_eq : Set.EqOn (Function.uncurry Az) (Function.uncurry (Work.Spaces.pz G)) U := by
    intro y hy
    exact (Work.Spaces.pz_eq_fderiv (hdat y hy)).symm
  have hAθ_eq : Set.EqOn (Function.uncurry Aθ) (Function.uncurry (Work.Spaces.pth G)) U := by
    intro y hy
    exact (Work.Spaces.pth_eq_fderiv (hdat y hy)).symm
  have key : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y v) (z, θ)
        = (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip v := by
    intro v
    rw [fderiv_clm_apply (hdat2 (z, θ) hz) (differentiableAt_const v), fderiv_const_apply]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (1, 0)) (1, 0) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (1, 0)) (z, θ) (1, 0) := by
          rw [key]
      _ = Work.Spaces.pz Az z θ := (Work.Spaces.pz_eq_fderiv hAz_diff).symm
      _ = Work.Spaces.pz (Work.Spaces.pz G) z θ :=
          Work.Spaces.pz_congr_of_isOpen hU hAz_eq hz
      _ = Work.Spaces.pzIter 2 G z θ := rfl
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (0, 1)) (1, 0) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (0, 1)) (z, θ) (1, 0) := by
          rw [key]
      _ = Work.Spaces.pz Aθ z θ := (Work.Spaces.pz_eq_fderiv hAθ_diff).symm
      _ = Work.Spaces.pz (Work.Spaces.pth G) z θ :=
          Work.Spaces.pz_congr_of_isOpen hU hAθ_eq hz
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (1, 0)) (0, 1) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (1, 0)) (z, θ) (0, 1) := by
          rw [key]
      _ = Work.Spaces.pth Az z θ := (Work.Spaces.pth_eq_fderiv hAz_diff).symm
      _ = Work.Spaces.pth (Work.Spaces.pz G) z θ :=
          eqc_pth_congr_of_isOpen hU hAz_eq hz
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (0, 1)) (0, 1) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (0, 1)) (z, θ) (0, 1) := by
          rw [key]
      _ = Work.Spaces.pth Aθ z θ := (Work.Spaces.pth_eq_fderiv hAθ_diff).symm
      _ = Work.Spaces.pth (Work.Spaces.pth G) z θ :=
          eqc_pth_congr_of_isOpen hU hAθ_eq hz
      _ = Work.Spaces.pthIter 2 G z θ := rfl

/-- A set integral over a product of closed intervals is an iterated interval integral. -/
lemma eqc_setIntegral_rect_eq {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (h : IntegrableOn (fun x : ℝ × ℝ => (f x) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f x) ^ 2)
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (f (z, θ)) ^ 2 := by
  rw [Measure.volume_eq_prod ℝ ℝ] at h ⊢
  exact setIntegral_prod (fun x : ℝ × ℝ => (f x) ^ 2) h

/-- Congruence of the squared-set-integral under a pointwise equality on the set. -/
lemma eqc_setIntegral_sq_congr {f₁ f₂ : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (h : ∀ x ∈ s, f₁ x = f₂ x) :
    (∫ x in s, (f₁ x) ^ 2) = ∫ x in s, (f₂ x) ^ 2 :=
  setIntegral_congr_fun hs fun x hx => by rw [h x hx]

end Work.FTS.StrongLWP.Sobolev
