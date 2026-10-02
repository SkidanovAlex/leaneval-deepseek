import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.ThomBordism.LeadChapter.thetaAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.LeadChapter

theorem thetaInvAux {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type}
    [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ) (hR : 0 < G.R) :
    (∀ v : EuclideanSpace ℝ (Fin (k + 8)),
        Work.ThomBordism.LeadChapter.thetaInv G m k₀ j₀
          (Work.ThomBordism.LeadChapter.theta G m k₀ j₀ v) = v) ∧
      (∀ v : EuclideanSpace ℝ (Fin (k + 8)),
        HasFDerivAt (Work.ThomBordism.LeadChapter.thetaInv G m k₀ j₀)
          (Work.ThomBordism.LeadChapter.dthetaInv G m k₀ j₀
            (Work.ThomBordism.LeadChapter.theta G m k₀ j₀ v))
          (Work.ThomBordism.LeadChapter.theta G m k₀ j₀ v)) ∧
      (∀ v : EuclideanSpace ℝ (Fin (k + 8)),
        (Work.ThomBordism.LeadChapter.dtheta G m k₀ j₀ v).comp
          (Work.ThomBordism.LeadChapter.dthetaInv G m k₀ j₀
            (Work.ThomBordism.LeadChapter.theta G m k₀ j₀ v)) = 1) ∧
      (∀ v : EuclideanSpace ℝ (Fin (k + 8)),
        (Work.ThomBordism.LeadChapter.dthetaInv G m k₀ j₀
            (Work.ThomBordism.LeadChapter.theta G m k₀ j₀ v)).comp
          (Work.ThomBordism.LeadChapter.dtheta G m k₀ j₀ v) = 1) ∧
      (∀ v : EuclideanSpace ℝ (Fin (k + 8)),
        0 < LinearMap.det (Work.ThomBordism.LeadChapter.dthetaEndo G m k₀ j₀ v).toLinearMap) := by
  -- The chain rule: differentiating the identity `thetaInv ∘ theta = id` gives the second inverse
  -- identity (`dthetaInv (theta v) ∘ dtheta v = 1`).
  have hchain : ∀ v : EuclideanSpace ℝ (Fin (k + 8)),
      (dthetaInv G m k₀ j₀ (theta G m k₀ j₀ v)).comp (dtheta G m k₀ j₀ v) = 1 := by
    intro v
    have hcomp := fderiv_comp (𝕜 := ℝ) (x := v) (f := theta G m k₀ j₀) (g := thetaInv G m k₀ j₀)
      (thetaAux_differentiableAt_thetaInv G m k₀ j₀ hR v) (differentiableAt_theta G m k₀ j₀ v)
    rw [show (thetaInv G m k₀ j₀) ∘ (theta G m k₀ j₀) = id from
      funext fun w => thetaInv_theta G m k₀ j₀ hR w, fderiv_id] at hcomp
    exact hcomp.symm
  -- A left inverse of a square map is a two-sided inverse.
  have hleft : ∀ v : EuclideanSpace ℝ (Fin (k + 8)),
      (dtheta G m k₀ j₀ v).comp (dthetaInv G m k₀ j₀ (theta G m k₀ j₀ v)) = 1 := fun v =>
    comp_eq_one_of_comp_eq_one (dtheta G m k₀ j₀ v)
      (dthetaInv G m k₀ j₀ (theta G m k₀ j₀ v)) (hchain v)
  refine ⟨fun v => thetaInv_theta G m k₀ j₀ hR v,
    fun v => (thetaAux_differentiableAt_thetaInv G m k₀ j₀ hR v).hasFDerivAt,
    hleft, hchain, fun v => thetaAux_det_dthetaEndo_pos G m k₀ j₀ hR v⟩

end Work.ThomBordism.LeadChapter
