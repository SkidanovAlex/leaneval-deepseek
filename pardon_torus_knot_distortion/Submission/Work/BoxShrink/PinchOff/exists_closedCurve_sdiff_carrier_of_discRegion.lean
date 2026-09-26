import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential
import Submission.Work.BoxShrink.PinchOff.IB.Span
import Submission.Work.BoxShrink.PinchOff.pushoff_plane_interior
import Submission.Work.BoxShrink.PinchOff.pushoff_plane_boundary

namespace Work.BoxShrink.PinchOff

noncomputable section

open LeanEval.KnotTheory.PardonDistortion
open Set

/-! ## The main lemma -/

theorem exists_closedCurve_sdiff_carrier_of_discRegion
    {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : D.boundary ⊆ X)
    (δ : Work.CoreTopology.ClosedCurve P)
    (hδ : ∀ t : ℝ, δ t ∈ X) :
    ∃ δ' : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, δ' t ∈ X \ D.carrier) ∧
      Work.SurgeryInvariance.windingOf P δ' = Work.SurgeryInvariance.windingOf P δ := by
  classical
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P δ
  set a : ℤ := (Work.SurgeryInvariance.windingOf P δ).1 with ha
  set b : ℤ := (Work.SurgeryInvariance.windingOf P δ).2 with hb
  have hLw : L.winding = (a, b) := by
    rw [← Work.SurgeryInvariance.windingOf_eq P δ L]
  set Λ : ℝ → ℂ := fun t => Complex.mk (L.Θ t) (L.Φ t) with hΛdef
  have hΛc : Continuous Λ := by
    have h : (fun t : ℝ => Complex.mk (L.Θ t) (L.Φ t))
        = fun t : ℝ => (L.Θ t : ℂ) + (L.Φ t : ℂ) * Complex.I := by
      funext t; apply Complex.ext <;> simp
    rw [hΛdef, h]
    exact (Complex.continuous_ofReal.comp L.contΘ).add
      ((Complex.continuous_ofReal.comp L.contΦ).mul continuous_const)
  have hΛper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + periodPt a b := by
    intro t
    obtain ⟨h1, h2⟩ := L.period_shift_winding t
    rw [hLw] at h1 h2
    apply Complex.ext
    · simp only [hΛdef, Complex.add_re, periodPt_re]
      rw [h1]
    · simp only [hΛdef, Complex.add_im, periodPt_im]
      rw [h2]
  have hΛmem : ∀ t : ℝ, Λ t ∈ Xtilde P X := by
    intro t
    rw [mem_Xtilde]
    rw [show planePsi P (Λ t) = δ t from by
      simp only [planePsi_apply, hΛdef]
      exact L.lifts t]
    exact hδ t
  obtain ⟨Λ₁, hΛ₁c, hΛ₁per, hΛ₁mem, hΛ₁avoid⟩ :=
    Work.BoxShrink.PinchOff.pushoff_plane_interior D hX hsub hΛc hΛper hΛmem
  obtain ⟨c, hcc, hcper, hcmem⟩ :=
    Work.BoxShrink.PinchOff.pushoff_plane_boundary D hX hsub hΛ₁c hΛ₁per
      (fun t => ⟨hΛ₁mem t, hΛ₁avoid t⟩)
  have h2pi : c (2 * Real.pi) = c 0 + periodPt a b := by
    simpa using hcper 0
  obtain ⟨δ', hδ', hw'⟩ := exists_closedCurve_of_path c hcc rfl h2pi
    (fun t _ => hcmem t)
  refine ⟨δ', hδ', ?_⟩
  rw [hw']

end

end Work.BoxShrink.PinchOff
