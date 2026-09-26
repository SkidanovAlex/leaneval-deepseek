import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.Transport
import Submission.Work.Smooth.SphereJordan.thetaPlaneTwoComponents
import Submission.Work.Smooth.SphereJordan.exists_planeCurve_of_avoids_infty
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_isSimpleClosedCurve

/-!
# Transport of the planar Jordan separation to the Riemann sphere

Steps 1-3 of the plan in `JORDAN_NOTES.md`: a simple closed curve on `OnePoint ℂ` is conjugate by a
homeomorphism of the sphere to one avoiding `∞`, and hence is the sphere-image of a continuous
`2π`-periodic injective plane curve, to which the (proved, sorry-free) planar Jordan separation
`Work.Smooth.SphereJordan.nonempty_planeSeparation_of_continuous` applies.  The remaining steps 4-5
(apply it and push the two open preconnected pieces back through the homeomorphism) are below.
-/

noncomputable section

open Set Classical

namespace Work.Smooth.SphereJordan

/-- **Step 1**: a simple closed curve on the Riemann sphere misses a point. -/
theorem exists_notMem_range_of_isSimpleClosedCurve {γ : ℝ → RiemannSphere}
    (hγ : IsSimpleClosedCurve γ) : ∃ p : RiemannSphere, p ∉ Set.range γ := by
  by_contra h
  push Not at h
  have hrange : Set.range γ = Set.univ := Set.eq_univ_iff_forall.mpr h
  have : interior (Set.range γ) = Set.univ := by rw [hrange, interior_univ]
  rw [interior_range_empty_of_isSimpleClosedCurve hγ] at this
  exact Set.univ_nonempty.ne_empty this.symm

/-- **Steps 2-3**: after conjugating by a homeomorphism of the sphere carrying a point off the curve
to `∞`, the curve is the sphere-image of a continuous, `2π`-periodic, injective plane curve. -/
theorem exists_planeCurve_conj {γ : ℝ → RiemannSphere} (hγ : IsSimpleClosedCurve γ) :
    ∃ (Φ : RiemannSphere ≃ₜ RiemannSphere) (γ' : ℝ → ℂ),
      Continuous γ' ∧ Function.Periodic γ' (2 * Real.pi) ∧
      Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) ∧ (∀ t : ℝ, Φ (γ t) = (γ' t : RiemannSphere)) := by
  obtain ⟨p, hp⟩ := exists_notMem_range_of_isSimpleClosedCurve hγ
  obtain ⟨Φ₀, hΦ₀⟩ := exists_homeomorph_infty_eq p
  refine ⟨Φ₀.symm, ?_⟩
  have hΦp : Φ₀.symm p = infty := by
    have h := Φ₀.symm_apply_apply infty
    rwa [hΦ₀] at h
  have hγ' : IsSimpleClosedCurve fun t : ℝ => Φ₀.symm (γ t) :=
    ⟨Φ₀.symm.continuous.comp hγ.1, fun t => by simp [hγ.2.1 t],
      fun t ht t' ht' h => hγ.2.2 ht ht' (Φ₀.symm.injective h)⟩
  have hinf : ∀ t : ℝ, Φ₀.symm (γ t) ≠ infty := by
    intro t h
    have : Φ₀.symm (γ t) = Φ₀.symm p := by rw [h, hΦp]
    exact hp ⟨t, Φ₀.symm.injective this⟩
  obtain ⟨γ', hc, hper, hinj, hlift⟩ := exists_planeCurve_of_avoids_infty hγ' hinf
  exact ⟨γ', hc, hper, hinj, fun t => hlift t⟩

/-- **Step 4**: apply the (proved) planar Jordan separation to the plane curve produced by the
conjugation. -/
theorem exists_separation_conj {γ : ℝ → RiemannSphere} (hγ : IsSimpleClosedCurve γ) :
    ∃ (Φ : RiemannSphere ≃ₜ RiemannSphere) (γ' : ℝ → ℂ) (hc : Continuous γ')
      (hper : Function.Periodic γ' (2 * Real.pi)) (hinj : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi))),
      (∀ t : ℝ, Φ (γ t) = (γ' t : RiemannSphere)) ∧
      Nonempty (Work.Smooth.Jordan.PlaneSeparation ⟨γ', hc, hper⟩) := by
  obtain ⟨Φ, γ', hc, hper, hinj, hlift⟩ := exists_planeCurve_conj hγ
  exact ⟨Φ, γ', hc, hper, hinj, hlift,
    nonempty_planeSeparation_of_continuous hc hper hinj⟩

end Work.Smooth.SphereJordan
