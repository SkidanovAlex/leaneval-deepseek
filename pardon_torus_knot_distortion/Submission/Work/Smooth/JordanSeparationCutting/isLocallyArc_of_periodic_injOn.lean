import Mathlib
import Submission.Work.Smooth.SphereJordan.localArcOfSphere
import Submission.Work.Smooth.SphereJordan.LocalArc.LocallyArcInPlane

/-!
# A `2π`-periodic injective parametrisation of the plane is locally an arc

A continuous map `γ : ℝ → ℂ` which is `2π`-periodic and injective on the half-open interval
`[0, 2π)` is a parametrisation of a circle: it descends to a continuous bijection
`AddCircle (2π) → Set.range γ`, which is a homeomorphism because `AddCircle (2π)` is compact and
`ℂ` is Hausdorff.  Since the circle is locally an arc, so is `Set.range γ`.

The proof is accordingly a sequence of transports of `IsLocallyArc`:

* `isLocallyArc_sphere'`  : `Metric.sphere w ρ` is locally an arc for `0 < ρ` (via the explicit
  injective parametrisation `Work.Smooth.SphereJordan.localArcOfSphere`);
* `isLocallyArc_circle'`  : `Circle` (the unit circle of `ℂ`) is locally an arc;
* `isLocallyArc_addCircle'` : `AddCircle (2π)` is locally an arc;
* `homeomorphAddCircle_of_periodic_injOn` : `AddCircle (2π) ≃ₜ ↥(Set.range γ)`.

Everything is developed self-contained in this file (the same facts also appear inline in
`Work.Smooth.JordanSeparationCutting.commonFrontier_isLocallyArc`, but this file does not depend on
it, so the two can be used interchangeably without a cycle).
-/

namespace Work.Smooth.JordanSeparationCutting

open Set Function
open scoped Topology

noncomputable section

/-! ## Local-arcness is a topological property -/

/-- **A space homeomorphic to a locally-arc space is locally an arc.** -/
private theorem isLocallyArc_of_homeomorph' {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (h : Work.Smooth.SphereJordan.IsLocallyArc X) :
    Work.Smooth.SphereJordan.IsLocallyArc Y := by
  intro y
  obtain ⟨c⟩ := h (e.symm y)
  refine ⟨{ V := e '' c.V
            isOpen_V := e.isOpenMap c.V c.isOpen_V
            mem_V := ⟨e.symm y, c.mem_V, by simp⟩
            homeo := c.homeo.trans (Homeomorph.image e c.V)
            homeo_zero := ?_ }⟩
  apply Subtype.ext
  show e ((c.homeo 0 : c.V) : X) = y
  rw [show ((c.homeo 0 : c.V) : X) = e.symm y from congrArg Subtype.val c.homeo_zero]
  simp

/-! ## The circle is locally an arc -/

/-- **A metric circle in the plane is locally an arc.** -/
private theorem isLocallyArc_sphere' {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥(Metric.sphere w ρ) := by
  refine Work.Smooth.SphereJordan.LocalArc.isLocallyArc_of_locallyArcInPlane ?_
  intro x hx
  obtain ⟨γ, hc, hinj, h0, himg⟩ :=
    Work.Smooth.SphereJordan.localArcOfSphere (w := w) (x := x) (ρ := ρ) (ε := ρ)
      hρ hρ hx (by linarith)
  exact ⟨ρ, γ, hρ, hc, hinj, h0, himg⟩

/-- **The unit circle `Circle ⊆ ℂ` is locally an arc.** -/
private theorem isLocallyArc_circle' : Work.Smooth.SphereJordan.IsLocallyArc Circle :=
  isLocallyArc_of_homeomorph'
    (Homeomorph.setCongr (Submonoid.coe_unitSphere ℂ).symm)
    (isLocallyArc_sphere' (w := 0) (ρ := 1) one_pos)

/-- **The additive circle `AddCircle (2π)` is locally an arc.** -/
private theorem isLocallyArc_addCircle' :
    Work.Smooth.SphereJordan.IsLocallyArc (AddCircle (2 * Real.pi)) := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact isLocallyArc_of_homeomorph'
    (AddCircle.homeomorphCircle (by positivity : (2 : ℝ) * Real.pi ≠ 0)).symm isLocallyArc_circle'

/-! ## A periodic injective curve parametrises a copy of the circle -/

/-- **A `2π`-periodic continuous injection on `[0, 2π)` is a homeomorphism of the circle onto its
trace.** -/
private theorem homeomorphAddCircle_of_periodic_injOn {C : Set ℂ} {γ : ℝ → ℂ}
    (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hrange : Set.range γ = C) :
    Nonempty (AddCircle (2 * Real.pi) ≃ₜ ↥C) := by
  classical
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  set F : AddCircle (2 * Real.pi) → ℂ := AddCircle.liftIco (2 * Real.pi) 0 γ with hFdef
  have hFapply : ∀ z : AddCircle (2 * Real.pi),
      F z = γ ((AddCircle.equivIco (2 * Real.pi) 0 z : ℝ)) := fun z => rfl
  have hFcont : Continuous F := by
    rw [hFdef]
    exact AddCircle.liftIco_continuous (by simpa using (hper 0).symm) hcont.continuousOn
  have hmem : ∀ z : AddCircle (2 * Real.pi), F z ∈ C := by
    intro z; rw [← hrange]; exact ⟨_, (hFapply z).symm⟩
  set ψ : AddCircle (2 * Real.pi) → ↥C := fun z => ⟨F z, hmem z⟩ with hψdef
  have hψcont : Continuous ψ := Continuous.subtype_mk hFcont hmem
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ Set.range γ := by rw [hrange]; exact hx
    obtain ⟨t, ht⟩ := hx'
    refine ⟨(t : AddCircle (2 * Real.pi)), ?_⟩
    apply Subtype.ext
    show F (t : AddCircle (2 * Real.pi)) = x
    rw [hFapply, ← ht]
    set r : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 (t : AddCircle (2 * Real.pi)) : ℝ) with hr
    have hcoe : (r : AddCircle (2 * Real.pi)) = (t : AddCircle (2 * Real.pi)) := by
      rw [hr]; exact AddCircle.coe_equivIco
    have hsub : ((r - t : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      rw [AddCircle.coe_sub, hcoe, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at hsub
    obtain ⟨n, hn⟩ := hsub
    have h2 : r - t = (n : ℝ) * (2 * Real.pi) := by simpa [zsmul_eq_mul] using hn.symm
    have hn' : r = t + (n : ℝ) * (2 * Real.pi) := by linarith
    rw [hn']
    exact hper.int_mul n t
  have hinj' : Function.Injective ψ := by
    intro z z' hzz'
    have h1 : F z = F z' := congrArg Subtype.val hzz'
    rw [hFapply, hFapply] at h1
    have hz : ((AddCircle.equivIco (2 * Real.pi) 0 z : ℝ)) ∈ Set.Ico 0 (2 * Real.pi) := by
      simpa using (AddCircle.equivIco (2 * Real.pi) 0 z).2
    have hz' : ((AddCircle.equivIco (2 * Real.pi) 0 z' : ℝ)) ∈ Set.Ico 0 (2 * Real.pi) := by
      simpa using (AddCircle.equivIco (2 * Real.pi) 0 z').2
    have h2 : ((AddCircle.equivIco (2 * Real.pi) 0 z : ℝ))
        = ((AddCircle.equivIco (2 * Real.pi) 0 z' : ℝ)) := hinj hz hz' h1
    rw [← AddCircle.coe_equivIco (p := 2 * Real.pi) (a := 0) (y := z),
      ← AddCircle.coe_equivIco (p := 2 * Real.pi) (a := 0) (y := z'), h2]
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ψ ⟨hinj', hsurj⟩) hψcont⟩

/-! ## The main statement -/

theorem isLocallyArc_of_periodic_injOn {C : Set ℂ} {γ : ℝ → ℂ}
    (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hrange : Set.range γ = C) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥C := by
  obtain ⟨e⟩ := homeomorphAddCircle_of_periodic_injOn hcont hper hinj hrange
  exact isLocallyArc_of_homeomorph' e isLocallyArc_addCircle'

end

end Work.Smooth.JordanSeparationCutting
