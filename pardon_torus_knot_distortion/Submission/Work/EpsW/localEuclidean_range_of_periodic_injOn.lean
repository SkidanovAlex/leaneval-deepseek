import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.LocallyArcInPlane
import Submission.Work.Smooth.SphereJordan.localArcOfSphere
import Submission.Work.Smooth.JordanSeparationCutting.isLocallyArc_of_periodic_injOn
import Submission.Work.Smooth.OneManifold.Plane.Basic

/-!
# A `2π`-periodic injective curve in `ℝ³` is locally Euclidean

A continuous map `γ : ℝ → ℝ³` which is `2π`-periodic and injective on the fundamental period
`[0, 2π)` descends to a continuous bijection `AddCircle (2π) → Set.range γ`, which is a
homeomorphism because `AddCircle (2π)` is compact and `ℝ³` is Hausdorff.  Since the additive circle
is locally an arc (transport of `Work.Smooth.SphereJordan.localArcOfSphere` from a metric circle in
`ℂ`), so is `Set.range γ`.

This is the `ℝ³` version of `Work.Smooth.JordanSeparationCutting.isLocallyArc_of_periodic_injOn`;
the proof is a verbatim transport, since the argument never uses anything special about `ℂ`.
-/

namespace Work.EpsW

open Set Function
open scoped Topology

noncomputable section

/-! ## The additive circle is locally an arc -/

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
private theorem isLocallyArc_circle' : Work.Smooth.SphereJordan.IsLocallyArc Circle := by
  have hset : (Submonoid.unitSphere ℂ : Set ℂ) = (Metric.sphere (0 : ℂ) 1 : Set ℂ) := by
    ext z
    rw [Metric.mem_sphere, dist_zero_right]
    simp [Submonoid.unitSphere]
  exact Work.Smooth.OneManifold.isLocallyArc_of_homeomorph (Homeomorph.setCongr hset)
    (isLocallyArc_sphere' (w := 0) (ρ := 1) one_pos)

/-- **The additive circle `AddCircle (2π)` is locally an arc.** -/
private theorem isLocallyArc_addCircle' :
    Work.Smooth.SphereJordan.IsLocallyArc (AddCircle (2 * Real.pi)) := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact Work.Smooth.OneManifold.isLocallyArc_of_homeomorph
    (AddCircle.homeomorphCircle (by positivity : (2 : ℝ) * Real.pi ≠ 0)).symm isLocallyArc_circle'

/-! ## A periodic injective curve parametrises a copy of the circle -/

open LeanEval.KnotTheory.PardonDistortion in
/-- **A `2π`-periodic continuous injection on `[0, 2π)` is a homeomorphism of the circle onto its
trace** in `ℝ³`. -/
private theorem homeomorphAddCircle_of_periodic_injOn {C : Set R3} {γ : ℝ → R3}
    (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hrange : Set.range γ = C) :
    Nonempty (AddCircle (2 * Real.pi) ≃ₜ ↥C) := by
  classical
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  set F : AddCircle (2 * Real.pi) → R3 := AddCircle.liftIco (2 * Real.pi) 0 γ with hFdef
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

open LeanEval.KnotTheory.PardonDistortion in
/-- The range of a continuous `2π`-periodic map `ℝ → ℝ³` which is injective on a fundamental period `[0, 2π)` is a topological `1`-manifold (locally Euclidean of dimension one).  This is the `ℝ³` version of `Work.Smooth.JordanSeparationCutting.isLocallyArc_of_periodic_injOn` (which is stated for `ℂ`); the proof is the same: the curve descends to a continuous bijection `AddCircle (2π) → Set.range γ`, which is a homeomorphism because `AddCircle (2π)` is compact and `ℝ³` is Hausdorff (`Continuous.homeoOfEquivCompactToT2`), and `AddCircle (2π)` is locally an arc (transport from the unit circle in `ℂ`, which is locally an arc via `Work.Smooth.SphereJordan.localArcOfSphere`). -/
theorem localEuclidean_range_of_periodic_injOn {γ : ℝ → R3}
    (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (Set.range γ) := by
  obtain ⟨e⟩ := homeomorphAddCircle_of_periodic_injOn hcont hper hinj rfl
  exact Work.Smooth.OneManifold.isLocallyArc_of_homeomorph e isLocallyArc_addCircle'

end

end Work.EpsW
