import Mathlib
import Submission.Work.Cohomology.CompactComplDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The complement of a point in the one-point compactification of `ℝ^N`

The one-point compactification `OnePointSpace N = OnePoint (ℝ^N)` is homeomorphic to the unit
sphere `S^N ⊆ ℝ^{N+1}`, and the complement of any point of `S^N` is homeomorphic to `ℝ^N` via
stereographic projection.  Consequently the complement of *any* point of `OnePointSpace N` is
homeomorphic to `ℝ^N`.

* `Work.Cohomology.sphere_compl_point_homeo` — complement of a point of the unit sphere;
* `Work.Cohomology.onePointSpace_compl_point_homeo` — complement of a point of `OnePointSpace N`.
-/

namespace Work.Cohomology

/-- The complement of a point of the unit sphere `S^N ⊆ ℝ^{N+1}` is homeomorphic to `ℝ^N`
(stereographic projection). -/
theorem sphere_compl_point_homeo (N : ℕ)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) :
    Nonempty (↥({v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin N)) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (N + 1))) = N + 1) := ⟨by simp⟩
  have hA : (stereographic' N v).source =
      ({v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1)) := by simp
  have hB : (stereographic' N v).target = (Set.univ : Set (EuclideanSpace ℝ (Fin N))) := by simp
  exact ⟨(Homeomorph.setCongr hA).symm.trans
    ((stereographic' N v).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr hB).trans (Homeomorph.Set.univ _)))⟩

/-- The complement of any point of the one-point compactification of `ℝ^N` is homeomorphic to
`ℝ^N`. -/
theorem onePointSpace_compl_point_homeo (N : ℕ) (hN : 1 ≤ N) (q : OnePointSpace N) :
    Nonempty (↥({q}ᶜ : Set (OnePointSpace N)) ≃ₜ EuclideanSpace ℝ (Fin N)) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (N + 1))) = N + 1) := ⟨by simp⟩
  let e : OnePointSpace N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin N)) (ι := Fin (N + 1)) (by simp)
  have h1 : ↥({q}ᶜ : Set (OnePointSpace N)) ≃ₜ
      ↥({e q}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1)) :=
    e.subtype (fun x => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact not_congr e.injective.eq_iff.symm)
  obtain ⟨h2⟩ := sphere_compl_point_homeo N (e q)
  exact ⟨h1.trans h2⟩

end Work.Cohomology
