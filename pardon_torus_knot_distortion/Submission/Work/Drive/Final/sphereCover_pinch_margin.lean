import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_trace

/-!
# The pinch margin for a cover of spheres: two intersecting spheres are bounded away from `F`

`Work.Drive.Final.sphereCover_pinch_margin` is the separation statement used to control the
distance between the *pinch* locus of a cover of embedded spheres and the surface
`F = (Work.Drive.EpsSphere.torusOf ψ).carrier`.

The hypotheses are the natural ones: the `Ss i` are embedded spheres (`i : Fin m`) and their
traces on `F` are pairwise disjoint.  The conclusion is that the intersection points of two
distinct spheres stay a *positive* Euclidean distance `η` away from `F` (and `η` can be chosen
uniformly in the pair).

The mathematics is:

* each embedded sphere is the continuous image of the compact unit sphere, hence compact;
* the set `B` of points lying in two distinct spheres is therefore compact;
* by hypothesis `B` is disjoint from `F = P.carrier`, which is closed;
* a compact set and a *closed* disjoint set are separated: the (continuous) function
  `x ↦ infDist x F` is strictly positive on the compact set `B`, so by the extreme value theorem
  (`IsCompact.exists_forall_le'`) it admits a strictly positive lower bound `η` on `B`.

Indeed `0 < infDist x F ≤ dist x z` for every `z ∈ F`, which is exactly the required estimate.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

/-- **A compact set and a disjoint closed set are separated by a positive distance.**

If `B` is compact, `T` is closed and nonempty, and `B ∩ T = ∅`, then there is `η > 0` with
`η ≤ dist x z` for all `x ∈ B` and `z ∈ T`.

The proof is the extreme value theorem applied to the continuous function `x ↦ infDist x T`:
it is strictly positive at every point of the compact set `B` (as `B` misses the closed set `T`)
and the bound is read off with `infDist x T ≤ dist x z`. -/
lemma exists_pos_le_dist_of_isCompact_disjoint {B T : Set R3} (hB : IsCompact B)
    (hT : IsClosed T) (hTne : T.Nonempty) (hd : Disjoint B T) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ B, ∀ z ∈ T, η ≤ dist x z := by
  obtain ⟨η, hηpos, hη⟩ := hB.exists_forall_le' (f := fun x => Metric.infDist x T)
    (Metric.continuous_infDist_pt T).continuousOn
    (fun x hx => (hT.notMem_iff_infDist_pos hTne).mp ((Set.disjoint_left.mp hd) hx))
  exact ⟨η, hηpos, fun x hx z hz => (hη x hx).trans (Metric.infDist_le_dist_of_mem hz)⟩

/-- **The pinch margin.**  If `Ss` is a finite family of embedded spheres whose traces on the
torus `F = (Work.Drive.EpsSphere.torusOf ψ).carrier` are pairwise disjoint, then the points lying
in two *different* spheres are a positive distance `η` away from auniformly in the pair:

`∃ η > 0, ∀ i ≠ j, ∀ x ∈ Ss i ∩ Ss j, ∀ z ∈ F, η ≤ dist x z`.

This is what lets the pinching deformations be chosen small enough not to create new
intersections of the spheres with `F`. -/
theorem sphereCover_pinch_margin {ψ : Submission.Diffeo} {m : ℕ} {Ss : Fin m → Set R3}
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      (Ss j ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) :
    ∃ η : ℝ, 0 < η ∧ ∀ i j : Fin m, i ≠ j → ∀ x : R3, x ∈ (Ss i ∩ Ss j) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → η ≤ dist x z := by
  classical
  -- each embedded sphere is compact
  have hcomp_i : ∀ i, IsCompact (Ss i) := by
    intro i
    obtain ⟨e, -, he⟩ := hsph i
    rw [← he]
    exact isCompact_range e.continuous
  -- the set of points lying in two distinct spheres
  set B : Set R3 := ⋃ q : {q : Fin m × Fin m // q.1 ≠ q.2}, Ss q.1.1 ∩ Ss q.1.2 with hBdef
  have hBcomp : IsCompact B := by
    rw [hBdef]
    exact isCompact_iUnion (fun q => (hcomp_i q.1.1).inter (hcomp_i q.1.2))
  have hBsub : ∀ i j (hij : i ≠ j) x, x ∈ Ss i ∩ Ss j → x ∈ B := by
    intro i j hij x hx
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, hx⟩
  -- `B` is disjoint from the surface, by hypothesis
  have hBdisj : Disjoint B (Work.Drive.EpsSphere.torusOf ψ).carrier := by
    rw [Set.disjoint_left]
    intro x hxB hxT
    rw [hBdef, Set.mem_iUnion] at hxB
    obtain ⟨q, hq⟩ := hxB
    exact (Set.disjoint_left.mp (hdisj q.1.1 q.1.2 q.2)) ⟨hq.1, hxT⟩ ⟨hq.2, hxT⟩
  have hTclosed : IsClosed (Work.Drive.EpsSphere.torusOf ψ).carrier :=
    Work.CoreTopology.isClosed_carrier _
  have hTne : (Work.Drive.EpsSphere.torusOf ψ).carrier.Nonempty :=
    ⟨_, Work.CoreTopology.ParamTorus.psi_mem_carrier _ 0 0⟩
  obtain ⟨η, hηpos, hη⟩ := exists_pos_le_dist_of_isCompact_disjoint hBcomp hTclosed hTne hBdisj
  exact ⟨η, hηpos, fun i j hij x hx z hz => hη x (hBsub i j hij x hx) z hz⟩

end Work.Drive.Final
