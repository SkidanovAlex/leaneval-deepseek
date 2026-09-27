import Mathlib
import Submission.Work.PL.Defs

/-!
# Gluing a maximal family of affinely independent vertex sets into a simplicial complex

`exists_cx_of_maximal`: if `V : ι → Finset (E N)` is a finite family of affinely independent
vertex sets such that the convex hulls of the `V i` meet exactly in the convex hull of the
pairwise intersections (the "glue nicely" condition), then the collection

`{s | s.Nonempty ∧ ∃ i, s ⊆ V i}`

of all nonempty subsets of the individual vertex sets is the face set of a geometric simplicial
complex `K : PL.Cx N`.  This is the abstract gluing step of the Freudenthal/Kuhn subdivision of a
cube: the cells of a grid, listed with their vertex sets, glue to a triangulation.

The key point is the standard uniqueness-of-barycentric-coordinates fact: inside a single
affinely independent set, two faces meet exactly in the face spanned by the intersection of
their vertex sets.  Mathlib provides it as `AffineIndependent.convexHull_inter`; the glueing
condition `hinter` reduces the general two-index case to two applications of it (first against
`V i`, then against `V j`).
-/

namespace Work.PL.Subdiv.Cube

open Set

/-- **Faces of one simplex glue nicely.**  If `U` is an affinely independent set of points and
`s, t ⊆ U`, then the simplices spanned by `s` and `t` meet exactly in the simplex spanned by
`s ∩ t`. -/
lemma convexHull_inter_eq_of_affineIndependent {N : ℕ} {U s t : Finset (PL.E N)}
    (hU : AffineIndependent ℝ ((↑) : ↥U → PL.E N)) (hs : s ⊆ U) (ht : t ⊆ U) :
    convexHull ℝ (s : Set (PL.E N)) ∩ convexHull ℝ (t : Set (PL.E N)) =
      convexHull ℝ ((s ∩ t : Finset (PL.E N)) : Set (PL.E N)) := by
  rw [Finset.coe_inter]
  exact (AffineIndependent.convexHull_inter hU hs ht).symm

/-- **Membership form** of `convexHull_inter_eq_of_affineIndependent`. -/
lemma mem_convexHull_inter_of_affineIndependent {N : ℕ} {U s t : Finset (PL.E N)}
    (hU : AffineIndependent ℝ ((↑) : ↥U → PL.E N)) (hs : s ⊆ U) (ht : t ⊆ U)
    {x : PL.E N} (hx : x ∈ convexHull ℝ (s : Set (PL.E N)))
    (hy : x ∈ convexHull ℝ (t : Set (PL.E N))) :
    x ∈ convexHull ℝ ((s ∩ t : Finset (PL.E N)) : Set (PL.E N)) := by
  rw [← convexHull_inter_eq_of_affineIndependent hU hs ht]
  exact ⟨hx, hy⟩

/-- **The face set of a maximal family of affinely independent vertex sets.**  Given a finite
family `V : ι → Finset (E N)` of affinely independent vertex sets whose convex hulls glue nicely
(`hinter`), the nonempty subsets of the individual `V i` are the faces of a geometric simplicial
complex. -/
theorem exists_cx_of_maximal {N : ℕ} {ι : Type*} [Fintype ι] (V : ι → Finset (PL.E N))
    (hV : ∀ i, AffineIndependent ℝ ((↑) : ↥(V i) → PL.E N))
    (hinter : ∀ i j, convexHull ℝ ((V i ∩ V j : Finset (PL.E N)) : Set (PL.E N)) =
      convexHull ℝ (V i : Set (PL.E N)) ∩ convexHull ℝ (V j : Set (PL.E N))) :
    ∃ K : PL.Cx N, K.faces = {s : Finset (PL.E N) | s.Nonempty ∧ ∃ i, s ⊆ V i} := by
  classical
  refine ⟨{ faces := {s : Finset (PL.E N) | s.Nonempty ∧ ∃ i, s ⊆ V i}
            isRelLowerSet_faces := ?_
            indep := ?_
            inter_subset_convexHull := ?_ }, rfl⟩
  · -- downward closure: a nonempty subset of a subset of `V i` is still a nonempty subset of `V i`
    rintro s ⟨hsne, i, hsi⟩
    exact ⟨hsne, fun b hbs hbne => ⟨hbne, i, hbs.trans hsi⟩⟩
  · -- affine independence: a subset of an affinely independent set is affinely independent
    rintro s ⟨-, i, hsi⟩
    exact (hV i).mono (by simpa using hsi)
  · -- glueing: `conv s ∩ conv t ⊆ conv (s ∩ t)` for `s ⊆ V i`, `t ⊆ V j`
    rintro s t ⟨-, i, hsi⟩ ⟨-, j, htj⟩ x ⟨hxs, hxt⟩
    rw [← Finset.coe_inter]
    have hi : x ∈ convexHull ℝ ((V i : Finset (PL.E N)) : Set (PL.E N)) :=
      convexHull_mono (Finset.coe_subset.mpr hsi) hxs
    have hj : x ∈ convexHull ℝ ((V j : Finset (PL.E N)) : Set (PL.E N)) :=
      convexHull_mono (Finset.coe_subset.mpr htj) hxt
    -- `x` lies in the convex hull of the common part `V i ∩ V j`
    have h1 : x ∈ convexHull ℝ ((V i ∩ V j : Finset (PL.E N)) : Set (PL.E N)) := by
      rw [hinter i j]
      exact ⟨hi, hj⟩
    -- inside `V i`, the faces `s` and `V i ∩ V j` meet in the face `s ∩ (V i ∩ V j)`
    have h2 : x ∈ convexHull ℝ (((s ∩ (V i ∩ V j)) : Finset (PL.E N)) : Set (PL.E N)) := by
      rw [← convexHull_inter_eq_of_affineIndependent (U := V i) (s := s) (t := V i ∩ V j)
        (hV i) hsi Finset.inter_subset_left]
      exact ⟨hxs, h1⟩
    -- and inside `V j`, that face meets `t` in `s ∩ t`
    have h3 : x ∈ convexHull ℝ (((s ∩ (V i ∩ V j)) ∩ t : Finset (PL.E N)) : Set (PL.E N)) := by
      rw [← convexHull_inter_eq_of_affineIndependent (U := V j) (s := s ∩ (V i ∩ V j)) (t := t)
        (hV j) (Finset.Subset.trans Finset.inter_subset_right Finset.inter_subset_right) htj]
      exact ⟨h2, hxt⟩
    have hst : (s ∩ (V i ∩ V j)) ∩ t = s ∩ t := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hys, _⟩, hyt⟩
        exact ⟨hys, hyt⟩
      · rintro ⟨hys, hyt⟩
        exact ⟨⟨hys, hsi hys, htj hyt⟩, hyt⟩
    rwa [hst] at h3

end Work.PL.Subdiv.Cube
