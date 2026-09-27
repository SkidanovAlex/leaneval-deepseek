import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.PL.Defs

namespace Work.Engulf.Auxi

/-- A fine independent cover of a single simplex.  If `t ⊆ ℝⁿ` is a finite affinely independent
vertex set with at most `p + 1` vertices and `T` is the subdivision toolkit
(`Work.Engulf.SubdivTools`: iterated subdivision, finiteness, space preservation, dimension, mesh,
shelling), then for every `ν > 0` there is a finite family `G` of faces of some subdivision
`T.sdIter r K` of the standard simplex on `t`, each face nonempty, affinely independent, with at
most `p + 1` vertices, contained in `PL.simp t` and of vertex diameter `< ν`, that covers
`PL.simp t` (the case `t = ∅` gives `G = ∅`).  Suggested proof: let `K` be the complex whose faces
are the nonempty subsets of `t` (e.g. `Geometry.SimplicialComplex.ofErase {s | s ⊆ t}` with
`indep` from `AffineIndependent.mono` on `hind`, down-closure of the powerset, and the glueing axiom
from `AffineIndependent.convexHull_inter`); `K.faces.Finite` because faces are subsets of `t`,
`PL.DimLE K p` because they have at most `t.card ≤ p + 1` vertices, and `K.space = PL.simp t`
(using `t ∈ K.faces` when `t ≠ ∅`).  Take `r` from `T.fine K hK ν hν` and set
`G := (T.fin r K hK).toFinset`; then use `T.dimle`, `T.subdiv` (space and carrier property) and
`Geometry.SimplicialComplex.nonempty_of_mem_faces` / `Geometry.SimplicialComplex.indep`. -/
theorem fine_cover_simplex {n p : ℕ} (T : Work.Engulf.SubdivTools n) {t : Finset (PL.E n)}
    (hind : AffineIndependent ℝ (fun v : ↥t => (v : PL.E n))) (hcard : t.card ≤ p + 1)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ G : Finset (Finset (PL.E n)),
      (∀ τ ∈ G, τ.Nonempty ∧ AffineIndependent ℝ (fun v : ↥τ => (v : PL.E n)) ∧
        τ.card ≤ p + 1 ∧ PL.simp τ ⊆ PL.simp t ∧ ∀ v ∈ τ, ∀ w ∈ τ, dist v w < ν) ∧
      PL.simp t ⊆ ⋃ τ ∈ G, PL.simp τ := by
  classical
  -- The complex whose faces are the nonempty subsets of `t`.
  let K : PL.Cx n :=
    { faces := {s : Finset (PL.E n) | s ⊆ t ∧ s.Nonempty}
      isRelLowerSet_faces := by
        intro s hs
        exact ⟨hs.2, fun r hr hrn => ⟨hr.trans hs.1, hrn⟩⟩
      indep := by
        intro s hs
        exact hind.mono (Finset.coe_subset.mpr hs.1)
      inter_subset_convexHull := by
        intro s u hs hu
        exact (hind.convexHull_inter hs.1 hu.1).ge }
  have hmem : ∀ s : Finset (PL.E n), s ∈ K.faces ↔ s ⊆ t ∧ s.Nonempty := fun s => Iff.rfl
  -- Finitely many faces: they are subsets of the finite set `t`.
  have hK : K.faces.Finite := by
    refine (t.powerset.finite_toSet).subset ?_
    rintro s ⟨hs, -⟩
    simpa using hs
  -- All faces have at most `t.card ≤ p + 1` vertices.
  have hdim : PL.DimLE K p := by
    intro s hs
    have hst : s ⊆ t := ((hmem s).mp hs).1
    exact le_trans (Finset.card_le_card hst) hcard
  -- A sufficiently fine iterated subdivision.
  obtain ⟨r, hr⟩ := T.fine K hK ν hν
  refine ⟨(T.fin r K hK).toFinset, ?_, ?_⟩
  · intro τ hτ
    rw [Set.Finite.mem_toFinset] at hτ
    refine ⟨(T.sdIter r K hK).nonempty_of_mem_faces hτ, (T.sdIter r K hK).indep hτ,
      T.dimle r K hK p hdim τ hτ, ?_, ?_⟩
    · -- `τ` lies in a coarse face `s ⊆ t`.
      obtain ⟨s, hs, hsub⟩ := (T.subdiv r K hK).2 τ hτ
      exact hsub.trans (simp_mono ((hmem s).mp hs).1)
    · -- vertex diameter, from the mesh bound.
      intro v hv w hw
      exact hr r le_rfl τ hτ v hv w hw
  · -- the subdivision covers the simplex.
    intro x hx
    have hsub : PL.simp t ⊆ K.space := by
      rcases t.eq_empty_or_nonempty with ht | ht
      · rw [ht] at hx
        simp at hx
      · exact K.convexHull_subset_space ⟨le_refl t, ht⟩
    have hx' : x ∈ (T.sdIter r K hK).space := by
      rw [(T.subdiv r K hK).1]; exact hsub hx
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr
      ⟨(T.fin r K hK).mem_toFinset.mpr hs, hxs⟩⟩

end Work.Engulf.Auxi
