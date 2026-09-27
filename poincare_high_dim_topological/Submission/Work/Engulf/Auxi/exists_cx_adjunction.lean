import Mathlib
import Submission.Work.PL.Defs

/-!
# Adjunction of a single simplex to a finite simplicial complex

Given a finite geometric simplicial complex `Γ` in `ℝᴺ` and a finitely many vertices `Δ'`
spanning a simplex whose convex hull is disjoint from `Γ.space`, we may glue `Δ'` onto `Γ`
along nothing: the resulting complex `Γ'` has faces `Γ.faces` together with all nonempty
subsets of `Δ'`, and its underlying space is `Γ.space ∪ simp Δ'`.

This is the elementary "cell attachment" step of the engulfing argument: attaching a
simplex that misses the current complex.
-/

open Set

namespace Work.Engulf.Aux

theorem exists_cx_adjunction {N : ℕ} (Γ : PL.Cx N) (hfin : Γ.faces.Finite) (Δ' : Finset (PL.E N))
    (hind : AffineIndependent ℝ (fun v : ↥Δ' => (v : PL.E N)))
    (hne : Δ'.Nonempty) (hdisj : PL.simp Δ' ∩ Γ.space = ∅) :
    ∃ Γ' : PL.Cx N, Γ'.faces.Finite ∧ Γ.faces ⊆ Γ'.faces ∧ Δ' ∈ Γ'.faces ∧
      (∀ t ∈ Γ'.faces, t ∈ Γ.faces ∨ t ⊆ Δ') ∧ Γ'.space = Γ.space ∪ PL.simp Δ' := by
  classical
  -- The set of faces of the attached simplex: the nonempty subsets of `Δ'`.
  let S : Set (Finset (PL.E N)) := { t | t ⊆ Δ' ∧ t.Nonempty }
  have hS : IsRelLowerSet S Finset.Nonempty := by
    intro a ha
    exact ⟨ha.2, fun b hba hb => ⟨hba.trans ha.1, hb⟩⟩
  -- Every subset of an affinely independent set is affinely independent.
  have hind_sub : ∀ u : Finset (PL.E N), u ⊆ Δ' →
      AffineIndependent ℝ (Subtype.val : ↥u → PL.E N) := by
    intro u hu
    exact hind.comp_embedding (⟨fun v : ↥u => ⟨(v : PL.E N), hu v.2⟩,
      fun a b hab => Subtype.ext (congrArg (fun x : ↥Δ' => (x : PL.E N)) hab)⟩ : ↥u ↪ ↥Δ')
  -- Faces glue nicely: either both are old faces, the intersection is empty (disjointness
  -- of the new simplex from `Γ`), or both lie inside the affinely independent simplex `Δ'`.
  have hinter : ∀ {s t : Finset (PL.E N)}, s ∈ Γ.faces ∪ S → t ∈ Γ.faces ∪ S →
      convexHull ℝ (s : Set (PL.E N)) ∩ convexHull ℝ (t : Set (PL.E N)) ⊆
        convexHull ℝ ((s : Set (PL.E N)) ∩ (t : Set (PL.E N))) := by
    intro s t hs ht
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · exact Γ.inter_subset_convexHull hs ht
      · have h1 : convexHull ℝ (s : Set _) ∩ convexHull ℝ (t : Set _) ⊆
            (∅ : Set (PL.E N)) := by
          rw [← hdisj]
          intro x hx
          exact ⟨convexHull_mono (Finset.coe_subset.mpr ht.1) hx.2,
            Γ.convexHull_subset_space hs hx.1⟩
        exact h1.trans (Set.empty_subset _)
    · rcases ht with ht | ht
      · have h1 : convexHull ℝ (s : Set _) ∩ convexHull ℝ (t : Set _) ⊆
            (∅ : Set (PL.E N)) := by
          rw [← hdisj]
          intro x hx
          exact ⟨convexHull_mono (Finset.coe_subset.mpr hs.1) hx.1,
            Γ.convexHull_subset_space ht hx.2⟩
        exact h1.trans (Set.empty_subset _)
      · have h := AffineIndependent.convexHull_inter' (R := ℝ) (t₁ := s) (t₂ := t)
          (hind_sub (s ∪ t) (Finset.union_subset hs.1 ht.1))
        rw [← h]
  -- The glued complex.
  let Γ' : PL.Cx N :=
    { faces := Γ.faces ∪ S
      indep := fun {s} hs => hs.elim (fun h => Γ.indep h) (fun h => hind_sub s h.1)
      isRelLowerSet_faces := Γ.isRelLowerSet_faces.union hS
      inter_subset_convexHull := fun {s t} hs ht => hinter hs ht }
  have hfinS : S.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (Δ'.powerset))
    intro t ht
    exact Finset.mem_powerset.mpr ht.1
  have hspace : Γ'.space = Γ.space ∪ PL.simp Δ' := by
    show (⋃ s ∈ Γ.faces ∪ S, convexHull ℝ (s : Set (PL.E N))) = Γ.space ∪ PL.simp Δ'
    rw [Geometry.SimplicialComplex.space, PL.simp, Set.biUnion_union]
    congr 1
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun s (hs : s ∈ S) => convexHull_mono (Finset.coe_subset.mpr hs.1)
    · exact Set.subset_biUnion_of_mem
        (u := fun s : Finset (PL.E N) => convexHull ℝ (s : Set (PL.E N)))
        (show Δ' ∈ S from ⟨subset_refl Δ', hne⟩)
  refine ⟨Γ', ?_, ?_, ?_, ?_, hspace⟩
  · show (Γ.faces ∪ S).Finite
    exact hfin.union hfinS
  · exact Set.subset_union_left
  · exact Or.inr ⟨subset_refl Δ', hne⟩
  · intro t ht
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr h.1

end Work.Engulf.Aux
