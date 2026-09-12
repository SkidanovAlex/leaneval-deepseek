import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_smear_dissection
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace

open Set Filter
open scoped Topology Convex Pointwise BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

/-- The smear `P + [0,1]·v` of a full-dimensional polytope is the union of `P`
with the prisms over the `v`-forward top faces `topFace w P` (with `w ≠ 0` and
`0 ≤ ⟪w, v⟫`); any two pieces meet with empty interior. -/
theorem polytope_smear_dissection_normal
    (n : ℕ) (u : Finset (EuclideanSpace ℝ (Fin n))) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP : P = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin n))))
    (hint : (interior P).Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ Q : ι → ConvexBody (EuclideanSpace ℝ (Fin n)),
      (∀ i : ι, ∃ w : EuclideanSpace ℝ (Fin n), w ≠ 0 ∧ 0 ≤ inner ℝ w v ∧
        ((Q i : Set (EuclideanSpace ℝ (Fin n))) =
          {x : EuclideanSpace ℝ (Fin n) | ∃ f : EuclideanSpace ℝ (Fin n), f ∈ topFace w P ∧
            ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v})) ∧
      ({x : EuclideanSpace ℝ (Fin n) | ∃ p : EuclideanSpace ℝ (Fin n), p ∈ P ∧
          ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v} =
        P ∪ ⋃ i : ι, (Q i : Set (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ i : ι, interior (P ∩ (Q i : Set (EuclideanSpace ℝ (Fin n)))) = ∅) ∧
      (∀ i j : ι, i ≠ j → interior ((Q i : Set (EuclideanSpace ℝ (Fin n))) ∩ (Q j : Set (EuclideanSpace ℝ (Fin n)))) = ∅) := by
  classical
  let E : Type := EuclideanSpace ℝ (Fin n)
  let fam : Set (Set E) := {F : Set E | F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
      ∃ w : E, w ≠ 0 ∧ F = topFace w P ∧ 0 ≤ inner ℝ w v}
  have hfam_sub : fam ⊆ {F : Set E | IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P} := by
    intro F hF
    exact ⟨hF.2.1, hF.1, hF.2.2.1⟩
  have hfam_fin : fam.Finite := (finite_exposedFaces_convexHull n u P hP).subset hfam_sub
  let ι : Type := {F : Set E // F ∈ fam}
  haveI : Fintype ι := hfam_fin.fintype
  have hPcvx : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set E)
  have hPcpt : IsCompact P := by
    rw [hP]
    exact (Finset.finite_toSet u).isCompact_convexHull ℝ
  have faceConv : ∀ F : Set E, F ∈ fam → Convex ℝ F := by
    intro F hF
    exact (hF.2.1).convex hPcvx
  have faceCpt : ∀ F : Set E, F ∈ fam → IsCompact F := by
    intro F hF
    rcases hF with ⟨hFne, hFexp, hFneP, hFw⟩
    have hFcv := polytope_exposedFace_conv_vertices n u P hP hFexp hFne
    rw [hFcv]
    exact ((Finset.finite_toSet u).subset (by intro x hx; exact hx.2)).isCompact_convexHull ℝ
  let Q : ι → ConvexBody E := fun i => prismBody (faceConv i.1 i.2) (faceCpt i.1 i.2) (i.2).1 v
  have hQco : ∀ i : ι, (Q i : Set E) = prismSet (i.1 : Set E) v := by
    intro i
    simp [Q, prismBody_coe]
  -- (c) each piece meets P with empty interior
  have hinterP : ∀ i : ι, interior (P ∩ (Q i : Set E)) = ∅ := by
    intro i
    rcases (i.2) with ⟨hFne, hFexp, hFneP, hFw⟩
    rcases hFw with ⟨w, hw0, hFw, hwv⟩
    rw [hQco i]
    exact interior_inter_prismSet_topFace_eq_empty (P := P) (F := (i.1 : Set E)) (n := w) (v := v)
      hFw hw0 hwv hFne
  -- (d) distinct pieces meet with empty interior
  have hpair : ∀ i j : ι, i ≠ j → interior ((Q i : Set E) ∩ (Q j : Set E)) = ∅ := by
    intro i j hij
    have hface_ne : (i.1 : Set E) ≠ j.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    rcases (i.2) with ⟨hFne, hFexp, hFneP, hFw⟩
    rcases hFw with ⟨w, hw0, hFw, hwv⟩
    rcases (j.2) with ⟨hGne, hGexp, hGneP, hGw⟩
    rcases hGw with ⟨m, hm0, hGm, hmv⟩
    rw [hQco i, hQco j]
    exact interior_inter_prismSet_prismSet_eq_empty (P := P) (F := (i.1 : Set E)) (G := (j.1 : Set E))
      (n := w) (m := m) (v := v) hFw hGm hw0 hm0 hwv hmv hFne hGne hface_ne
  -- (b) the union identity
  have hsub_union : P ∪ ⋃ i : ι, (Q i : Set E) ⊆ smearSet P v := by
    apply Set.union_subset
    · intro x hx
      exact subset_smearSet_of_mem hx
    · apply Set.iUnion_subset
      intro i
      rw [hQco i]
      exact subset_smearSet_prism (P := P) (F := (i.1 : Set E)) (v := v) ((i.2).2.1.subset)
  have hcover : smearSet P v ⊆ P ∪ ⋃ i : ι, (Q i : Set E) := by
    intro x hxS
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    · right
      rcases local_cover (P := P) hPcvx hPcpt v x hxS hxP with ⟨w, hw0, hwv, f, hf, t, ht, hxeq⟩
      let Fw : Set E := topFace w P
      have hFw_exp : IsExposed ℝ P Fw := by
        simpa [Fw] using isExposed_topFace w P
      have hFw_ne : Fw.Nonempty := ⟨f, hf⟩
      have hFw_pp : Fw ≠ P := by
        exact topFace_ne_P_of_ne_zero (P := P) hint hw0
      have hFw_mem : Fw ∈ fam := by
        change Fw.Nonempty ∧ IsExposed ℝ P Fw ∧ Fw ≠ P ∧
          ∃ w' : E, w' ≠ 0 ∧ Fw = topFace w' P ∧ 0 ≤ inner ℝ w' v
        exact ⟨hFw_ne, hFw_exp, hFw_pp, w, hw0, rfl, hwv⟩
      let i : ι := ⟨Fw, hFw_mem⟩
      have hxQi : x ∈ (Q i : Set E) := by
        rw [hQco i]
        change x ∈ prismSet Fw v
        exact ⟨f, hf, t, ht, hxeq⟩
      exact Set.mem_iUnion.mpr ⟨i, hxQi⟩
  have hunion : smearSet P v = P ∪ ⋃ i : ι, (Q i : Set E) :=
    Subset.antisymm hcover hsub_union
  refine ⟨ι, hfam_fin.fintype, Q, ?_, ?_, ?_, ?_⟩
  · -- each piece is the prism over a forward top face, translated to the literal E type
    intro i
    rcases (i.2).2.2.2 with ⟨w, hw0, hFw, hwv⟩
    refine ⟨w, hw0, hwv, ?_⟩
    change (Q i : Set (EuclideanSpace ℝ (Fin n))) =
      {x : EuclideanSpace ℝ (Fin n) | ∃ f : EuclideanSpace ℝ (Fin n), f ∈ topFace w P ∧
        ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v}
    rw [hQco i]
    change prismSet (i.1 : Set E) v = prismSet (topFace w P) v
    rw [hFw]
  · -- union identity
    change {x : EuclideanSpace ℝ (Fin n) | ∃ p : EuclideanSpace ℝ (Fin n), p ∈ P ∧
        ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v} =
      P ∪ ⋃ i : ι, (Q i : Set (EuclideanSpace ℝ (Fin n)))
    simpa [E, smearSet] using hunion
  · intro i
    change interior (P ∩ (Q i : Set (EuclideanSpace ℝ (Fin n)))) = ∅
    simpa [E] using hinterP i
  · intro i j hij
    change interior ((Q i : Set (EuclideanSpace ℝ (Fin n))) ∩ (Q j : Set (EuclideanSpace ℝ (Fin n)))) = ∅
    simpa [E] using hpair i j hij

end

end Commons.Geometry.Convex.Hadwiger
