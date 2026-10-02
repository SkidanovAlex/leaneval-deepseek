import Mathlib
import Submission.Work.Orient.Port.Hatcher

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PORT: the gluing lemma over a finite cover by coordinate balls

A **snapshot** of `Submission/Work/ThomBordism/localGenAux2.lean` (from the THOM area), copied into
the ORIENT area under the namespace `Work.Orient.Port` so that
`Submission/Work/Orient/Closed.lean` does not depend on a file under active development elsewhere.
The mathematical content is `Work.Orient.Port.coverGlue` (using `Work.Orient.Port.compactZero` from
`Submission/Work/Orient/Port/Hatcher.lean`): classes over coordinate balls which agree at every point
of the pairwise intersections are the restrictions of a single class on the union.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

open Work.ThomBordism

namespace Work.Orient.Port

noncomputable section

variable {n : ℕ}

/-- Restriction commutes with a transport of the excluded sets (auxiliary port of
`Work.Orient.resRelH_eqToIso`, reproduced here to keep the port self-contained). -/
theorem resRelH_aux {M : TopCat} {n : ℕ} {B B' D D' : Set M} (hB : B = B') (hD : D = D')
    (h : D ⊆ B) (h' : D' ⊆ B') (v : RelH M n B) :
    RelHmap M n h' ((eqToIso (congrArg (fun S : Set M => RelH M n S) hB)).hom v)
      = (eqToIso (congrArg (fun S : Set M => RelH M n S) hD)).hom (RelHmap M n h v) := by
  subst hB
  subst hD
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.id_apply,
    RelHmap_congr_h M n h' h]

/-- The transport of a dependent family of classes along an equality of the index. -/
theorem eqToIso_congrArg_apply {M : TopCat} {n : ℕ} {ι : Type} {K : ι → Set M}
    (ζ : ∀ i, RelH M n (K i))
    {i j : ι} (h : i = j) :
    (eqToIso (congrArg (fun S : Set M => RelH M n S) (congrArg K h))).hom (ζ i) = ζ j := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.id_apply]

/-- **Gluing over a finite cover by coordinate balls**: classes which agree at every point of the
pairwise intersections are the restrictions of a single class on the union. -/
theorem coverGlue (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {ι : Type} (s : Finset ι) (K : ι → Set M)
    (hK : ∀ i ∈ s, IsCoordBall n M (K i)) (ζ : ∀ i, RelH M n (K i))
    (hglue : ∀ i ∈ s, ∀ j ∈ s, ∀ (x : M) (hx : x ∈ K i ∩ K j),
      RelHmap M n (Set.singleton_subset_iff.mpr hx.1) (ζ i)
        = RelHmap M n (Set.singleton_subset_iff.mpr hx.2) (ζ j)) :
    ∃ γ : RelH M n (⋃ i ∈ s, K i), ∀ (i : ι) (hi : i ∈ s),
      RelHmap M n (Set.subset_biUnion_of_mem hi) γ = ζ i := by
  classical
  have key : ∀ t : Finset ι, (∀ i ∈ t, IsCoordBall n M (K i)) →
      (∀ i ∈ t, ∀ j ∈ t, ∀ (x : M) (hx : x ∈ K i ∩ K j),
        RelHmap M n (Set.singleton_subset_iff.mpr hx.1) (ζ i)
          = RelHmap M n (Set.singleton_subset_iff.mpr hx.2) (ζ j)) →
      ∃ γ : RelH M n (⋃ i ∈ t, K i), ∀ (i : ι) (hi : i ∈ t),
        RelHmap M n (Set.subset_biUnion_of_mem hi) γ = ζ i := by
    intro t
    refine Finset.induction_on t ?base ?step
    · intro _ _
      exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro a t ha ih hKt hgt
      obtain ⟨γt, hγt⟩ := ih (fun i hi => hKt i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj x hx => hgt i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) x hx)
      have hKa : IsCoordBall n M (K a) := hKt a (Finset.mem_insert_self a t)
      have hWU : (K a ∪ ⋃ i ∈ t, K i) ⊆ (⋃ i ∈ insert a t, K i) := by
        intro y hy
        rcases hy with hy | hy
        · exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t, hy⟩
        · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hyi⟩
      have hUW : (⋃ i ∈ insert a t, K i) ⊆ (K a ∪ ⋃ i ∈ t, K i) := by
        intro y hy
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hyi
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hyi⟩)
      have hLcpt : IsCompact (⋃ i ∈ t, K i) :=
        Finset.isCompact_biUnion t (fun i hi => (hKt i (Finset.mem_insert_of_mem hi)).isCompact)
      have hInt : IsCompact (K a ∩ ⋃ i ∈ t, K i) := hKa.isCompact.inter hLcpt
      have hagree : RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
          = RelHmap M n (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt := by
        have hzero : RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
            - RelHmap M n (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt
            = 0 :=
          compactZero n hn M hInt _
            (fun x hx => by
              have hxa : x ∈ K a := hx.1
              have hxi : x ∈ ⋃ i ∈ t, K i := hx.2
              obtain ⟨i, hi, hxKi⟩ := Set.mem_iUnion₂.mp hxi
              have e1 : RelHmap M n (Set.singleton_subset_iff.mpr hxa) (ζ a)
                  = RelHmap M n (Set.singleton_subset_iff.mpr hxKi) (ζ i) := by
                rw [hgt a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) x
                  ⟨hxa, hxKi⟩]
              have e2 : RelHmap M n (Set.singleton_subset_iff.mpr hxKi) (ζ i)
                  = RelHmap M n (Set.singleton_subset_iff.mpr hxi) γt := by
                rw [← hγt i hi, ← LinearMap.comp_apply, RelHmap_comp' M n
                  (Set.singleton_subset_iff.mpr hxKi) (Set.subset_biUnion_of_mem hi)
                  (Set.singleton_subset_iff.mpr hxi)]
                first
                 | rfl
                 | (congr 1; exact RelHmap_congr_h M n _ _)
              have key1 : RelHmap M n (Set.singleton_subset_iff.mpr hx)
                    (RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a))
                  = RelHmap M n (Set.singleton_subset_iff.mpr hxa) (ζ a) := by
                rw [← LinearMap.comp_apply, RelHmap_comp' M n (Set.singleton_subset_iff.mpr hx)
                  (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a)
                  (Set.singleton_subset_iff.mpr hxa)]
              have key2 : RelHmap M n (Set.singleton_subset_iff.mpr hx)
                    (RelHmap M n (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt)
                  = RelHmap M n (Set.singleton_subset_iff.mpr hxi) γt := by
                rw [← LinearMap.comp_apply, RelHmap_comp' M n (Set.singleton_subset_iff.mpr hx)
                  (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i)
                  (Set.singleton_subset_iff.mpr hxi)]
              rw [map_sub, key1, key2, e1, e2, sub_self])
        exact sub_eq_zero.mp hzero
      obtain ⟨u, hu1, hu2⟩ := (Work.ThomBordism.excludedMV n M (K a) (⋃ i ∈ t, K i)
        hKa.isClosed hLcpt.isClosed
        (Work.Cohomology.relChains_vanishing_of_compact hn (M := M) (K a ∩ ⋃ i ∈ t, K i)
          hInt (n+1) (by omega))).2 (ζ a) γt hagree
      refine ⟨RelHmap M n hUW u, ?_⟩
      intro i hi
      have hsub : K i ⊆ K a ∪ ⋃ j ∈ t, K j := by
        rcases Finset.mem_insert.mp hi with hia | hi
        · intro y hy
          exact Or.inl (by rwa [hia] at hy)
        · intro y hy
          exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩)
      have h1 : RelHmap M n (Set.subset_biUnion_of_mem hi) (RelHmap M n hUW u)
          = RelHmap M n hsub u := by
        rw [show RelHmap M n (Set.subset_biUnion_of_mem hi) (RelHmap M n hUW u)
              = ((RelHmap M n (Set.subset_biUnion_of_mem hi)).comp (RelHmap M n hUW)) u from rfl]
        rw [RelHmap_comp' M n (Set.subset_biUnion_of_mem hi) hUW hsub]
      rw [h1]
      rcases Finset.mem_insert.mp hi with hia | hi
      · -- `i = a`
        have hcast := resRelH_aux (M := M) (n := n) (B := K a ∪ ⋃ j ∈ t, K j)
          (B' := K a ∪ ⋃ j ∈ t, K j) (D := K a) (D' := K i) rfl (congrArg K hia.symm)
          (Set.subset_union_left : K a ⊆ K a ∪ ⋃ j ∈ t, K j) hsub u
        simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.id_apply] at hcast
        rw [hcast]
        have hstep : RelHmap M n (Set.subset_union_left : K a ⊆ K a ∪ ⋃ j ∈ t, K j) u = ζ a := hu1
        rw [hstep]
        exact eqToIso_congrArg_apply (M := M) (n := n) ζ hia.symm
      · -- `i ∈ t`
        have h2 : RelHmap M n hsub u = RelHmap M n (Set.subset_biUnion_of_mem hi)
            (RelHmap M n (Set.subset_union_right :
              (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) u) := by
          rw [show RelHmap M n (Set.subset_biUnion_of_mem hi)
                (RelHmap M n (Set.subset_union_right :
                  (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) u)
              = ((RelHmap M n (Set.subset_biUnion_of_mem hi)).comp (RelHmap M n
                  (Set.subset_union_right : (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j))) u from rfl]
          rw [RelHmap_comp' M n (Set.subset_biUnion_of_mem hi)
            (Set.subset_union_right : (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) hsub]
        have hstep : RelHmap M n (Set.subset_union_right :
            (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) u = γt := hu2
        rw [h2, hstep, hγt i hi]
  exact key s hK hglue

end

end Work.Orient.Port
