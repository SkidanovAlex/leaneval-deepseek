import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.CWComplex.Classical.Basic

set_option linter.style.haveILetI false

namespace Commons.Topology.CWComplex

open Set Function

/-- A CW structure on a closed subspace `C` of a space `X` restricts to a CW structure on the whole
of the subtype `↥C`, with the same cell types. -/
theorem exists_cwComplex_univ_of_isClosed_subspace
    {X : Type*} [TopologicalSpace X] {C : Set X} (hCc : IsClosed C)
    (hC : _root_.Topology.CWComplex C) :
    ∃ hC' : _root_.Topology.CWComplex (X := ↥C) Set.univ,
      ∀ n : ℕ, IsEmpty (hC.cell n) → IsEmpty (hC'.cell n) := by
  classical
  have hcellC : ∀ (n : ℕ) (j : hC.cell n),
      hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 ⊆ C := by
    intro n j x hx
    rw [← hC.union']
    simp only [Set.mem_iUnion]
    exact ⟨n, j, hx⟩
  by_cases hne : Nonempty ↥C
  · let dflt : ↥C := Classical.choice hne
    let toF : (n : ℕ) → hC.cell n → (Fin n → ℝ) → ↥C :=
      fun n i t => if h : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1
        then ⟨hC.map n i t, hcellC n i (mem_image_of_mem _ h)⟩
        else dflt
    have toF_apply : ∀ (n : ℕ) (i : hC.cell n) (t : Fin n → ℝ)
        (ht : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1),
        (toF n i t : X) = hC.map n i t := by
      intro n i t ht
      simp only [toF, dif_pos ht]
    let mp : (n : ℕ) → hC.cell n → PartialEquiv (Fin n → ℝ) ↥C :=
      fun n i =>
        { toFun := toF n i
          invFun := fun y => (hC.map n i).symm (y : X)
          source := Metric.ball (0 : Fin n → ℝ) 1
          target := Subtype.val ⁻¹' (hC.map n i).target
          map_source' := by
            intro t ht
            change ((toF n i t : ↥C) : X) ∈ (hC.map n i).target
            rw [toF_apply n i t (Metric.ball_subset_closedBall ht)]
            exact (hC.map n i).map_source (by rw [hC.source_eq n i]; exact ht)
          map_target' := by
            intro y hy
            have hy' : (y : X) ∈ (hC.map n i).target := hy
            have h := (hC.map n i).map_target hy'
            rwa [hC.source_eq n i] at h
          left_inv' := by
            intro t ht
            rw [toF_apply n i t (Metric.ball_subset_closedBall ht)]
            exact (hC.map n i).left_inv (by rw [hC.source_eq n i]; exact ht)
          right_inv' := by
            intro y hy
            have hy' : (y : X) ∈ (hC.map n i).target := hy
            have hmem : (hC.map n i).symm (y : X) ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
              Metric.ball_subset_closedBall
                (by rw [← hC.source_eq n i]; exact (hC.map n i).map_target hy')
            apply Subtype.ext
            rw [toF_apply n i _ hmem, (hC.map n i).right_inv hy'] }
    have hopen : ∀ (n : ℕ) (i : hC.cell n),
        mp n i '' Metric.ball (0 : Fin n → ℝ) 1
          = (Subtype.val : ↥C → X) ⁻¹' (hC.map n i '' Metric.ball (0 : Fin n → ℝ) 1) := by
      intro n i
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [Set.mem_preimage]
        change ((toF n i t : ↥C) : X) ∈ hC.map n i '' Metric.ball (0 : Fin n → ℝ) 1
        rw [toF_apply n i t (Metric.ball_subset_closedBall ht)]
        exact mem_image_of_mem _ ht
      · intro hy
        rw [Set.mem_preimage] at hy
        obtain ⟨t, ht, ht'⟩ := hy
        refine ⟨t, ht, ?_⟩
        apply Subtype.ext
        rw [toF_apply n i t (Metric.ball_subset_closedBall ht), ht']
    have hclosed : ∀ (n : ℕ) (i : hC.cell n),
        mp n i '' Metric.closedBall (0 : Fin n → ℝ) 1
          = (Subtype.val : ↥C → X) ⁻¹'
              (hC.map n i '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
      intro n i
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [Set.mem_preimage]
        change ((toF n i t : ↥C) : X) ∈ hC.map n i '' Metric.closedBall (0 : Fin n → ℝ) 1
        rw [toF_apply n i t ht]
        exact mem_image_of_mem _ ht
      · intro hy
        rw [Set.mem_preimage] at hy
        obtain ⟨t, ht, ht'⟩ := hy
        refine ⟨t, ht, ?_⟩
        apply Subtype.ext
        rw [toF_apply n i t ht, ht']
    have himgv : ∀ (n : ℕ) (j : hC.cell n),
        (Subtype.val : ↥C → X) '' (mp n j '' Metric.closedBall (0 : Fin n → ℝ) 1)
          = hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 := by
      intro n j
      ext x
      constructor
      · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, by rw [toF_apply n j t ht]⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨mp n j t, ⟨t, ht, rfl⟩, toF_apply n j t ht⟩
    have hun : (⋃ (n : ℕ) (j : hC.cell n),
        hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1) = C := hC.union'
    refine ⟨{ cell := fun n => hC.cell n
              map := mp
              source_eq := fun n i => rfl
              continuousOn := by
                intro n i
                rw [_root_.Topology.IsInducing.continuousOn_iff
                  _root_.Topology.IsInducing.subtypeVal]
                exact (hC.continuousOn n i).congr (fun t ht => by
                  simp only [Function.comp_apply]
                  exact toF_apply n i t ht)
              continuousOn_symm := by
                intro n i
                exact (hC.continuousOn_symm n i).comp continuous_subtype_val.continuousOn
                  (fun y hy => hy)
              pairwiseDisjoint' := by
                intro a _ b _ hab
                show Disjoint (mp a.1 a.2 '' Metric.ball (0 : Fin a.1 → ℝ) 1)
                  (mp b.1 b.2 '' Metric.ball (0 : Fin b.1 → ℝ) 1)
                rw [hopen a.1 a.2, hopen b.1 b.2]
                refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
                rw [Set.mem_preimage] at hy1 hy2
                exact Set.disjoint_left.mp
                  (hC.pairwiseDisjoint' (Set.mem_univ a) (Set.mem_univ b) hab) hy1 hy2
              mapsTo' := by
                intro n i
                obtain ⟨I, hJ⟩ := hC.mapsTo' n i
                refine ⟨I, fun t ht => ?_⟩
                have htm : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
                  Metric.sphere_subset_closedBall ht
                have h1 := hJ ht
                simp only [Set.mem_iUnion, Set.mem_image] at h1 ⊢
                obtain ⟨m, hmn, j, hj, t', ht', heq⟩ := h1
                refine ⟨m, hmn, j, hj, t', ht', ?_⟩
                apply Subtype.ext
                rw [toF_apply m j t' ht', toF_apply n i t htm]
                exact heq
              closed' := by
                intro A _ hcl
                have hAeq : A = (Subtype.val : ↥C → X) ⁻¹' (Subtype.val '' A) :=
                  (Set.preimage_image_eq A Subtype.val_injective).symm
                rw [hAeq]
                refine IsClosed.preimage continuous_subtype_val (hC.closed' _ ?_ ?_)
                · rintro x ⟨a, -, rfl⟩
                  exact a.2
                · intro n j
                  have himg : (Subtype.val : ↥C → X) ''
                      (A ∩ mp n j '' Metric.closedBall (0 : Fin n → ℝ) 1)
                      = (Subtype.val '' A) ∩
                        (hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
                    rw [Set.image_inter Subtype.val_injective, himgv n j]
                  simpa only [← himg] using hCc.isClosedMap_subtype_val _ (hcl n j)
              union' := by
                have hthis : (⋃ (n : ℕ) (j : hC.cell n),
                      mp n j '' Metric.closedBall (0 : Fin n → ℝ) 1)
                    = (Subtype.val : ↥C → X) ⁻¹' (⋃ (n : ℕ) (j : hC.cell n),
                      hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
                  rw [Set.preimage_iUnion]
                  refine Set.iUnion_congr (fun n => ?_)
                  rw [Set.preimage_iUnion]
                  exact Set.iUnion_congr (fun j => hclosed n j)
                rw [hthis, hun]
                exact Set.eq_univ_iff_forall.mpr (fun z => z.2) }, ?_⟩
    intro n h
    exact h
  · haveI hZ : IsEmpty ↥C := not_nonempty_iff.mp hne
    have hcell : ∀ n : ℕ, IsEmpty (hC.cell n) := fun n =>
      ⟨fun j => IsEmpty.false (self := hZ)
        ⟨hC.map n j 0, hcellC n j (mem_image_of_mem _ (by simp [Metric.mem_closedBall]))⟩⟩
    have hexf : ∀ (n : ℕ) (i : hC.cell n), False := fun n i => (hcell n).false i
    refine ⟨{ cell := fun n => hC.cell n
              map := fun n i => (hexf n i).elim
              source_eq := fun n i => (hexf n i).elim
              continuousOn := fun n i => (hexf n i).elim
              continuousOn_symm := fun n i => (hexf n i).elim
              pairwiseDisjoint' := by
                intro a _ b _ _
                exact (hexf a.1 a.2).elim
              mapsTo' := fun n i => (hexf n i).elim
              closed' := by
                intro A _ _
                rw [show A = ∅ from
                  Set.eq_empty_iff_forall_notMem.mpr (fun z _ => isEmptyElim z)]
                exact isClosed_empty
              union' := by
                rw [Set.eq_univ_iff_forall]
                intro z
                exact isEmptyElim z }, ?_⟩
    intro n h
    exact h

end Commons.Topology.CWComplex