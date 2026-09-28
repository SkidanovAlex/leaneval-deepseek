import Mathlib

namespace Work.ThomBordism

open Set UniformSpace
open scoped Uniformity SetRel

theorem exists_starRefinement {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type*} [Fintype ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = Set.univ) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → Set X) (r : κ → ι),
      (∀ j, IsOpen (W j)) ∧ (⋃ j, W j = Set.univ) ∧ (∀ j, W j ⊆ U (r j)) ∧
      (∀ j l, (W l ∩ W j).Nonempty → W l ⊆ U (r j)) := by
  -- Put the unique uniform structure of the compact Hausdorff space `X`.
  letI : UniformSpace X := uniformSpaceOfCompactR1
  -- Lebesgue number of the open cover `U`
  obtain ⟨V, hV, hVU⟩ :=
    lebesgue_number_lemma (K := (Set.univ : Set X)) isCompact_univ hU (by rw [hcov])
  -- A small open symmetric entourage `W` with `W ○ W ○ W ⊆ V` and `W ⊆ V`.
  obtain ⟨W, hW_mem, hW_open, hW_symm, hWWW, hWV⟩ :
      ∃ W ∈ 𝓤 X, IsOpen W ∧ SetRel.IsSymm W ∧ W ○ W ○ W ⊆ V ∧ W ⊆ V := by
    obtain ⟨W₂, hW₂, hW₂V⟩ := comp_mem_uniformity_sets hV
    obtain ⟨W₃, hW₃, hW₃W₂⟩ := comp_mem_uniformity_sets hW₂
    have hW₃_sub_W₂ : W₃ ⊆ W₂ := (subset_comp_self_of_mem_uniformity hW₃).trans hW₃W₂
    have hW₂_sub_V : W₂ ⊆ V := (subset_comp_self_of_mem_uniformity hW₂).trans hW₂V
    have hW₃_sub_V : W₃ ⊆ V := hW₃_sub_W₂.trans hW₂_sub_V
    have hWW : (W₃ ○ W₃) ○ W₃ ⊆ V := by
      calc (W₃ ○ W₃) ○ W₃ ⊆ W₂ ○ W₃ := SetRel.comp_subset_comp_left hW₃W₂
        _ ⊆ W₂ ○ W₂ := SetRel.comp_subset_comp_right hW₃_sub_W₂
        _ ⊆ V := hW₂V
    obtain ⟨W, ⟨hW_mem, hW_open, hW_symm⟩, hWW₃⟩ :=
      (uniformity_hasBasis_open_symmetric (α := X)).mem_iff.mp hW₃
    refine ⟨W, hW_mem, hW_open, hW_symm, ?_, hWW₃.trans hW₃_sub_V⟩
    calc (W ○ W) ○ W ⊆ (W₃ ○ W₃) ○ W₃ :=
          SetRel.comp_subset_comp (SetRel.comp_subset_comp hWW₃ hWW₃) hWW₃
      _ ⊆ V := hWW
  haveI : SetRel.IsSymm W := hW_symm
  -- Finitely many balls of radius `W` cover `X`.
  have hball_open : ∀ x : X, IsOpen (ball x W) := fun x => isOpen_ball x hW_open
  have hball_cover : (Set.univ : Set X) ⊆ ⋃ x, ball x W := by
    intro x _
    exact mem_iUnion.2 ⟨x, mem_ball_self x hW_mem⟩
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover (fun x => ball x W) hball_open hball_cover
  -- The star-refinement is the family of these balls.
  let κ₀ := {x // x ∈ t}
  let W₀ : κ₀ → Set X := fun j => ball j.1 W
  let r₀ : κ₀ → ι := fun j => (hVU j.1 (Set.mem_univ _)).choose
  have hW₀_open : ∀ j : κ₀, IsOpen (W₀ j) := fun j => hball_open j.1
  have hcover₀ : (⋃ j : κ₀, W₀ j) = Set.univ := by
    apply Subset.antisymm (Set.subset_univ _)
    intro x _
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.1 hy
    exact Set.mem_iUnion.2 ⟨⟨y, hyt⟩, hxy⟩
  have hr₀ : ∀ j : κ₀, W₀ j ⊆ U (r₀ j) := fun j =>
    (ball_mono hWV j.1).trans (hVU j.1 (Set.mem_univ _)).choose_spec
  have hstar₀ : ∀ j l : κ₀, (W₀ l ∩ W₀ j).Nonempty → W₀ l ⊆ U (r₀ j) := by
    intro j l hne w hw
    obtain ⟨z, hz⟩ := hne
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hzl, hzj⟩ := hz
    have h1 : (j.1, z) ∈ W := hzj
    have h3 : (z, l.1) ∈ W := (SetRel.comm W).mp hzl
    have h4 : (l.1, w) ∈ W := hw
    have h5 : (j.1, w) ∈ W ○ W ○ W :=
      SetRel.prodMk_mem_comp (SetRel.prodMk_mem_comp h1 h3) h4
    exact (hVU j.1 (Set.mem_univ _)).choose_spec (hWWW h5)
  -- Reindex by a small (`Type 0`) finite type.
  let e := Fintype.equivFin κ₀
  refine ⟨Fin (Fintype.card κ₀), inferInstance,
    fun k => W₀ (e.symm k), fun k => r₀ (e.symm k), ?_, ?_, ?_, ?_⟩
  · intro k; exact hW₀_open (e.symm k)
  · apply Subset.antisymm (Set.subset_univ _)
    intro x _
    have hx : x ∈ ⋃ j : κ₀, W₀ j := by rw [hcover₀]; exact Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨e j, by simpa using hj⟩
  · intro k; exact hr₀ (e.symm k)
  · intro j l; exact hstar₀ (e.symm j) (e.symm l)

end Work.ThomBordism
