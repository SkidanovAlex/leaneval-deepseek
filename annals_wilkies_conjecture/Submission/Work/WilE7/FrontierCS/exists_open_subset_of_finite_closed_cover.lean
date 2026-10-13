import Mathlib

open Set

set_option linter.style.haveILetI false

namespace Work.WilE7.FrontierCS

/-- **Baire lemma for a finite closed cover of an open set.**
Let `X` be a Baire space, `V` a nonempty open subset of `X`, and `C i` a *finite* family of
closed subsets of `X` covering `V`. Then one member `C i` meets `V` in a set with nonempty
interior: there is a nonempty open `V' ⊆ V` with `V' ⊆ C i`.

This is the relative form of the Baire category theorem: in the open subspace `V` (which is
itself Baire, `IsOpen.baireSpace`), the closed sets `V ∩ C i` cover `V`, so some one of them
has nonempty interior in `V`; pulling that interior back into `X` along the open embedding
`Subtype.val : V → X` yields the required `V'`. -/
theorem exists_open_subset_of_finite_closed_cover {ι X : Type*} [Finite ι] [TopologicalSpace X]
    [BaireSpace X] {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (C : ι → Set X)
    (hC : ∀ i, IsClosed (C i)) (hcov : V ⊆ ⋃ i, C i) :
    ∃ i, ∃ V' : Set X, IsOpen V' ∧ V'.Nonempty ∧ V' ⊆ V ∧ V' ⊆ C i := by
  -- `V`, viewed as the open subspace `↥V`, is a nonempty Baire space.
  haveI : BaireSpace ↥V := hV.baireSpace
  haveI : Nonempty ↥V := hne.to_subtype
  -- The closed sets `V ∩ C i`, as subsets of the subspace `↥V`, cover `↥V`.
  have hc : ∀ i, IsClosed (Subtype.val ⁻¹' (C i) : Set ↥V) :=
    fun i => (hC i).preimage continuous_subtype_val
  have hcov' : (⋃ i, (Subtype.val ⁻¹' (C i) : Set ↥V)) = univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hmem : ∃ i, (x : X) ∈ C i := Set.mem_iUnion.1 (hcov x.2)
    obtain ⟨i, hi⟩ := hmem
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  -- Baire in the subspace: some `C i` has nonempty relative interior.
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed (X := ↥V) hc hcov'
  -- The open embedding `↥V → X` carries that relative interior to an open subset of `X`.
  let f : ↥V → X := Subtype.val
  have hf : IsOpenMap f := hV.isOpenMap_subtype_val
  refine ⟨i, f '' interior (Subtype.val ⁻¹' (C i) : Set ↥V), hf _ isOpen_interior, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hi
    exact ⟨f x, x, hx, rfl⟩
  · rintro y ⟨x, -, rfl⟩
    exact x.2
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ Subtype.val ⁻¹' (C i) := interior_subset hx
    exact hx'

end Work.WilE7.FrontierCS
