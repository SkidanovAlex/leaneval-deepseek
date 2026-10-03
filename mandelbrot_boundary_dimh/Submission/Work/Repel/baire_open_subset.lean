import Mathlib

set_option linter.style.haveILetI false

namespace Work.Repel

/-- **Baire category, relative form.** If `U` is a nonempty open subset of a Baire space and
`U` is covered by countably many sets `Z n` each of which is relatively closed in `U`
(`Z n = U ∩ K n` with `K n` closed), then some `Z n` contains a nonempty relatively open
piece `V ∩ U`, with `V` open in the whole space. -/
theorem baire_open_subset {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty) {Z : ℕ → Set X}
    (hZc : ∀ n, ∃ K : Set X, IsClosed K ∧ Z n = U ∩ K)
    (hcover : U ⊆ ⋃ n, Z n) :
    ∃ n, ∃ V : Set X, IsOpen V ∧ (V ∩ U).Nonempty ∧ V ∩ U ⊆ Z n := by
  -- Work in the subspace `↥U`, which is Baire because `U` is open in a Baire space.
  haveI : Nonempty ↥U := hUne.to_subtype
  haveI : BaireSpace ↥U := hU.baireSpace
  set f : ℕ → Set ↥U := fun n => (↑) ⁻¹' (Z n) with hf
  -- `Z n` is relatively closed, hence `f n` is closed in `↥U`.
  have hfclosed : ∀ n, IsClosed (f n) := by
    intro n
    obtain ⟨K, hK, hZK⟩ := hZc n
    have hfn : f n = (↑) ⁻¹' K := by
      ext x
      simp only [hf, Set.mem_preimage, hZK, Set.mem_inter_iff]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [hfn]
    exact hK.preimage continuous_subtype_val
  -- The `f n` cover `↥U`.
  have hcover' : ⋃ n, f n = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx := hcover x.2
    rw [Set.mem_iUnion] at hx
    simpa [hf] using hx
  -- Baire: some `f n` has nonempty interior in `↥U`.
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hfclosed hcover'
  -- The interior is open in the subspace, so it is the trace of an open `V` in `X`.
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior (f n)))
  refine ⟨n, V, hVopen, ?_, ?_⟩
  · rcases hn with ⟨x, hx⟩
    have hxV : x ∈ Subtype.val ⁻¹' V := hVeq.symm ▸ hx
    exact ⟨x.1, hxV, x.2⟩
  · intro y hy
    rw [Set.mem_inter_iff] at hy
    have hxV : (⟨y, hy.2⟩ : ↥U) ∈ Subtype.val ⁻¹' V := hy.1
    have hxI : (⟨y, hy.2⟩ : ↥U) ∈ interior (f n) := hVeq ▸ hxV
    have h2 : (⟨y, hy.2⟩ : ↥U) ∈ f n := interior_subset hxI
    simpa [hf] using h2

end Work.Repel
