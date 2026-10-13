import Mathlib

set_option linter.style.haveILetI false

namespace Work.WilE7.FrontierCS

theorem exists_mem_iInter_of_dense_in_open {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (O : ℕ → Set X) (hO : ∀ k, IsOpen (O k))
    (hd : ∀ k, V ⊆ closure (O k)) : ∃ x ∈ V, ∀ k, x ∈ O k := by
  -- `V` is an open subset of a Baire space, hence itself a Baire space.
  haveI : BaireSpace V := hV.baireSpace
  haveI : Nonempty V := hne.to_subtype
  -- For each `k`, the open set `O k` meets every nonempty open part of `V`, so its
  -- trace on `V` is dense in the subspace `V`.
  have hdense : ∀ k, Dense ((↑) ⁻¹' (O k) : Set V) := by
    intro k
    rw [Subtype.dense_iff]
    intro x hx
    have h1 : x ∈ closure (O k) ∩ V := ⟨hd k hx, hx⟩
    have h2 : x ∈ closure (O k ∩ V) := hV.closure_inter h1
    have hset : ((↑) '' ((↑) ⁻¹' (O k) : Set V)) = O k ∩ V := by
      rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
    simpa [hset] using h2
  -- Baire category theorem in `V`: the countable intersection is dense, hence nonempty.
  have hAll : Dense (⋂ k, ((↑) ⁻¹' (O k) : Set V)) :=
    dense_iInter_of_isOpen_nat (fun k => (hO k).preimage continuous_subtype_val) hdense
  obtain ⟨x, hx⟩ := hAll.nonempty
  rw [Set.mem_iInter] at hx
  exact ⟨(x : X), x.property, fun k => hx k⟩

end Work.WilE7.FrontierCS
