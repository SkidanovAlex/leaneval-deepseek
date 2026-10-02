import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

/-- A compact set covered by two open sets can be split into two compact pieces, one contained
in each of the two open sets. -/
theorem pd_compact_pieces {M : TopCat} [T2Space M] {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V) {K : Set M} (hKc : IsCompact K) (hKW : K ⊆ U ∪ V) :
    ∃ K₁ K₂ : Set M, K₁ ⊆ U ∧ K₂ ⊆ V ∧ IsCompact K₁ ∧ IsCompact K₂ ∧ K ⊆ K₁ ∪ K₂ := by
  have hKcomp : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hsc : IsClosed {x : K | (x : M) ∉ U} :=
    (hU.preimage continuous_subtype_val).isClosed_compl
  have htc : IsClosed {x : K | (x : M) ∉ V} :=
    (hV.preimage continuous_subtype_val).isClosed_compl
  have hd : Disjoint {x : K | (x : M) ∉ U} {x : K | (x : M) ∉ V} := by
    rw [Set.disjoint_left]
    rintro x hx1 hx2
    rcases hKW x.2 with h | h
    · exact hx1 h
    · exact hx2 h
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed hsc htc hd
  refine ⟨Subtype.val '' {x : K | (1 : ℝ) / 2 ≤ f x},
    Subtype.val '' {x : K | f x ≤ (1 : ℝ) / 2}, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hcon
    have h0 : f x = 0 := hf0 hcon
    rw [h0] at hx
    norm_num at hx
  · rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hcon
    have h1 : f x = 1 := hf1 hcon
    rw [h1] at hx
    norm_num at hx
  · exact (isClosed_le continuous_const f.continuous).isCompact.image continuous_subtype_val
  · exact (isClosed_le f.continuous continuous_const).isCompact.image continuous_subtype_val
  · intro y hy
    rcases le_total (f ⟨y, hy⟩) ((1 : ℝ) / 2) with h | h
    · exact Or.inr ⟨⟨y, hy⟩, h, rfl⟩
    · exact Or.inl ⟨⟨y, hy⟩, h, rfl⟩

end Work.Cohomology
