import Mathlib.Data.Finset.BooleanAlgebra

namespace Commons.Data.Finset

theorem map_toEmbedding_compl {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β) (S : Finset α) : (S.map e.toEmbedding)ᶜ = Sᶜ.map e.toEmbedding := by
  ext x
  simp only [Finset.mem_compl, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro h
    refine ⟨e.symm x, fun hc => h ?_, e.apply_symm_apply x⟩
    exact ⟨e.symm x, hc, e.apply_symm_apply x⟩
  · rintro ⟨a, ha, rfl⟩ h
    exact ha (by
      rcases h with ⟨b, hb, hba⟩
      rwa [e.injective hba] at hb)

end Commons.Data.Finset