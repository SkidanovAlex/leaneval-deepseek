import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.LinearAlgebra.Dimension

theorem linearIndependent_mem_of_le_finrank_span
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
    {s : Set M} {ℓ : ℕ} (h : ℓ ≤ Module.finrank K (Submodule.span K s)) :
    ∃ f : Fin ℓ → M, (∀ i, f i ∈ s) ∧ LinearIndependent K f := by
  obtain ⟨f, hf_mem, -, hf_li⟩ := Submodule.exists_fun_fin_finrank_span_eq K s
  exact ⟨f ∘ Fin.castLE h, fun i => hf_mem _, hf_li.comp _ (Fin.castLE_injective h)⟩

end Commons.LinearAlgebra.Dimension