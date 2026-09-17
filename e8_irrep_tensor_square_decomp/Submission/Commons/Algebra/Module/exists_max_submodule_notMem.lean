import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Zorn

namespace Commons.Algebra.Module

theorem exists_max_submodule_notMem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (m : M)
    (h : ∀ N₁ N₂ : Submodule R M, m ∉ N₁ → m ∉ N₂ → m ∉ N₁ ⊔ N₂) (h0 : m ≠ 0) :
    ∃ N : Submodule R M, m ∉ N ∧ ∀ N' : Submodule R M, m ∉ N' → N' ≤ N := by
  have hchain : ∀ c ⊆ {N : Submodule R M | m ∉ N}, IsChain (· ≤ ·) c →
      ∃ ub ∈ {N : Submodule R M | m ∉ N}, ∀ z ∈ c, z ≤ ub := by
    intro c hc_sub hc_chain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, by simpa using h0, fun z hz => by simp at hz⟩
    · refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
      intro hm
      obtain ⟨y, hyc, hmy⟩ := (Submodule.mem_sSup_of_directed hne hc_chain.directedOn).mp hm
      exact hc_sub hyc hmy
  obtain ⟨N, hNs, hmax⟩ := zorn_le₀ {N : Submodule R M | m ∉ N} hchain
  refine ⟨N, hNs, fun N' hN' => ?_⟩
  have hjoin : m ∉ N ⊔ N' := h N N' hNs hN'
  exact le_trans le_sup_right (hmax (y := N ⊔ N') hjoin le_sup_left)

end Commons.Algebra.Module