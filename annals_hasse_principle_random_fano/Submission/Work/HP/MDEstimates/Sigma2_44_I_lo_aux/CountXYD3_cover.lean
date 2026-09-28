import Mathlib

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

theorem CountXYD3_cover {α : Type*} [DecidableEq α]
    (S : Set α) (I : Finset (ℕ × ℕ)) (shell : ℕ × ℕ → Set α) (g : α → ℕ × ℕ)
    (hS : S.Finite) (hshell : ∀ q ∈ I, (shell q).Finite)
    (hmap : ∀ p ∈ S, g p ∈ I)
    (hsub : ∀ q ∈ I, ∀ p ∈ S, g p = q → p ∈ shell q) :
    S.ncard ≤ ∑ q ∈ I, (shell q).ncard := by
  rw [Set.ncard_eq_toFinset_card S hS]
  have hmap' : Set.MapsTo g ↑(hS.toFinset) ↑I := by
    intro x hx
    rw [Set.Finite.coe_toFinset hS] at hx
    exact hmap x hx
  rw [Finset.card_eq_sum_card_fiberwise (s := hS.toFinset) (t := I) hmap']
  apply Finset.sum_le_sum
  intro b hb
  have hsub' : (↑(hS.toFinset.filter (fun a => g a = b)) : Set α) ⊆ shell b := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset hS] at hx
    exact hsub b hb x hx.1 hx.2
  have hle : (↑(hS.toFinset.filter (fun a => g a = b)) : Set α).ncard ≤ (shell b).ncard :=
    Set.ncard_le_ncard hsub' (hshell b hb)
  rwa [Set.ncard_coe_finset] at hle

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
