import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace Commons.Analysis.Fourier

theorem card_filter_le_two (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) (c : ℝ) :
    (Finset.univ.filter (fun k : Fin K => |lam k - c| < 3 / 4)).card ≤ 2 := by
  classical
  set S : Finset (Fin K) := Finset.univ.filter (fun k => |lam k - c| < 3 / 4) with hS
  set S₁ : Finset (Fin K) := S.filter (fun k => lam k < c) with hS₁
  set S₂ : Finset (Fin K) := S.filter (fun k => ¬ lam k < c) with hS₂
  have hmemS : ∀ k ∈ S, |lam k - c| < 3 / 4 := by
    intro k hk; rw [hS] at hk; exact (Finset.mem_filter.mp hk).2
  have hsplit : S.card = S₁.card + S₂.card := by
    rw [hS₁, hS₂, Finset.card_filter_add_card_filter_not]
  have h1 : S₁.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk l hl
    by_contra hne
    have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
    have hlS : l ∈ S := (Finset.mem_filter.mp hl).1
    have hklt : lam k < c := (Finset.mem_filter.mp hk).2
    have hllt : lam l < c := (Finset.mem_filter.mp hl).2
    have hka := hmemS k hkS
    have hla := hmemS l hlS
    have hk2 : c - lam k < 3 / 4 := by
      have := (abs_lt.mp hka).1; linarith
    have hl2 : c - lam l < 3 / 4 := by
      have := (abs_lt.mp hla).1; linarith
    have hlt : |(c - lam l) - (c - lam k)| < 3 / 4 := by
      rw [abs_lt]; constructor <;> linarith
    have heq : |(c - lam l) - (c - lam k)| = |lam k - lam l| := by
      rw [show (c - lam l) - (c - lam k) = lam k - lam l by ring]
    rw [heq] at hlt
    have := hsep k l hne
    linarith
  have h2 : S₂.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk l hl
    by_contra hne
    have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
    have hlS : l ∈ S := (Finset.mem_filter.mp hl).1
    have hkge : c ≤ lam k := not_lt.mp (Finset.mem_filter.mp hk).2
    have hlge : c ≤ lam l := not_lt.mp (Finset.mem_filter.mp hl).2
    have hka := hmemS k hkS
    have hla := hmemS l hlS
    have hk2 : lam k - c < 3 / 4 := (abs_lt.mp hka).2
    have hl2 : lam l - c < 3 / 4 := (abs_lt.mp hla).2
    have hlt : |(lam k - c) - (lam l - c)| < 3 / 4 := by
      rw [abs_lt]; constructor <;> linarith
    have heq : |(lam k - c) - (lam l - c)| = |lam k - lam l| := by
      rw [show (lam k - c) - (lam l - c) = lam k - lam l by ring]
    rw [heq] at hlt
    have := hsep k l hne
    linarith
  rw [hsplit]
  omega

end Commons.Analysis.Fourier