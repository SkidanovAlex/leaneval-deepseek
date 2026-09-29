import Mathlib

namespace Work.Haupt

open scoped BigOperators

/-- Splitting an infinite product over `ℕ` into its three residue classes modulo `3`:
if the three subsequences `f (3k)`, `f (3k+1)`, `f (3k+2)` are separately multipliable,
then so is `f`, and the total product is the product of the three partial products. -/
theorem tprod_nat_split_three {f : ℕ → ℂ}
    (h0 : Multipliable fun k => f (3 * k))
    (h1 : Multipliable fun k => f (3 * k + 1))
    (h2 : Multipliable fun k => f (3 * k + 2)) :
    (∏' k : ℕ, f (3 * k)) * (∏' k : ℕ, f (3 * k + 1)) * (∏' k : ℕ, f (3 * k + 2))
      = ∏' k : ℕ, f k := by
  have hinj0 : Function.Injective (fun k : ℕ => 3 * k) := by
    intro a b h; dsimp at h; omega
  have hinj1 : Function.Injective (fun k : ℕ => 3 * k + 1) := by
    intro a b h; dsimp at h; omega
  have hinj2 : Function.Injective (fun k : ℕ => 3 * k + 2) := by
    intro a b h; dsimp at h; omega
  -- Each residue class is the range of an injective map, so the corresponding `HasProd`
  -- holds after restricting to that range.
  have hs0 : HasProd (f ∘ (↑) : Set.range (fun k : ℕ => 3 * k) → ℂ) (∏' k, f (3 * k)) :=
    (Function.Injective.hasProd_range_iff (f := f) hinj0).2 h0.hasProd
  have hs1 : HasProd (f ∘ (↑) : Set.range (fun k : ℕ => 3 * k + 1) → ℂ) (∏' k, f (3 * k + 1)) :=
    (Function.Injective.hasProd_range_iff (f := f) hinj1).2 h1.hasProd
  have hs2 : HasProd (f ∘ (↑) : Set.range (fun k : ℕ => 3 * k + 2) → ℂ) (∏' k, f (3 * k + 2)) :=
    (Function.Injective.hasProd_range_iff (f := f) hinj2).2 h2.hasProd
  -- The classes `1` and `2` mod `3` are disjoint.
  have hdisj : Disjoint (Set.range (fun k : ℕ => 3 * k + 1))
      (Set.range (fun k : ℕ => 3 * k + 2)) := by
    rw [Set.disjoint_left]
    rintro n hn1 hn2
    rw [Set.mem_range] at hn1 hn2
    obtain ⟨a, ha⟩ := hn1
    obtain ⟨b, hb⟩ := hn2
    omega
  have h12 : HasProd (f ∘ (↑) :
      (Set.range (fun k : ℕ => 3 * k + 1) ∪ Set.range (fun k : ℕ => 3 * k + 2) : Set ℕ) → ℂ)
      ((∏' k, f (3 * k + 1)) * (∏' k, f (3 * k + 2))) :=
    HasProd.mul_disjoint hdisj hs1 hs2
  -- The classes `0` mod `3` and `1,2` mod `3` are complementary.
  have hcompl : IsCompl (Set.range (fun k : ℕ => 3 * k))
      (Set.range (fun k : ℕ => 3 * k + 1) ∪ Set.range (fun k : ℕ => 3 * k + 2)) := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro n hn0 hn12
      rw [Set.mem_union] at hn12
      rw [Set.mem_range] at hn0
      obtain ⟨a, ha⟩ := hn0
      rcases hn12 with hn1 | hn2
      · rw [Set.mem_range] at hn1; obtain ⟨b, hb⟩ := hn1; omega
      · rw [Set.mem_range] at hn2; obtain ⟨b, hb⟩ := hn2; omega
    · rw [codisjoint_iff]
      change Set.range (fun k : ℕ => 3 * k) ∪
        (Set.range (fun k : ℕ => 3 * k + 1) ∪ Set.range (fun k : ℕ => 3 * k + 2)) = Set.univ
      rw [Set.eq_univ_iff_forall]
      intro n
      simp only [Set.mem_union, Set.mem_range]
      have hn : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
      have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
      have hc : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hc with hc | hc | hc
      · exact Or.inl ⟨n / 3, by omega⟩
      · exact Or.inr (Or.inl ⟨n / 3, by omega⟩)
      · exact Or.inr (Or.inr ⟨n / 3, by omega⟩)
  have hprod : HasProd f
      ((∏' k, f (3 * k)) * ((∏' k, f (3 * k + 1)) * (∏' k, f (3 * k + 2)))) :=
    HasProd.mul_isCompl hcompl hs0 h12
  rw [hprod.tprod_eq]
  exact mul_assoc _ _ _

end Work.Haupt
