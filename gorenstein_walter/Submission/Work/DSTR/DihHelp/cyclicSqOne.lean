import Mathlib

namespace Work.DSTR.DihHelp

/-- A cyclic group all of whose elements satisfy `x ^ 2 = 1` has at most two elements.  (No
finiteness hypothesis: for an infinite cyclic group `Nat.card` is `0`, and the argument via a
generator handles both cases.) -/
lemma cyclicSqOne {G : Type*} [Group G]
    (hcyc : IsCyclic G) (h2 : ∀ g : G, g ^ 2 = 1) : Nat.card G ≤ 2 := by
  classical
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  -- `g ^ 2 = 1`, with the exponent read as an integer so that the results about `zpow` apply
  have hg2 : g ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact h2 g
  -- every integer power of `g` is either `1` or `g`, since `g ^ 2 = 1`
  have key : ∀ k : ℤ, g ^ k = 1 ∨ g ^ k = g := by
    intro k
    have h1 : g ^ k = g ^ (k % 2) := zpow_eq_zpow_emod k hg2
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h1, h]; exact zpow_zero g
    · right; rw [h1, h]; exact zpow_one g
  -- hence every element of `G` is `1` or `g`
  have hall : ∀ x : G, x = 1 ∨ x = g := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [← hk]; exact key k
  -- so there is an injection `G → Fin 2`, which bounds `Nat.card G` by `2`
  have hinj : Function.Injective (fun x : G => if x = 1 then (0 : Fin 2) else 1) := by
    intro a b hab
    by_cases ha : a = 1 <;> by_cases hb : b = 1
    · rw [ha, hb]
    · exact absurd hab (by simp [ha, hb])
    · exact absurd hab (by simp [ha, hb])
    · rcases hall a with h | h <;> rcases hall b with h' | h'
      · rw [h, h']
      · exact absurd h ha
      · exact absurd h' hb
      · rw [h, h']
  have hle := Nat.card_le_card_of_injective
    (fun x : G => if x = 1 then (0 : Fin 2) else 1) hinj
  simpa using hle

end Work.DSTR.DihHelp
