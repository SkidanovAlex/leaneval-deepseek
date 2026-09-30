import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

theorem floorIccSumEqIndicator (b : ℕ → ℂ) (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
    (htN : t ≤ (N : ℝ)) :
    (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n)
      = ∑ n ∈ Finset.Icc 1 N, b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0) := by
  have hfl : ⌊t⌋₊ ≤ N := by
    have h1 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
    exact_mod_cast le_trans h1 htN
  have hzero : ∀ x ∈ Finset.Icc 1 N, x ∉ Finset.Icc 1 ⌊t⌋₊ →
      b x * (if (x : ℝ) ≤ t then (1 : ℂ) else 0) = 0 := by
    intro x hx hxn
    have hxle : x ≤ N := (Finset.mem_Icc.mp hx).2
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    have hlt : ⌊t⌋₊ < x := by
      rcases Nat.lt_or_ge ⌊t⌋₊ x with h | h
      · exact h
      · exact absurd (Finset.mem_Icc.mpr ⟨hx1, h⟩) hxn
    have htx : t < (x : ℝ) := by
      have h2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
      have h3 : ((⌊t⌋₊ : ℕ) : ℝ) + 1 ≤ (x : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith
    rw [ite_eq_right (not_le.mpr htx), mul_zero]
  have hswap : (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0))
      = ∑ n ∈ Finset.Icc 1 N, b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0) :=
    Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hfl) hzero
  rw [← hswap]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ ⌊t⌋₊ := (Finset.mem_Icc.mp hx).2
  have hxt : (x : ℝ) ≤ t := by
    have h1 : ((x : ℕ) : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hxle
    have h2 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
    linarith
  rw [ite_eq_left hxt, mul_one]

end Work.BMF.mr_core
