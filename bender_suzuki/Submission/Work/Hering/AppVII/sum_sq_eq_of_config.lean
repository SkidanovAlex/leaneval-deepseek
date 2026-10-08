import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- Direct computation of the "sum of squared differences" for a configuration in which all
values `n i` equal `m` except at one index `i₀`, where the value differs from `m` by `±1`:
only the `2 (p - 1)` ordered pairs involving `i₀` contribute, each contributing `1`. -/
theorem sum_sq_eq_of_config {p : ℕ} {n : Fin p → ℤ} {i₀ : Fin p} {m : ℤ}
    (hrest : ∀ i : Fin p, i ≠ i₀ → n i = m) (hsp : n i₀ = m + 1 ∨ n i₀ = m - 1) :
    ∑ i : Fin p, ∑ j : Fin p, (n i - n j) ^ 2 = 2 * ((p : ℤ) - 1) := by
  classical
  have hp1 : 1 ≤ p := by have := i₀.isLt; omega
  have hc2 : (n i₀ - m) ^ 2 = 1 := by
    rcases hsp with h | h <;> rw [h] <;> ring
  -- inner sum at an index different from `i₀`
  have hinner_ne : ∀ i : Fin p, i ≠ i₀ → ∑ j : Fin p, (n i - n j) ^ 2 = 1 := by
    intro i hi
    rw [hrest i hi]
    have hsum : ∑ j : Fin p, (m - n j) ^ 2 = (m - n i₀) ^ 2 := by
      apply Finset.sum_eq_single i₀
      · intro j _ hj; rw [hrest j hj]; ring
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [hsum]
    have hm : m - n i₀ = -(n i₀ - m) := by ring
    rw [hm, neg_sq]
    exact hc2
  -- inner sum at `i₀`
  have hinner_eq : ∑ j : Fin p, (n i₀ - n j) ^ 2 = (p : ℤ) - 1 := by
    rw [← Finset.add_sum_erase Finset.univ (fun j => (n i₀ - n j) ^ 2) (Finset.mem_univ i₀)]
    have hzero : (n i₀ - n i₀) ^ 2 = 0 := by ring
    rw [hzero, zero_add]
    have hcongr : ∑ j ∈ Finset.univ.erase i₀, (n i₀ - n j) ^ 2
        = ∑ j ∈ Finset.univ.erase i₀, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_erase] at hj
      rw [hrest j hj.1]
      exact hc2
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    exact Nat.cast_sub hp1
  -- the outer sum over the indices different from `i₀`
  have hrestsum : ∑ i ∈ Finset.univ.erase i₀, (∑ j : Fin p, (n i - n j) ^ 2) = (p : ℤ) - 1 := by
    rw [show (∑ i ∈ Finset.univ.erase i₀, (∑ j : Fin p, (n i - n j) ^ 2))
        = ∑ i ∈ Finset.univ.erase i₀, (1 : ℤ) from
      Finset.sum_congr rfl (fun i hi => hinner_ne i (Finset.mem_erase.mp hi).1)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    exact Nat.cast_sub hp1
  rw [← Finset.add_sum_erase Finset.univ (fun i => ∑ j : Fin p, (n i - n j) ^ 2) (Finset.mem_univ i₀)]
  rw [hinner_eq, hrestsum]
  ring

end Work.Hering.AppVII
