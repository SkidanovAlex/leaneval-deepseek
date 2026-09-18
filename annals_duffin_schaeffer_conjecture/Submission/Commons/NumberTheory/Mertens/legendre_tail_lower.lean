import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.NumberTheory.Mertens

theorem legendre_tail_lower (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    (n : ℝ) * (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / (p : ℝ) ^ i)
        - ((Nat.log p n : ℝ) - 1)
      ≤ ∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ) := by
  set L := Nat.log p n with hLdef
  set s := Finset.Ico 2 (L + 1) with hsdef
  set t := Finset.Ico 2 (n + 1) with htdef
  have hp2 : 1 < p := hp.one_lt
  have hp0 : 0 < p := hp.pos
  have hL1 : 1 ≤ L := by
    have : p ^ 1 ≤ n := by simpa using hpn
    exact Nat.le_log_of_pow_le hp2 this
  have hLn : L ≤ n := Nat.log_le_self p n
  have hpow_pos : ∀ i, 0 < p ^ i := fun i => pow_pos hp0 i
  have hterm : ∀ i ∈ s, (n : ℝ) / (p : ℝ) ^ i - 1 ≤ ((n / p ^ i : ℕ) : ℝ) := by
    intro i _
    have hk : 0 < p ^ i := hpow_pos i
    have hnlt : n < (n / p ^ i + 1) * p ^ i := by
      have h := Nat.div_add_mod n (p ^ i)
      have hmod := Nat.mod_lt n hk
      have hdist : (n / p ^ i + 1) * p ^ i = p ^ i * (n / p ^ i) + p ^ i := by ring
      rw [hdist]
      omega
    have hkR : (0 : ℝ) < (p : ℝ) ^ i := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
      positivity
    have hcast : (n : ℝ) < (((n / p ^ i : ℕ) : ℝ) + 1) * (p : ℝ) ^ i := by
      have h' : (n : ℝ) < (((n / p ^ i + 1) * p ^ i : ℕ) : ℝ) := by exact_mod_cast hnlt
      push_cast at h'
      exact h'
    have hlt : (n : ℝ) / (p : ℝ) ^ i < ((n / p ^ i : ℕ) : ℝ) + 1 :=
      (div_lt_iff₀ hkR).mpr hcast
    linarith
  have hsubset : s ⊆ t := by
    rw [hsdef, htdef]
    exact Finset.Ico_subset_Ico_right (Nat.succ_le_succ hLn)
  have h2 : ∑ i ∈ s, ((n / p ^ i : ℕ) : ℝ) ≤ ∑ i ∈ t, ((n / p ^ i : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => by positivity)
  have hs_card : (s.card : ℝ) = (L : ℝ) - 1 := by
    rw [hsdef, Nat.card_Ico]
    have h : L + 1 - 2 = L - 1 := by omega
    rw [h, Nat.cast_sub hL1]
    norm_num
  have hsum_eq : ∑ i ∈ s, ((n : ℝ) / (p : ℝ) ^ i - 1)
      = (n : ℝ) * (∑ i ∈ s, (1 : ℝ) / (p : ℝ) ^ i) - ((L : ℝ) - 1) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_inv, one_div]
    · simp [hs_card]
  have h1 : ∑ i ∈ s, ((n : ℝ) / (p : ℝ) ^ i - 1) ≤ ∑ i ∈ s, ((n / p ^ i : ℕ) : ℝ) :=
    Finset.sum_le_sum hterm
  rw [hsum_eq] at h1
  rw [hLdef, hsdef, htdef]
  exact h1.trans h2

end Commons.NumberTheory.Mertens