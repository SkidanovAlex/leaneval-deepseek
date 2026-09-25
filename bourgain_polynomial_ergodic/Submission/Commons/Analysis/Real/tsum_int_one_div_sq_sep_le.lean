import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries

namespace Commons.Analysis.Real

open scoped Topology

/-- Telescoping bound: every partial sum of `∑ 1/(n+1)²` is at most `2`. -/
lemma sum_range_one_div_sq_add_one_le_two (N : ℕ) :
    ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 2 ≤ 2 := by
  have hterm : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ^ 2 ≤
      1 / ((i : ℝ) + 1 / 2) - 1 / (((i : ℝ) + 1) + 1 / 2) := by
    intro i
    have hkey : (1:ℝ) / ((i:ℝ) + 1/2) - 1 / (((i:ℝ) + 1) + 1/2)
        = 1 / (((i:ℝ) + 1/2) * (((i:ℝ) + 1) + 1/2)) := by
      field_simp
      ring
    rw [hkey]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  calc ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 2
      ≤ ∑ i ∈ Finset.range N,
          (1 / ((i : ℝ) + 1 / 2) - 1 / (((i : ℝ) + 1) + 1 / 2)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 1 / ((0:ℝ) + 1 / 2) - 1 / ((N:ℝ) + 1 / 2) := by
        have := Finset.sum_range_sub' (fun t : ℕ => 1 / ((t:ℝ) + 1/2)) N
        simpa [Nat.cast_add, Nat.cast_one] using this
    _ ≤ 2 := by
        have hN : 0 ≤ 1 / ((N:ℝ) + 1/2) := by positivity
        norm_num
        linarith

/-- The series `∑ 1/(n+1)²` is summable. -/
lemma summable_one_div_sq_add_one : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)
  have h2 := h.comp_injective (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) Nat.succ_injective
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h2

/-- `∑' n, 1/(n+1)² ≤ 2`. -/
lemma tsum_one_div_sq_add_one_le_two : ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2 ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun i => by positivity) sum_range_one_div_sq_add_one_le_two

/-- For `ρ > 0`, the series `∑ 1/(ρ+n)²` is summable. -/
lemma summable_one_div_add_sq (ρ : ℝ) (hρ : 0 < ρ) :
    Summable (fun t : ℕ => 1 / (ρ + (t : ℝ)) ^ 2) := by
  have hshift : Summable (fun n : ℕ => 1 / (ρ + ((n : ℝ) + 1)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      summable_one_div_sq_add_one
    have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have h2 : (n:ℝ) + 1 ≤ ρ + ((n:ℝ) + 1) := by linarith [le_of_lt hρ]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt h1) h2 2)
  refine (summable_nat_add_iff 1).mp ?_
  simpa [Nat.cast_add, Nat.cast_one] using hshift

/-- For `ρ > 0`, the shifted series `∑ 1/(ρ+n+1)²` is summable. -/
lemma summable_one_div_add_sq_succ (ρ : ℝ) (hρ : 0 < ρ) :
    Summable (fun t : ℕ => 1 / (ρ + ((t : ℝ) + 1)) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    summable_one_div_sq_add_one
  have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h2 : (n:ℝ) + 1 ≤ ρ + ((n:ℝ) + 1) := by linarith [le_of_lt hρ]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt h1) h2 2)

/-- For `ρ > 0`, `∑' n, 1/(ρ+n+1)² ≤ 2`. -/
lemma tsum_one_div_add_sq_succ_le_two (ρ : ℝ) (hρ : 0 < ρ) :
    ∑' t : ℕ, 1 / (ρ + ((t : ℝ) + 1)) ^ 2 ≤ 2 := by
  calc ∑' t : ℕ, 1 / (ρ + ((t : ℝ) + 1)) ^ 2
      ≤ ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := by
        refine Summable.tsum_le_tsum (fun t => ?_)
          (summable_one_div_add_sq_succ ρ hρ) summable_one_div_sq_add_one
        have h1 : (0:ℝ) < (t:ℝ) + 1 := by positivity
        have h2 : (t:ℝ) + 1 ≤ ρ + ((t:ℝ) + 1) := by linarith [le_of_lt hρ]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt h1) h2 2)
    _ ≤ 2 := tsum_one_div_sq_add_one_le_two

theorem tsum_int_one_div_sq_sep_le (α ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ k : ℤ, ρ ≤ |α - (k : ℝ)|) :
    ∑' k : ℤ, 1 / (α - (k : ℝ)) ^ 2 ≤ 2 / ρ ^ 2 + 4 := by
  have hρnn : 0 ≤ ρ := le_of_lt hρ
  -- an integer `m` with `m ≤ α < m + 1`
  obtain ⟨m, hm_le, hm_lt⟩ : ∃ m : ℤ, (m : ℝ) ≤ α ∧ α < (m : ℝ) + 1 :=
    ⟨⌊α⌋, Int.floor_le α, Int.lt_floor_add_one α⟩
  set a : ℝ := α - (m : ℝ) with ha
  have ha_nonneg : 0 ≤ a := by rw [ha]; linarith
  have ha_pos : 0 < a := by
    rcases lt_or_eq_of_le ha_nonneg with h | h
    · exact h
    · exfalso
      have h1 := hsep m
      rw [← ha] at h1
      rw [← h, abs_zero] at h1
      linarith
  have ha_ge : ρ ≤ a := by
    have h1 := hsep m
    rw [← ha, abs_of_nonneg ha_nonneg] at h1
    exact h1
  have ha_lt_one : a < 1 := by rw [ha]; linarith
  have hb_ge : ρ ≤ 1 - a := by
    have h1 := hsep (m + 1)
    have hcast : (((m + 1 : ℤ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h1
    have h2 : α - ((m : ℝ) + 1) = a - 1 := by rw [ha]; ring
    rw [h2] at h1
    have h3 : a - 1 < 0 := by linarith
    rw [abs_of_neg h3] at h1
    linarith
  -- shift the index of the sum by `m`, so the closest integer becomes `0`
  have hshift : ∑' n : ℤ, 1 / (a - (n : ℝ)) ^ 2 = ∑' k : ℤ, 1 / (α - (k : ℝ)) ^ 2 := by
    have h := Equiv.tsum_eq (Equiv.addRight m) (fun k : ℤ => 1 / (α - (k : ℝ)) ^ 2)
    rw [← h]
    apply tsum_congr
    intro n
    have h1 : (((Equiv.addRight m) n : ℤ) : ℝ) = (n : ℝ) + (m : ℝ) := by simp
    rw [h1]
    rw [show α - ((n:ℝ) + (m:ℝ)) = a - (n:ℝ) from by rw [ha]; ring]
  -- summable comparison series
  have hUsum : Summable (fun t : ℕ => 1 / (ρ + (t : ℝ)) ^ 2) := summable_one_div_add_sq ρ hρ
  have hUshift : Summable (fun t : ℕ => 1 / (ρ + ((t : ℝ) + 1)) ^ 2) :=
    summable_one_div_add_sq_succ ρ hρ
  have hS : ∑' t : ℕ, 1 / (ρ + ((t : ℝ) + 1)) ^ 2 ≤ 2 :=
    tsum_one_div_add_sq_succ_le_two ρ hρ
  -- the bound `1/(a - (n+1))² ≤ 1/(ρ + n)²`
  have hstep : ∀ n : ℕ, 1 / (a - ((n:ℝ) + 1)) ^ 2 ≤ 1 / (ρ + (n:ℝ)) ^ 2 := by
    intro n
    have hle : ρ + (n:ℝ) ≤ (n:ℝ) + 1 - a := by linarith
    have hp : (0:ℝ) < ρ + (n:ℝ) := by positivity
    have hx : a - ((n:ℝ) + 1) = -((n:ℝ) + 1 - a) := by ring
    have hsq : (a - ((n:ℝ) + 1)) ^ 2 = ((n:ℝ) + 1 - a) ^ 2 := by rw [hx, neg_sq]
    rw [hsq]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt hp) hle 2)
  -- the two halves are summable
  have hPtail : Summable (fun n : ℕ => 1 / (a - (((n : ℕ) + 1 : ℕ) : ℝ)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hUsum
    simpa only [Nat.cast_add, Nat.cast_one] using hstep n
  have hPsum : Summable (fun n : ℕ => 1 / (a - (n : ℝ)) ^ 2) :=
    (summable_nat_add_iff (f := fun s : ℕ => 1 / (a - (s : ℝ)) ^ 2) 1).mp hPtail
  have hQsum : Summable (fun n : ℕ => 1 / (a + ((n : ℝ) + 1)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hUshift
    have hle : ρ + ((n:ℝ) + 1) ≤ a + ((n:ℝ) + 1) := by linarith
    have hp : (0:ℝ) < ρ + ((n:ℝ) + 1) := by positivity
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt hp) hle 2)
  have hQsum' : Summable (fun n : ℕ => 1 / (a - ((((-((n : ℤ) + 1)) : ℤ)) : ℝ)) ^ 2) := by
    refine hQsum.congr (fun n => ?_)
    have h : ((((-((n : ℤ) + 1)) : ℤ)) : ℝ) = -((n:ℝ) + 1) := by push_cast; ring
    have hx : a + ((n:ℝ) + 1) = a - (-((n:ℝ) + 1)) := by ring
    rw [h, hx]
  -- split the `ℤ`-sum into two `ℕ`-sums
  have hsplit : ∑' k : ℤ, 1 / (α - (k : ℝ)) ^ 2
      = (∑' n : ℕ, 1 / (a - (n : ℝ)) ^ 2)
        + (∑' n : ℕ, 1 / (a + ((n : ℝ) + 1)) ^ 2) := by
    rw [← hshift]
    rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ => 1 / (a - (k : ℝ)) ^ 2) hPsum hQsum']
    have h1 : (∑' n : ℕ, (fun k : ℤ => 1 / (a - (k : ℝ)) ^ 2) (n : ℤ))
        = ∑' n : ℕ, 1 / (a - (n : ℝ)) ^ 2 :=
      tsum_congr (fun n => by simp)
    have h2 : (∑' n : ℕ, (fun k : ℤ => 1 / (a - (k : ℝ)) ^ 2) (-((n : ℤ) + 1)))
        = ∑' n : ℕ, 1 / (a + ((n : ℝ) + 1)) ^ 2 :=
      tsum_congr (fun n => by
        show 1 / (a - ((((-((n : ℤ) + 1)) : ℤ)) : ℝ)) ^ 2 = 1 / (a + ((n : ℝ) + 1)) ^ 2
        have h : ((((-((n : ℤ) + 1)) : ℤ)) : ℝ) = -((n:ℝ) + 1) := by push_cast; ring
        have hx : a - (-((n:ℝ) + 1)) = a + ((n:ℝ) + 1) := by ring
        rw [h, hx])
    rw [h1, h2]
  -- bound the positive half
  have hPbound : ∑' n : ℕ, 1 / (a - (n : ℝ)) ^ 2
      ≤ 2 / ρ ^ 2 + ∑' n : ℕ, 1 / (ρ + ((n : ℝ) + 1)) ^ 2 := by
    have h0 : 1 / (a - (((0:ℕ)) : ℝ)) ^ 2 ≤ 1 / ρ ^ 2 := by
      simp only [Nat.cast_zero, sub_zero]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt hρ) ha_ge 2)
    have htail : ∑' n : ℕ, 1 / (a - (((n : ℕ) + 1 : ℕ) : ℝ)) ^ 2
        ≤ ∑' n : ℕ, 1 / (ρ + (n : ℝ)) ^ 2 := by
      refine Summable.tsum_le_tsum (fun n => ?_) hPtail hUsum
      simpa only [Nat.cast_add, Nat.cast_one] using hstep n
    have hU : ∑' n : ℕ, 1 / (ρ + (n : ℝ)) ^ 2
        = 1 / ρ ^ 2 + ∑' n : ℕ, 1 / (ρ + ((n : ℝ) + 1)) ^ 2 := by
      rw [hUsum.tsum_eq_zero_add]
      congr 1
      · simp
      · apply tsum_congr; intro n
        simp only [Nat.cast_add, Nat.cast_one]
    rw [hPsum.tsum_eq_zero_add]
    have hcoef : (2:ℝ) / ρ ^ 2 = 1 / ρ ^ 2 + 1 / ρ ^ 2 := by ring
    linarith
  -- bound the negative half
  have hQbound : ∑' n : ℕ, 1 / (a + ((n : ℝ) + 1)) ^ 2
      ≤ ∑' n : ℕ, 1 / (ρ + ((n : ℝ) + 1)) ^ 2 := by
    refine Summable.tsum_le_tsum (fun n => ?_) hQsum hUshift
    have hle : ρ + ((n:ℝ) + 1) ≤ a + ((n:ℝ) + 1) := by linarith
    have hp : (0:ℝ) < ρ + ((n:ℝ) + 1) := by positivity
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt hp) hle 2)
  calc ∑' k : ℤ, 1 / (α - (k : ℝ)) ^ 2
      = (∑' n : ℕ, 1 / (a - (n : ℝ)) ^ 2)
        + (∑' n : ℕ, 1 / (a + ((n : ℝ) + 1)) ^ 2) := hsplit
    _ ≤ (2 / ρ ^ 2 + ∑' n : ℕ, 1 / (ρ + ((n : ℝ) + 1)) ^ 2)
        + ∑' n : ℕ, 1 / (ρ + ((n : ℝ) + 1)) ^ 2 := add_le_add hPbound hQbound
    _ ≤ 2 / ρ ^ 2 + 4 := by linarith

end Commons.Analysis.Real