import Mathlib
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea3.JointCount.joint_sum_le_double

namespace Work.FIArea3

/-- **`FI` Lemma 2.2 at `k = 4`: `τ(m)² ≤ 256² · Σ_{1 ≤ d ≤ K, d ∣ m} τ(d)¹⁶` for `m ≤ K⁴`.**

`Work.FIArea3.lemma_2_2` supplies a divisor `d ∣ m` with `d⁴ ≤ m` and
`τ(m) ≤ (2τ(d))⁸ = 256·τ(d)⁸`; from `d⁴ ≤ m ≤ K⁴` we get `d ≤ K`, so `τ(d)¹⁶` is one of the
summed terms (which, when it is not present, contributes `0`). Squaring gives the claim. -/
theorem tau_sq_trunc (m K : ℕ) (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    (((m.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
      ≤ (256 : ℝ) ^ (2 : ℕ) * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: `τ(0) = 0`, and the right-hand side is nonnegative.
    subst hm
    have h0 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ 0 then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
    have hzero : ((((Finset.card (∅ : Finset ℕ) : ℕ)) : ℝ)) ^ (2 : ℕ) = 0 := by simp
    rw [Nat.divisors_zero, hzero]
    exact mul_nonneg (by norm_num) h0
  · -- `m ≥ 1`: apply `FI` Lemma 2.2 with `k = 4`.
    obtain ⟨d, hdvd, hdk, hbound⟩ := Work.FIArea3.lemma_2_2 (k := 4) (by norm_num) hm
    rw [Work.FIArea3.exp_eq_eight] at hbound
    rw [Real.rpow_natCast] at hbound
    have hd4 : ((d : ℝ)) ^ 4 ≤ (m : ℝ) := by exact_mod_cast hdk
    have hdK4 : ((d : ℝ)) ^ 4 ≤ (K : ℝ) ^ 4 := le_trans hd4 h
    have hdK : d ≤ K := by
      have hle := (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ (d : ℝ) by positivity)
        (show (0 : ℝ) ≤ (K : ℝ) by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp hdK4
      exact_mod_cast hle
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm
    have hmem : d ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hd1, hdK⟩
    have hsingle : (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)
        ≤ ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
      Finset.single_le_sum (s := Finset.Icc 1 K)
        (f := fun d' => if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)
        (fun i _ => by split_ifs <;> positivity) hmem
    rw [if_pos hdvd] at hsingle
    have h2 : (2 * (d.divisors.card : ℝ)) ^ (8 : ℕ)
        = 256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ) := by ring
    rw [h2] at hbound
    have hbound2 : ((m.divisors.card : ℝ)) ^ (2 : ℕ)
        ≤ (256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hbound 2
    have h16 : (256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ)) ^ (2 : ℕ)
        = (256 : ℝ) ^ (2 : ℕ) * ((d.divisors.card : ℝ)) ^ (16 : ℕ) := by ring
    rw [h16] at hbound2
    calc ((m.divisors.card : ℝ)) ^ (2 : ℕ)
        ≤ (256 : ℝ) ^ (2 : ℕ) * ((d.divisors.card : ℝ)) ^ (16 : ℕ) := hbound2
      _ ≤ (256 : ℝ) ^ (2 : ℕ) * ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
          mul_le_mul_of_nonneg_left hsingle (by positivity)

end Work.FIArea3
