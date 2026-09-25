import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.Identity

open Finset

/-- The partial sum `∑_{k=1}^{e} 1/(k p^k)` is bounded by the full series
`-log(1 - 1/p) = ∑_{k ≥ 1} 1/(k p^k)`, whose terms are all nonnegative. -/
lemma sum_Icc_inv_mul_pow_le_neg_log {p e : ℕ} (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 1 e, 1 / ((k : ℝ) * (p : ℝ) ^ k) ≤ -Real.log (1 - 1 / (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hy_abs : |(1 : ℝ) / (p : ℝ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hpR]
    exact_mod_cast hp
  have hmain := Real.hasSum_pow_div_log_of_abs_lt_one hy_abs
  set f : ℕ → ℝ := fun k => 1 / ((k : ℝ) * (p : ℝ) ^ k) with hf
  have hshift : HasSum (fun n : ℕ => f (n + 1)) (-Real.log (1 - 1 / (p : ℝ))) := by
    convert hmain using 1
    ext n
    simp only [hf]
    rw [one_div_pow]
    push_cast
    field_simp
  have hf0 : f 0 = 0 := by simp [hf]
  have hfsum : HasSum f (-Real.log (1 - 1 / (p : ℝ))) := by
    refine (hasSum_nat_add_iff' (f := f) (g := -Real.log (1 - 1 / (p : ℝ))) 1).mp ?_
    simpa [Finset.sum_range_one, hf0] using hshift
  have hle := hfsum.summable.sum_le_tsum (Finset.Icc 1 e)
    (fun i _ => by simp only [hf]; positivity)
  rwa [hfsum.tsum_eq] at hle

/-- Each summand of `primeTail` is the tail `Σ_{k>e_p} 1/(k p^k)` of the positive series
`-log(1-1/p) = Σ_{k≥1} 1/(k p^k)`, hence nonnegative. -/
theorem primeTail_nonneg (x : ℝ) (hx : 2 ≤ x) : 0 ≤ Work.RHContract.primeTail x := by
  rw [Work.RHContract.primeTail_eq_sum]
  refine Finset.sum_nonneg fun p hp => ?_
  have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp
  have h := sum_Icc_inv_mul_pow_le_neg_log (p := p) (e := Nat.log p ⌊x⌋₊) hp2
  simp only [Work.RHContract.primeTailSummand]
  linarith

end Work.RHContract.Identity
