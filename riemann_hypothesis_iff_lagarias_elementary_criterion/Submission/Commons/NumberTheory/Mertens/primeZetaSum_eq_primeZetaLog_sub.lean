import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.SumPrimeReciprocals
import Submission.Commons.Analysis.ExpLog.log_one_sub_le

namespace Commons.NumberTheory.Mertens

private lemma primeRpow_pos {s : ℝ} (p : Nat.Primes) :
    0 < ((p : ℕ) : ℝ) ^ (-s) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.Prime.pos p.property)
  simpa using Real.rpow_pos_of_pos hp0 (-s)

private lemma primeRpow_le_half {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-s) ≤ (1 : ℝ) / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le p.property)
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hle : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_le_rpow_left_iff hp1]
    linarith
  have hle2 : (p : ℝ) ^ (-1 : ℝ) ≤ (1 : ℝ) / 2 := by
    rw [Real.rpow_neg hp_nonneg 1, Real.rpow_one]
    simpa [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  simpa using hle.trans hle2

private lemma primeLogTerm_nonneg {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    0 ≤ -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) := by
  have hx1 : ((p : ℕ) : ℝ) ^ (-s) < 1 := (primeRpow_le_half hs p).trans_lt (by norm_num)
  have h1mx : 0 < 1 - ((p : ℕ) : ℝ) ^ (-s) := sub_pos.mpr hx1
  have hle1 : 1 - ((p : ℕ) : ℝ) ^ (-s) ≤ 1 := by
    have hx0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-s) := le_of_lt (primeRpow_pos p)
    linarith
  have hlog : Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) ≤ 0 := by
    exact (Real.log_nonpos_iff (le_of_lt h1mx)).mpr hle1
  linarith

private lemma primeLogTerm_le_two_mul {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) ≤
      2 * ((p : ℕ) : ℝ) ^ (-s) := by
  have hx0 : 0 < ((p : ℕ) : ℝ) ^ (-s) := primeRpow_pos p
  have hx1 : ((p : ℕ) : ℝ) ^ (-s) < 1 := (primeRpow_le_half hs p).trans_lt (by norm_num)
  have hmain := Commons.Analysis.ExpLog.log_one_sub_le hx0 hx1
  have h1mx : 0 < 1 - ((p : ℕ) : ℝ) ^ (-s) := sub_pos.mpr hx1
  have hdiv : ((p : ℕ) : ℝ) ^ (-s) / (1 - ((p : ℕ) : ℝ) ^ (-s)) ≤
      2 * ((p : ℕ) : ℝ) ^ (-s) := by
    rw [div_le_iff₀ h1mx]
    nlinarith [primeRpow_le_half hs p]
  exact hmain.trans hdiv

private lemma primeLogTerm_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) := by
  have hf : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s)) := by
    simpa using (Nat.Primes.summable_rpow (r := -s)).mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun p => primeLogTerm_nonneg hs p)
    (fun p => primeLogTerm_le_two_mul hs p) (hf.mul_left 2)

lemma primeZetaSum_eq_primeZetaLog_sub {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)) =
      (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) -
      (∑' p : Nat.Primes,
        (-Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s))) := by
  let f : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-s)
  let A : Nat.Primes → ℝ := fun p => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))
  have hf : Summable f := by
    dsimp [f]
    simpa using (Nat.Primes.summable_rpow (r := -s)).mpr (by linarith)
  have hA : Summable A := by
    dsimp [A]
    exact primeLogTerm_summable hs
  have hAsub : (∑' p : Nat.Primes, (A p - f p)) = (∑' p : Nat.Primes, A p) - (∑' p : Nat.Primes, f p) :=
    Summable.tsum_sub hA hf
  have hgoal : (∑' p : Nat.Primes, f p) = (∑' p : Nat.Primes, A p) -
      (∑' p : Nat.Primes, (A p - f p)) := by
    rw [hAsub]
    ring
  simpa [f, A] using hgoal

end Commons.NumberTheory.Mertens