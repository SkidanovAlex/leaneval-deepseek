import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.LinnikAreas.Density4.LamRDefs

/-!
# The truncated Möbius sums `Qm`, `Dl` and the real/integer cut-off dictionary

`Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` (`bvDefs`) is Jutila's truncated von Mangoldt sum
with a *real* cut-off `z`, while `Commons.NumberTheory.Sieve.LambdaR k n` is the same object with
an *integer* cut-off `k`.  The two are compared here through the two truncated Möbius sums

  `Qm T n = Σ_{d ∣ n, d ≤ T} μ(d)`,   `Dl T n = Σ_{d ∣ n, d ≤ T} μ(d)·log d`,

by the elementary splitting `log(z/d) = log z − log d`:

  `Lz z n = log z · Qm ⌊z⌋₊ n − Dl ⌊z⌋₊ n`   (`0 < z`),

and the corresponding integer identity

  `Λ_{T+1}(n) = log(T+1) · Qm T n − Dl T n`

(in which the `d = T+1` term cancels because `log((T+1)/(T+1)) = 0`).  Subtracting gives the
dictionary used in the proof of `LzSqLower`:

  `Lz z n = Λ_{⌊z⌋₊+1}(n) − log((⌊z⌋₊+1)/z)·Qm ⌊z⌋₊ n`.

Everything in this file is elementary.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **Truncated Möbius divisor sum.** `Qm T n = Σ_{d ∣ n, d ≤ T} μ(d)`
(the integer-cut-off version of `P T n` of `bvDefs`). -/
def Qm (T n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T), (ArithmeticFunction.moebius d : ℝ)

/-- **Truncated Möbius-log divisor sum.** `Dl T n = Σ_{d ∣ n, d ≤ T} μ(d)·log d`. -/
def Dl (T n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T), (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)

/-- The divisor filters of the real cut-off `z ≥ 0` and of the integer cut-off `⌊z⌋₊` agree. -/
lemma filter_le_floor (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
      = n.divisors.filter (fun d : ℕ => d ≤ ⌊z⌋₊) := by
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hle⟩
    exact ⟨hd, Nat.le_floor hle⟩
  · rintro ⟨hd, hle⟩
    exact ⟨hd, le_trans (by exact_mod_cast hle) (Nat.floor_le hz)⟩

/-- For a natural cut-off `k`, `Lz (k : ℝ)` is Mathlib's `LambdaR k`. -/
lemma Lz_natCast_eq_LambdaR (k n : ℕ) :
    Lz (k : ℝ) n = Commons.NumberTheory.Sieve.LambdaR k n := by
  rw [Lz, Commons.NumberTheory.Sieve.LambdaR]
  refine Finset.sum_congr ?_ (fun d _ => ?_)
  · ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hle⟩; exact ⟨hd, by exact_mod_cast hle⟩
    · rintro ⟨hd, hle⟩; exact ⟨hd, by exact_mod_cast hle⟩
  · simp

/-- **Splitting the logarithm.**  `Lz z n = log z · Qm ⌊z⌋₊ n − Dl ⌊z⌋₊ n` for `0 < z`. -/
lemma Lz_eq_log_mul_Qm_sub_Dl (z : ℝ) (hz : 0 < z) (n : ℕ) :
    Lz z n = Real.log z * Qm ⌊z⌋₊ n - Dl ⌊z⌋₊ n := by
  have hz0 : z ≠ 0 := hz.ne'
  rw [Lz, Qm, Dl, filter_le_floor z (le_of_lt hz) n, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    exact_mod_cast this.ne'
  rw [Real.log_div hz0 hd0]
  ring

/-- **Splitting the logarithm, integer cut-off.**  `Λ_k(n) = log k · Qm k n − Dl k n`
for `0 < k`. -/
lemma LambdaR_eq_log_mul_Qm_sub_Dl (k : ℕ) (hk : 0 < k) (n : ℕ) :
    Commons.NumberTheory.Sieve.LambdaR k n = Real.log (k : ℝ) * Qm k n - Dl k n := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Commons.NumberTheory.Sieve.LambdaR, Qm, Dl, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    exact_mod_cast this.ne'
  rw [Real.log_div hk0 hd0]
  ring

/-- Adding the divisor `T+1` to the truncated Möbius sum `Qm` (for `n ≠ 0`). -/
lemma Qm_add_one (T n : ℕ) (hn : n ≠ 0) : Qm (T + 1) n
    = Qm T n + (if (T + 1) ∣ n then (ArithmeticFunction.moebius (T + 1) : ℝ) else 0) := by
  classical
  have hset : n.divisors.filter (fun d : ℕ => d ≤ T + 1)
      = n.divisors.filter (fun d : ℕ => d ≤ T) ∪ (if (T + 1) ∣ n then {T + 1} else ∅) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_union, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvd, hd0⟩, hle⟩
      rcases lt_or_ge d (T + 1) with h | h
      · exact Or.inl ⟨⟨hdvd, hd0⟩, by omega⟩
      · refine Or.inr ?_
        have hdT : d = T + 1 := by omega
        subst hdT
        simp [hdvd]
    · rintro (⟨⟨hdvd, hd0⟩, hle⟩ | h)
      · exact ⟨⟨hdvd, hd0⟩, by omega⟩
      · by_cases hdiv : (T + 1) ∣ n
        · rw [if_pos hdiv] at h
          simp only [Finset.mem_singleton] at h
          subst h
          exact ⟨⟨hdiv, hn⟩, le_rfl⟩
        · rw [if_neg hdiv] at h
          exact absurd h (by simp)
  have hdisj : Disjoint (n.divisors.filter (fun d : ℕ => d ≤ T))
      (if (T + 1) ∣ n then {T + 1} else ∅) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [Finset.mem_filter] at hd1
    by_cases hdiv : (T + 1) ∣ n
    · rw [if_pos hdiv] at hd2
      simp only [Finset.mem_singleton] at hd2
      omega
    · rw [if_neg hdiv] at hd2
      exact absurd hd2 (by simp)
  rw [Qm, hset, Finset.sum_union hdisj]
  congr 1
  by_cases hdiv : (T + 1) ∣ n
  · rw [if_pos hdiv, if_pos hdiv, Finset.sum_singleton]
  · rw [if_neg hdiv, if_neg hdiv, Finset.sum_empty]

/-- Adding the divisor `T+1` to the truncated Möbius-log sum `Dl` (for `n ≠ 0`). -/
lemma Dl_add_one (T n : ℕ) (hn : n ≠ 0) : Dl (T + 1) n
    = Dl T n
      + (if (T + 1) ∣ n then
          (ArithmeticFunction.moebius (T + 1) : ℝ) * Real.log (((T + 1 : ℕ)) : ℝ) else 0) := by
  classical
  have hset : n.divisors.filter (fun d : ℕ => d ≤ T + 1)
      = n.divisors.filter (fun d : ℕ => d ≤ T) ∪ (if (T + 1) ∣ n then {T + 1} else ∅) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_union, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvd, hd0⟩, hle⟩
      rcases lt_or_ge d (T + 1) with h | h
      · exact Or.inl ⟨⟨hdvd, hd0⟩, by omega⟩
      · refine Or.inr ?_
        have hdT : d = T + 1 := by omega
        subst hdT
        simp [hdvd]
    · rintro (⟨⟨hdvd, hd0⟩, hle⟩ | h)
      · exact ⟨⟨hdvd, hd0⟩, by omega⟩
      · by_cases hdiv : (T + 1) ∣ n
        · rw [if_pos hdiv] at h
          simp only [Finset.mem_singleton] at h
          subst h
          exact ⟨⟨hdiv, hn⟩, le_rfl⟩
        · rw [if_neg hdiv] at h
          exact absurd h (by simp)
  have hdisj : Disjoint (n.divisors.filter (fun d : ℕ => d ≤ T))
      (if (T + 1) ∣ n then {T + 1} else ∅) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [Finset.mem_filter] at hd1
    by_cases hdiv : (T + 1) ∣ n
    · rw [if_pos hdiv] at hd2
      simp only [Finset.mem_singleton] at hd2
      omega
    · rw [if_neg hdiv] at hd2
      exact absurd hd2 (by simp)
  rw [Dl, hset, Finset.sum_union hdisj]
  congr 1
  by_cases hdiv : (T + 1) ∣ n
  · rw [if_pos hdiv, if_pos hdiv, Finset.sum_singleton]
  · rw [if_neg hdiv, if_neg hdiv, Finset.sum_empty]

/-- **The `T+1` term cancels.**  `Λ_{T+1}(n) = log(T+1)·Qm T n − Dl T n`: the extra divisor
`d = T+1` of the full sum carries `log((T+1)/(T+1)) = 0`. -/
lemma LambdaR_succ_eq (T n : ℕ) :
    Commons.NumberTheory.Sieve.LambdaR (T + 1) n
      = Real.log ((T : ℝ) + 1) * Qm T n - Dl T n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Commons.NumberTheory.Sieve.LambdaR, Qm, Dl]
  · have hn' : n ≠ 0 := by omega
    have hcast : (((T + 1 : ℕ)) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
    rw [LambdaR_eq_log_mul_Qm_sub_Dl (T + 1) (by omega) n, Qm_add_one T n hn',
      Dl_add_one T n hn', hcast]
    by_cases hdiv : (T + 1) ∣ n
    · rw [if_pos hdiv, if_pos hdiv]; ring
    · rw [if_neg hdiv, if_neg hdiv]; ring

/-- **The real/integer cut-off dictionary.**  For `0 < z` and every `n`,

  `Lz z n = Λ_{⌊z⌋₊+1}(n) − log((⌊z⌋₊+1)/z)·Qm ⌊z⌋₊ n`. -/
lemma Lz_eq_LambdaR_floor_add_one (z : ℝ) (hz : 0 < z) (n : ℕ) :
    Lz z n = Commons.NumberTheory.Sieve.LambdaR (⌊z⌋₊ + 1) n
      - Real.log (((⌊z⌋₊ : ℝ) + 1) / z) * Qm ⌊z⌋₊ n := by
  have hlog : Real.log (((⌊z⌋₊ : ℝ) + 1) / z)
      = Real.log ((⌊z⌋₊ : ℝ) + 1) - Real.log z :=
    Real.log_div (by positivity) (ne_of_gt hz)
  rw [Lz_eq_log_mul_Qm_sub_Dl z hz n, LambdaR_succ_eq, hlog]
  ring

end

end Work.ZeroDensity.Jutila
