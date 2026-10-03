import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25

namespace Work.FITop

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `γ(n;1) = ∑_{d ∣ n, d ≤ 1} μ(d) = 1` for `n ≥ 1`: the only divisor `d ≤ 1` of `n > 0`
is `d = 1`, and `μ 1 = 1`. -/
lemma gammaTrunc_one (n : ℕ) (hn : 1 ≤ n) : Work.FIPlan.gammaTrunc 1 n = 1 := by
  rw [Work.FIPlan.gammaTrunc]
  have hn0 : n ≠ 0 := by omega
  have hset : n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hd1⟩
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdpos : 1 ≤ d := Nat.one_le_of_lt (Nat.pos_of_dvd_of_pos hdvd (by omega))
      have hdle : d ≤ 1 := by exact_mod_cast hd1
      omega
    · rintro rfl
      exact ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩, by norm_num⟩
  rw [hset, Finset.sum_singleton]
  norm_num

/-- For the squarefree-supported sequence `ã = μ² a` the factor `μ(n)γ(n;1)ã(mn)` vanishes
whenever `(n,m) ≠ 1`: if a prime divides both, then `p² ∣ nm`, so `nm` is not squarefree and
`ã(nm) = μ(nm)² a(nm) = 0`. -/
lemma atilFIa_mul_eq_zero_of_not_coprime (n m : ℕ) (h : ¬ Nat.Coprime n m) :
    atilFIa (n * m) = 0 := by
  rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  have hns : ¬ Squarefree (n * m) := by
    intro hs
    have h2 := Nat.squarefree_iff_prime_squarefree.mp hs
    have hg : Nat.gcd n m ≠ 1 := fun hc => h ((Nat.coprime_iff_gcd_eq_one).mpr hc)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have hpn : p ∣ n := (Nat.dvd_gcd_iff.mp hpd).1
    have hpm : p ∣ m := (Nat.dvd_gcd_iff.mp hpd).2
    exact h2 p hp (mul_dvd_mul hpn hpm)
  have hmu : ArithmeticFunction.moebius (n * m) = 0 := by
    by_contra hc
    exact hns ((ArithmeticFunction.moebius_ne_zero_iff_squarefree).mp hc)
  rw [hmu]
  simp

/-- The `n`-index set of `BformAtil` (`1 ≤ n ≤ 2N`, `N < n`, `mn ≤ x`, `(n,m) = 1`) and the
`b`-index set of `Xsum` (`1 ≤ b ≤ x`, `N < b`, `b ≤ 2N`, `bm ≤ x`) coincide when `m ≥ 1`:
`mn ≤ x` forces `n ≤ x`. -/
lemma bformAtil_filter_eq (x N m : ℕ) (hm : 0 < m) :
    (Finset.Icc 1 x).filter
        (fun b : ℕ => (N : ℝ) < (b : ℝ) ∧ (b : ℝ) ≤ 2 * (N : ℝ) ∧ b * m ≤ x)
      = (Finset.Icc 1 (2 * N)).filter (fun n : ℕ => N < n ∧ m * n ≤ x) := by
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
    · have h : (b : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by rw [hcast]; exact h3
      exact_mod_cast h
    · exact_mod_cast h2
    · rwa [mul_comm]
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, ?_, ?_⟩
    · have h4' : b * m ≤ x := by rwa [mul_comm]
      have h5 : b ≤ b * m := Nat.le_mul_of_pos_right b hm
      omega
    · exact_mod_cast h3
    · have h : (b : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast h2
      rwa [hcast] at h
    · rwa [mul_comm]

/-- **The inner-sum identity of `BformAtilEqXsum`.**  For `m ≥ 1` the `n`-sum of `BformAtil`
(with `C = 1`) equals the `(B′)`-shape inner sum `Xsum atilFIa x m N (2N)`.

The `n`-index set of `BformAtil` is `1 ≤ n ≤ 2N` with `N < n`, `mn ≤ x`, `(n,m) = 1`; the
`b`-index set of `Xsum` is `1 ≤ b ≤ x` with `N < b`, `b ≤ 2N`, `bm ≤ x`.  By
`bformAtil_filter_eq` the two sets coincide; and the coprimality condition is redundant,
because for `(n,m) ≠ 1` the factor `ã(mn)` vanishes (`atilFIa_mul_eq_zero_of_not_coprime`). -/
lemma inner_sum_eq (x N m : ℕ) (hm : 1 ≤ m) :
    (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m then
          (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc 1 n * atilFIa (m * n)
        else 0))
      = ∑ b ∈ Finset.Icc 1 x,
        (if (N : ℝ) < (b : ℝ) ∧ (b : ℝ) ≤ 2 * (N : ℝ) ∧ b * m ≤ x then
          (ArithmeticFunction.moebius b : ℝ) * atilFIa (b * m) else 0) := by
  have hmpos : 0 < m := hm
  have hS := bformAtil_filter_eq x N m hmpos
  have hL : (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m then
          (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc 1 n * atilFIa (m * n)
        else 0))
      = ∑ n ∈ (Finset.Icc 1 (2 * N)).filter (fun n : ℕ => N < n ∧ m * n ≤ x),
          (ArithmeticFunction.moebius n : ℝ) * atilFIa (n * m) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [gammaTrunc_one n hn1, mul_one]
    by_cases hP : N < n ∧ m * n ≤ x
    · by_cases hc : Nat.Coprime n m
      · rw [if_pos ⟨hP.1, hP.2, hc⟩, if_pos hP, mul_comm m n]
      · rw [if_neg (fun h => hc h.2.2), if_pos hP,
            atilFIa_mul_eq_zero_of_not_coprime n m hc, mul_zero]
    · rw [if_neg (fun h => hP ⟨h.1, h.2.1⟩), if_neg hP]
  have hR : (∑ b ∈ Finset.Icc 1 x,
        (if (N : ℝ) < (b : ℝ) ∧ (b : ℝ) ≤ 2 * (N : ℝ) ∧ b * m ≤ x then
          (ArithmeticFunction.moebius b : ℝ) * atilFIa (b * m) else 0))
      = ∑ n ∈ (Finset.Icc 1 (2 * N)).filter (fun n : ℕ => N < n ∧ m * n ≤ x),
          (ArithmeticFunction.moebius n : ℝ) * atilFIa (n * m) := by
    rw [← Finset.sum_filter]
    rw [hS]
  exact hL.trans hR.symm

/-- The `Prop41Statement` bilinear form `BformAtil x N C` with `C = 1` is exactly the
sum of the absolute values of the `(B′)`-shape inner sums `Xsum` on the integer window
`(N, 2N]`.  Proof route: `gammaTrunc 1 n = 1` for `n ≥ 1`; the coprimality condition
`Nat.Coprime n m` in `BformAtil` is redundant for the sequence `atilFIa` (if `¬ Nat.Coprime n m`
then `p ∣ n`, `p ∣ m` for some prime `p`, hence `p ^ 2 ∣ m * n` and `atilFIa (m * n) = 0`);
`n ∈ Icc 1 (2*N)` with `N < n` is `n ∈ (N, 2N]`, and `m * n ≤ x` with `m ≥ 1` forces `n ≤ x`,
so the index sets of the two sums agree.  (Cf. the proved lemma `BformAtil_one_eq` in
`Submission/Work/FITop/ScratchBW.lean`, which assumes additionally `2*N ≤ x`.) -/
theorem BformAtilEqXsum (x N : ℕ) :
    BformAtil x N 1 =
      ∑ m ∈ Finset.Icc 1 x,
        |Submission.ASP.Xsum atilFIa x m (N : ℝ) (2 * (N : ℝ))| := by
  rw [Work.FITop.BformAtil]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  rw [Submission.ASP.Xsum, Finset.sum_filter]
  congr 1
  exact inner_sum_eq x N m hm1

end

end Work.FITop
