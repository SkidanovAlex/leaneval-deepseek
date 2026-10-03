/-
# `Submission.Work.FIChain.Xf_sum_le_BformPi`

The aggregate `c`-sum of the `Π`-restricted window sums `Xf` is dominated by the `Π`-restricted
bilinear form `BformPi` at truncation `C = 1`:

  `∑_{c ≤ x} |Xf x Pz c N| ≤ BformPi x N 1 Pz`.

The proof is by an exact identification of the two sums.  For `c ≤ x`, the window sum
`Xf x Pz c N` is the sum over `n ∈ (N, 2N] ∩ (Icc 1 x)` with `c n ≤ x`, `(n,Π) = 1` of
`μ(n)·ã(cn)`; the `c`-th inner sum of `BformPi x N 1 Pz` is the same sum with the extra
coprimality condition `(n,c) = 1` and the extra factor `γ(n;1)`.  Both differences are immaterial:

* `γ(n;1) = ∑_{d | n, d ≤ 1} μ(d) = μ(1) = 1` for `n ≥ 1` (the only divisor `≤ 1` is `1`);
* a term with `(n,c) > 1` vanishes, because `p | n`, `p | c` force `p² | cn`, hence `cn` is not
  squarefree and `ã(cn) = μ(cn)²·a_{cn} = 0`.

So the two sums are in fact equal, and the inequality follows.

Everything is definitions plus the lemmas below (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The truncation factor `γ(n;1) = 1` -/

/-- `γ(n;1) = ∑_{d | n, d ≤ 1} μ(d) = 1` for `n ≥ 1`: the only divisor of `n` that is `≤ 1`
is `1` itself. -/
private lemma gammaTrunc_one_of_pos {n : ℕ} (hn : 1 ≤ n) : Work.FIPlan.gammaTrunc 1 n = 1 := by
  rw [Work.FIPlan.gammaTrunc]
  have hset : n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvd, hn0⟩, hle⟩
      have hd1 : d ≤ 1 := by exact_mod_cast hle
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      omega
    · rintro rfl
      exact ⟨⟨one_dvd n, by omega⟩, by norm_num⟩
  rw [hset, Finset.sum_singleton]
  norm_num [ArithmeticFunction.moebius_apply_one]

/-! ## 2. Terms with `(n,c) > 1` vanish -/

/-- From `¬ (a,b) = 1` and `a > 0` extract a prime dividing both `a` and `b`
(via `gcd a b ≠ 1`, which has a prime factor dividing both arguments). -/
private lemma exists_prime_dvd_of_not_coprime {a b : ℕ} (h : ¬ Nat.Coprime a b) (ha : 0 < a) :
    ∃ p, Nat.Prime p ∧ p ∣ a ∧ p ∣ b := by
  have hg : a.gcd b ≠ 1 := fun h1 => h (Nat.coprime_iff_gcd_eq_one.mpr h1)
  have hg0 : a.gcd b ≠ 0 := by
    intro h0
    have hm0 : a = 0 := Nat.eq_zero_of_zero_dvd (by rw [← h0]; exact Nat.gcd_dvd_left a b)
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left a b), hpd.trans (Nat.gcd_dvd_right a b)⟩

/-- If a prime divides both `a` and `b` and `ab ≠ 0`, then `ab` is not squarefree. -/
private lemma not_squarefree_mul_of_prime_dvd {p a b : ℕ} (hp : p.Prime) (ha : p ∣ a) (hb : p ∣ b)
    (h : a * b ≠ 0) : ¬ Squarefree (a * b) := by
  intro hsq
  have h2 : p * p ∣ a * b := by
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' * b', by ring⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) h2

/-- For `c ≥ 1`, `n ≥ 1` and `¬ (n,c) = 1`, the summand `μ(n)ã(cn)` vanishes: some prime `p`
divides both `n` and `c`, so `p² | cn`, `cn` is not squarefree, `μ(cn) = 0` and `ã(cn) = 0`. -/
private lemma mul_atilc_zero_of_not_coprime {c n : ℕ} (hc : 1 ≤ c) (hn : 1 ≤ n)
    (h : ¬ Nat.Coprime n c) :
    (ArithmeticFunction.moebius n : ℝ) * Work.FIChain.atilc (c * n) = 0 := by
  have hz : Work.FIChain.atilc (c * n) = 0 := by
    obtain ⟨p, hp, hpn, hpc⟩ := exists_prime_dvd_of_not_coprime h (by omega)
    have hmu : ArithmeticFunction.moebius (c * n) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (not_squarefree_mul_of_prime_dvd hp hpc hpn (Nat.mul_ne_zero (by omega) (by omega)))
    simp [Work.FIChain.atilc, Work.FITop.atilFIa, Submission.ASP.atil, hmu]
  rw [hz, mul_zero]

/-! ## 3. The cast bookkeeping between the `ℝ`-window and the `ℕ`-window -/

/-- `(n : ℝ) ≤ 2 · (N : ℝ) ↔ n ≤ 2N`. -/
private lemma real_le_two_mul_iff (n N : ℕ) : ((n : ℝ) ≤ 2 * (N : ℝ)) ↔ n ≤ 2 * N := by
  rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Nat.cast_le]

/-! ## 4. `Xf` as a `filter`ed sum matching the inner sum of `BformPi` -/

/-- `Xf x Pz c N` rewritten as the sum over the `filter`ed `n`-set of the `c`-th inner sum of
`BformPi x N 1 Pz`: the window conditions are `N < n ≤ 2N` and `c n ≤ x`, and the index set
`(Icc 1 x)` may be replaced by `(Icc 1 (2N))` because `c ≥ 1` and `c n ≤ x` force `n ≤ x`.
The coprimality condition `(n,c) = 1` is added for free since the complementary terms vanish. -/
private lemma Xf_eq_filter (x N Pz c : ℕ) (hc : 1 ≤ c) :
    Work.FIChain.Xf x Pz c (N : ℝ) =
      ∑ n ∈ (Finset.Icc 1 (2 * N)).filter
        (fun n => N < n ∧ c * n ≤ x ∧ Nat.Coprime n c ∧ Work.FITop4.PiCond Pz n),
        (ArithmeticFunction.moebius n : ℝ) * Work.FIChain.atilc (c * n) := by
  have hle : ∀ n : ℕ, 1 ≤ n → 1 ≤ c → n ≤ c * n := by
    intro m hm hc1
    calc m = 1 * m := (one_mul m).symm
      _ ≤ c * m := Nat.mul_le_mul_right m hc1
  rw [Work.FIChain.Xf]
  trans ∑ n ∈ ((Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ (N : ℝ) < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * (N : ℝ) ∧
          Work.FITop4.PiCond Pz n)).filter (fun n => Nat.Coprime n c),
      (ArithmeticFunction.moebius n : ℝ) * Work.FIChain.atilc (c * n)
  · conv_rhs => rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n hn => by
      by_cases h : Nat.Coprime n c
      · simp [h]
      · rw [if_neg h]
        exact mul_atilc_zero_of_not_coprime hc (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1 h)
  · refine Finset.sum_congr ?_ (fun n _ => rfl)
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hn1, hnx⟩, hcn, hNn, hn2N, hPi⟩, hcop⟩
      exact ⟨⟨hn1, (real_le_two_mul_iff n N).mp hn2N⟩, Nat.cast_lt.mp hNn, hcn, hcop, hPi⟩
    · rintro ⟨⟨hn1, hn2N⟩, hNn, hcn, hcop, hPi⟩
      exact ⟨⟨⟨hn1, le_trans (hle n hn1 hc) hcn⟩, hcn, Nat.cast_lt.mpr hNn,
              (real_le_two_mul_iff n N).mpr hn2N, hPi⟩, hcop⟩

/-! ## 5. The target -/

theorem Xf_sum_le_BformPi (x N Pz : ℕ) :
    (∑ c ∈ Finset.Icc 1 x, |Work.FIChain.Xf x Pz c (N : ℝ)|) ≤ Work.FITop.BformPi x N 1 Pz := by
  refine Finset.sum_le_sum (fun c hc => ?_)
  rw [Xf_eq_filter x N Pz c (Finset.mem_Icc.mp hc).1]
  conv_rhs => rw [← Finset.sum_filter]
  refine le_of_eq (congrArg abs ?_)
  refine Finset.sum_congr
    (Finset.filter_congr (fun n _ => by simp only [Work.FITop4.PiCond])) (fun n hn => ?_)
  rw [gammaTrunc_one_of_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1]
  simp [Work.FIChain.atilc]

end

end Work.FIChain
