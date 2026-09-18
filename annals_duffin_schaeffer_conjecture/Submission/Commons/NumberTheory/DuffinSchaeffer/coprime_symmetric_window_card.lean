import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Commons.NumberTheory.DuffinSchaeffer

/-- Reindex a symmetric integer window `[-W, W]` by absolute value: each nonzero
absolute value `m ∈ [1, W]` is attained twice (`±m`), and `0` once. -/
private lemma sum_symm_window (W : ℕ) (F : ℕ → ℤ) :
    (∑ e ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), F e.natAbs) =
      F 0 + 2 * (∑ m ∈ Finset.Icc 1 W, F m) := by
  classical
  induction W with
  | zero => simp
  | succ W ih =>
      have hI : Finset.Icc (-((W : ℤ) + 1)) ((W : ℤ) + 1) =
          insert ((W : ℤ) + 1)
            (insert (-((W : ℤ) + 1)) (Finset.Icc (-(W : ℤ)) (W : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        constructor <;> intro hx <;> omega
      have htopAbs : (((W : ℤ) + 1).natAbs) = W + 1 := by
        have hz : 0 ≤ (W : ℤ) + 1 := by omega
        have hcast : ((((W : ℤ) + 1).natAbs : ℕ) : ℤ) = (W : ℤ) + 1 := Int.natAbs_of_nonneg hz
        have hcast' : ((((W : ℤ) + 1).natAbs : ℕ) : ℤ) = ((W + 1 : ℕ) : ℤ) := by simpa using hcast
        exact_mod_cast hcast'
      have hbotAbs : ((-((W : ℤ) + 1)).natAbs) = W + 1 := by
        rw [Int.natAbs_neg, htopAbs]
      have hJ : Finset.Icc 1 (W + 1) = insert (W + 1) (Finset.Icc 1 W) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        constructor <;> intro hx <;> omega
      calc
        (∑ e ∈ Finset.Icc (-((W : ℤ) + 1)) ((W : ℤ) + 1), F e.natAbs)
            = (∑ e ∈ insert ((W : ℤ) + 1)
                  (insert (-((W : ℤ) + 1)) (Finset.Icc (-(W : ℤ)) (W : ℤ))), F e.natAbs) := by rw [hI]
        _ = F (((W : ℤ) + 1).natAbs) +
              (∑ e ∈ insert (-((W : ℤ) + 1)) (Finset.Icc (-(W : ℤ)) (W : ℤ)), F e.natAbs) := by
                rw [Finset.sum_insert]
                intro hx
                rw [Finset.mem_insert] at hx
                rcases hx with hx | hx
                · omega
                · rw [Finset.mem_Icc] at hx
                  omega
        _ = F (((W : ℤ) + 1).natAbs) +
              (F ((-((W : ℤ) + 1)).natAbs) +
                (∑ e ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), F e.natAbs)) := by
                rw [Finset.sum_insert]
                intro hx
                rw [Finset.mem_Icc] at hx
                omega
        _ = F (W + 1) + (F (W + 1) +
              (∑ e ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), F e.natAbs)) := by
                rw [htopAbs, hbotAbs]
        _ = F (W + 1) + (F (W + 1) + (F 0 + 2 * (∑ m ∈ Finset.Icc 1 W, F m))) := by
                rw [ih]
        _ = F 0 + 2 * (F (W + 1) + (∑ m ∈ Finset.Icc 1 W, F m)) := by ring
        _ = F 0 + 2 * (∑ m ∈ Finset.Icc 1 (W + 1), F m) := by
                rw [hJ]
                rw [Finset.sum_insert]
                intro hx
                rw [Finset.mem_Icc] at hx
                omega

/-- The number of `c ∈ [1,C]` coprime to `N` (as integers): `Σ_{d | N} μ(d)·(C/d)`. -/
private lemma coprime_count_Icc_one (C N : ℕ) (hN : 1 ≤ N) :
    (((Finset.Icc 1 C).filter (fun c : ℕ => c.gcd N = 1)).card : ℤ) =
      ∑ d ∈ N.divisors, μ d * ((C / d : ℕ) : ℤ) := by
  classical
  calc
    (((Finset.Icc 1 C).filter (fun c : ℕ => c.gcd N = 1)).card : ℤ)
        = ∑ c ∈ Finset.Icc 1 C, (if c.gcd N = 1 then (1 : ℤ) else 0) := by
            rw [Finset.natCast_card_filter]
    _ = ∑ c ∈ Finset.Icc 1 C, (∑ d ∈ (c.gcd N).divisors, μ d) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            have hs := Commons.NumberTheory.Totient.sum_moebius_gcd_coprime c N
            simpa [Nat.Coprime] using hs.symm
    _ = ∑ c ∈ Finset.Icc 1 C, (∑ d ∈ N.divisors, if d ∣ c then μ d else 0) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            rw [Commons.NumberTheory.Totient.divisors_gcd_eq_filter c N hN]
            rw [Finset.sum_filter]
    _ = ∑ d ∈ N.divisors, (∑ c ∈ Finset.Icc 1 C, if d ∣ c then μ d else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ d ∈ N.divisors, μ d * ((C / d : ℕ) : ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            calc
              (∑ c ∈ Finset.Icc 1 C, if d ∣ c then μ d else 0)
                  = ∑ c ∈ Finset.Icc 1 C, μ d * (if d ∣ c then (1 : ℤ) else 0) := by
                      refine Finset.sum_congr rfl ?_
                      intro c hc
                      by_cases h : d ∣ c <;> simp [h]
              _ = μ d * (∑ c ∈ Finset.Icc 1 C, if d ∣ c then (1 : ℤ) else 0) := by
                      rw [Finset.mul_sum]
              _ = μ d * (((Finset.Icc 1 C).filter (fun c : ℕ => d ∣ c)).card : ℤ) := by
                      rw [Finset.natCast_card_filter]
              _ = μ d * ((C / d : ℕ) : ℤ) := by
                      congr 1
                      rw [Commons.NumberTheory.Totient.card_multiples_Icc_one d C]

/-- `Σ_{d | N} μ(d)` is the indicator of `N = 1` (as an integer). -/
private lemma moebius_sum_divisors (N : ℕ) :
    (∑ d ∈ N.divisors, μ d) = if N = 1 then (1 : ℤ) else 0 := by
  exact Commons.NumberTheory.Totient.sum_moebius_divisors N

/-- The number of integers `e ∈ [-W, W]` coprime to `N` equals
`Σ_{d | N} μ(d)·(2·(W/d) + 1)`. -/
theorem coprime_symmetric_window_card (N W : ℕ) (hN : 0 < N) :
    (((Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun e : ℤ => (e.natAbs).gcd N = 1)).card : ℤ) =
      ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) * (((2 * (W / d) + 1 : ℕ) : ℤ)) := by
  classical
  have hN1 : 1 ≤ N := hN
  let F : ℕ → ℤ := fun m => if m.gcd N = 1 then (1 : ℤ) else 0
  have hz : F 0 = (if N = 1 then (1 : ℤ) else 0) := by
    dsimp [F]
    simp
  have hleft :
      (((Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun e : ℤ => (e.natAbs).gcd N = 1)).card : ℤ) =
        (if N = 1 then (1 : ℤ) else 0) +
          2 * (∑ d ∈ N.divisors, μ d * ((W / d : ℕ) : ℤ)) := by
    calc
      (((Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun e : ℤ => (e.natAbs).gcd N = 1)).card : ℤ)
          = ∑ e ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), (if e.natAbs.gcd N = 1 then (1 : ℤ) else 0) := by
              rw [Finset.natCast_card_filter]
      _ = F 0 + 2 * (∑ m ∈ Finset.Icc 1 W, F m) := by
              rw [sum_symm_window W F]
      _ = (if N = 1 then (1 : ℤ) else 0) +
            2 * (∑ m ∈ Finset.Icc 1 W, F m) := by
              rw [hz]
      _ = (if N = 1 then (1 : ℤ) else 0) +
            2 * (((Finset.Icc 1 W).filter (fun m : ℕ => m.gcd N = 1)).card : ℤ) := by
              rw [← Finset.natCast_card_filter]
      _ = (if N = 1 then (1 : ℤ) else 0) +
            2 * (∑ d ∈ N.divisors, μ d * ((W / d : ℕ) : ℤ)) := by
              rw [coprime_count_Icc_one W N hN1]
  have hright :
      (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) * (((2 * (W / d) + 1 : ℕ) : ℤ))) =
        (if N = 1 then (1 : ℤ) else 0) +
          2 * (∑ d ∈ N.divisors, μ d * ((W / d : ℕ) : ℤ)) := by
    calc
      (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) * (((2 * (W / d) + 1 : ℕ) : ℤ)))
          = ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) * (2 * ((W / d : ℕ) : ℤ) + 1) := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              norm_num
      _ = ∑ d ∈ N.divisors, (2 * ((ArithmeticFunction.moebius d : ℤ) * ((W / d : ℕ) : ℤ)) + (ArithmeticFunction.moebius d : ℤ)) := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              ring
      _ = 2 * (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) * ((W / d : ℕ) : ℤ)) +
            ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 2 * (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℤ) * ((W / d : ℕ) : ℤ)) +
            (if N = 1 then (1 : ℤ) else 0) := by
              rw [moebius_sum_divisors N]
      _ = (if N = 1 then (1 : ℤ) else 0) +
          2 * (∑ d ∈ N.divisors, μ d * ((W / d : ℕ) : ℤ)) := by
              ring
  rw [hleft, hright]

end Commons.NumberTheory.DuffinSchaeffer
