/-
  Companion paper ("Asymptotic sieve for primes", Friedlander–Iwaniec, Ann. of Math. 148
  (1998) 1041–1065), §9 ("A generalization"): the passage from a sequence `A = (a_n)` to

      `ã_n = μ(n)²·a_n`      (9.4)

  which makes the sequence squarefree-supported, together with the modified density

      `g̃(p) = (g(p) − g(p²))/(1 − g(p²))`      (9.5)

  and the Euler product `G = ∏_p (1 − g(p²))` (9.8).  The two identities underlying §9 are, for
  `d` squarefree,

      `Ã_d(x) = ∑_ν μ(ν)·A_{[ν²,d]}(x)`      (9.6)/(9.8)

  (here `A_k(x) = ∑_{n ≤ x, k ∣ n} a_n` is the congruence sum (1.5)) and

      `Ã(x) = Ã_1(x) = G·A(x) + ∑_ν μ(ν)·r_{ν²}(x)`,      (9.10)

  from which the companion derives

      `r̃_d(x) = ∑_ν μ(ν)·(r_{[ν²,d]}(x) − g̃(d)·r_{ν²}(x))`.      (9.11)

  All the sums over `ν` are taken over `ν² ≤ x` (i.e. `ν ∈ [1,x]`), which is where they are
  truncated in the paper as well.  The point of this file: the identities above are *exact* and
  elementary once the Möbius square-divisor identity `μ(n)² = ∑_{d² ∣ n} μ(d)` (available in the
  commons as `Commons.NumberTheory.Moebius.sum_sq_dvd_moebius_eq`) is used; the companion's
  (9.8)/(9.9) are the `x → ∞` limits of the identities proved here, and the *density tail*

      `∑_{ν ≤ √x} μ(ν)·(g([ν²,d]) − g̃(d)·g(ν²))`

  is exactly the quantity controlled by (1.8)+(9.1) in the paper.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Commons.NumberTheory.Moebius.sum_sq_dvd_moebius_eq

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The squarefree-supported sequence `ã` -/

/-- `ã_n = μ(n)²·a_n` — the companion's (9.4). -/
def atil (a : ℕ → ℝ) (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * a n

lemma atil_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ atil a n := by
  rw [atil]
  exact mul_nonneg (by positivity) (ha n)

lemma sum_sq_dvd_moebius_eq_cast (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ)) ^ 2
      = ∑ e ∈ n.divisors,
          (if e ^ 2 ∣ n then (ArithmeticFunction.moebius e : ℝ) else 0) := by
  rw [← Int.cast_pow, ← Commons.NumberTheory.Moebius.sum_sq_dvd_moebius_eq n]
  push_cast
  ring

lemma moebius_sq_cast (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ)) ^ 2 = if Squarefree n then 1 else 0 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  by_cases hs : Squarefree n <;> simp [hs]

lemma atil_zero_of_not_squarefree {a : ℕ → ℝ} {n : ℕ} (h : ¬ Squarefree n) : atil a n = 0 := by
  rw [atil, moebius_sq_cast n, if_neg h]
  ring

lemma atil_le_abs {a : ℕ → ℝ} (n : ℕ) : atil a n ≤ |a n| := by
  by_cases h0 : 0 ≤ a n
  · have h : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
      rw [moebius_sq_cast n]; split_ifs <;> norm_num
    calc atil a n = ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * a n := rfl
      _ ≤ 1 * a n := mul_le_mul_of_nonneg_right h h0
      _ = a n := one_mul _
      _ ≤ |a n| := le_abs_self _
  · have ha' : a n < 0 := not_le.mp h0
    have h1 : atil a n ≤ 0 := by
      rw [atil]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ha'.le
    have h2 : (0 : ℝ) ≤ |a n| := abs_nonneg _
    linarith

/-- `Ã_d(x) = ∑_{n ≤ x, d ∣ n} ã_n` — the congruence sum (9.6) for the squarefree-supported
sequence `ã`. -/
def AtilAd (a : ℕ → ℝ) (d m : ℕ) : ℝ := Ad (atil a) d m

/-! ### (9.6): the reindexing `Ã_d(x) = ∑_ν μ(ν)·A_{[ν²,d]}(x)` -/

/-- For `n ∈ [1,m]`, the divisors `e` of `n` with `e² ∣ n` are exactly the `e ∈ [1,m]` with
`e² ∣ n`. -/
private lemma divisors_filter_sq_eq (m n : ℕ) (hn : n ∈ Finset.Icc 1 m) :
    n.divisors.filter (fun e => e ^ 2 ∣ n)
      = (Finset.Icc 1 m).filter (fun e => e ^ 2 ∣ n) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
  ext e
  rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hedvd, -⟩, hsq⟩
    have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hedvd (by omega)
    have he2 : e ^ 2 ≤ n := Nat.le_of_dvd (by omega) hsq
    have hee : e ≤ n := by nlinarith [he1]
    exact ⟨Finset.mem_Icc.mpr ⟨he1, le_trans hee hnm⟩, hsq⟩
  · rintro ⟨he, hsq⟩
    have hep : 0 < e := (Finset.mem_Icc.mp he).1
    have hedvd : e ∣ n := dvd_trans (by exact ⟨e, by ring⟩) hsq
    exact ⟨⟨hedvd, by omega⟩, hsq⟩

/-- **Companion §9, (9.6)**: for the squarefree-supported sequence `ã`,
`Ã_d(x) = ∑_{ν ≤ x} μ(ν)·A_{[ν²,d]}(x)` (all sums finite; `A_k(x) = Ad a k x`). -/
theorem AtilAd_eq_sum_lcm (a : ℕ → ℝ) (d m : ℕ) :
    AtilAd a d m
      = ∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ)
          * Ad a (Nat.lcm (ν ^ 2) d) m := by
  classical
  -- Step 1: expand `μ(n)²` by the square-divisor identity (all sums over `[1,m]`).
  have h1 : AtilAd a d m
      = ∑ n ∈ Finset.Icc 1 m, ∑ e ∈ Finset.Icc 1 m,
          (if d ∣ n ∧ e ^ 2 ∣ n then a n * (ArithmeticFunction.moebius e : ℝ) else 0) := by
    unfold AtilAd Ad atil
    rw [Nat.floor_natCast, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    by_cases hdn : d ∣ n
    · rw [if_pos hdn]
      rw [show ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * a n
          = a n * ((ArithmeticFunction.moebius n : ℝ)) ^ 2 from by ring]
      rw [sum_sq_dvd_moebius_eq_cast n, ← Finset.sum_filter, divisors_filter_sq_eq m n hn,
        Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases hen : e ^ 2 ∣ n
      · rw [if_pos hen, if_pos ⟨hdn, hen⟩]
      · rw [if_neg hen, if_neg (fun h => hen h.2)]
    · rw [if_neg hdn]
      refine (Finset.sum_eq_zero (fun e _ => ?_)).symm
      rw [if_neg (fun h => hdn h.1)]
  rw [h1]
  -- Step 2: swap the `(n,e)`-sums.
  have h2 : (∑ n ∈ Finset.Icc 1 m, ∑ e ∈ Finset.Icc 1 m,
        (if d ∣ n ∧ e ^ 2 ∣ n then a n * (ArithmeticFunction.moebius e : ℝ) else 0))
      = ∑ e ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius e : ℝ)
          * ∑ n ∈ Finset.Icc 1 m,
              (if d ∣ n ∧ e ^ 2 ∣ n then a n else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : d ∣ n ∧ e ^ 2 ∣ n
    · rw [if_pos h, if_pos h, mul_comm]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [h2]
  -- Step 3: identify the inner sums with `A_{[ν²,d]}(x)`.
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Ad, Nat.floor_natCast, Finset.sum_filter]
  refine congrArg (fun x => (ArithmeticFunction.moebius e : ℝ) * x) ?_
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : d ∣ n ∧ e ^ 2 ∣ n
  · rw [if_pos h, if_pos (Nat.lcm_dvd h.2 h.1)]
  · rw [if_neg h, if_neg (fun hl => h ⟨dvd_trans (Nat.dvd_lcm_right _ _) hl,
      dvd_trans (Nat.dvd_lcm_left _ _) hl⟩)]

/-! ### (9.6)/(9.10)/(9.11): the `(1.7)`-expansion of `Ã` -/

/-- **Companion §9, (9.6)+(9.10)+(9.11)** (exact form): for any `g̃ : ℕ → ℝ` and every scale `m`,
`Ã_d(m) = g̃(d)·Ã(m) + r̃_d(m) + A(m)·(density tail)`, where

  `r̃_d(m) = ∑_{ν ≤ m} μ(ν)·(r_{[ν²,d]}(m) − g̃(d)·r_{ν²}(m))`

is the companion's (9.11) and the density tail `∑_{ν ≤ m} μ(ν)·(g([ν²,d]) − g̃(d)·g(ν²))` is
the difference between the companion's exact identities (9.8)/(9.9) and their truncations at
`ν ≤ m`; it is `O((log m)^{-B})` in the applications (this is where (1.8), (1.9), (9.1) enter),
so the expansion becomes `Ã_d(m) = g̃(d)·Ã(m) + r̃_d(m)` up to an admissible error. -/
theorem AtilAd_eq_gtil_mul_add (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (d m : ℕ) (gtil : ℕ → ℝ)
    (happ : Approx a g r (m : ℝ)) :
    AtilAd a d m
      = gtil d * AtilAd a 1 m
        + (∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ)
            * (r (Nat.lcm (ν ^ 2) d) m - gtil d * r (ν ^ 2) m))
        + Acount a m * (∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ)
            * (g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2))) := by
  classical
  rw [AtilAd_eq_sum_lcm a d m, AtilAd_eq_sum_lcm a 1 m]
  -- `Ad a k m = g k * Acount a m + r k m` for every `k`, and `lcm (ν²) 1 = ν²`
  have hterm : ∀ ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * Ad a (Nat.lcm (ν ^ 2) d) m
      = gtil d * ((ArithmeticFunction.moebius ν : ℝ) * Ad a (Nat.lcm (ν ^ 2) 1) m)
        + (ArithmeticFunction.moebius ν : ℝ)
            * (r (Nat.lcm (ν ^ 2) d) m - gtil d * r (ν ^ 2) m)
        + Acount a m * ((ArithmeticFunction.moebius ν : ℝ)
            * (g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2))) := by
    intro ν
    rw [Nat.lcm_one_right, happ (ν ^ 2) m, happ (Nat.lcm (ν ^ 2) d) m]
    ring
  rw [Finset.sum_congr rfl (fun ν _ => hterm ν), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

end

end Submission.ASP
