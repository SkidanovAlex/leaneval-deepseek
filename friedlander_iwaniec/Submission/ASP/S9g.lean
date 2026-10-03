/-
  Companion paper, §9: the passage to the squarefree-supported sequence `ã` (9.4) with the
  modified density `g̃` (9.5).

  `S9a.AtilAd_eq_gtil_mul_add` proves the *exact* identity

      `Ã_d(m) = g̃(d)·Ã(m) + r̃_d(m) + A(m)·(density tail)`,

  where the density tail

      `gtail(d,m) = ∑_{ν ≤ m} μ(ν)·(g([ν²,d]) − g̃(d)·g(ν²))`

  is the difference between the companion's exact identities (9.8)/(9.9) and their truncations
  at `ν ≤ m` (the companion shows it is `O((log m)^{−B})` from (1.8), (9.1), (1.9)).  Hence the
  honest remainder function for (1.7) is

      `rtildeFull(d,m) = rtilde(d,m) + A(m)·gtail(d,m)`,

  and (1.7) for the pair `(atil a, g̃)` holds **exactly** (`approx_atil` below).  The bound (9.7)
  is then `S9f.Rtilde_sum_le_of_inputs` plus the tail bound.
-/
import Mathlib
import Submission.ASP.S9a
import Submission.ASP.S9c
import Submission.ASP.S9f

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The density tail of §9: the difference between the companion's exact identities (9.8)/(9.9)
and their truncations at `ν ≤ m`. -/
def gtail (g gtil : ℕ → ℝ) (d m : ℕ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ)
    * (g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2))

/-- The honest remainder of (9.6): `r̃_d(m) + A(m)·gtail(d,m)`. -/
def rtildeFull (r : ℕ → ℕ → ℝ) (g gtil : ℕ → ℝ) (a : ℕ → ℝ) (d m : ℕ) : ℝ :=
  rtilde r gtil d m + Acount a m * gtail g gtil d m

/-- `Acount (atil a) = Ã_1`. -/
lemma Acount_atil_eq (a : ℕ → ℝ) (m : ℕ) : Acount (atil a) (m : ℝ) = AtilAd a 1 m := by
  rw [Acount, AtilAd, Ad, Nat.floor_natCast]
  congr 1
  ext n
  rw [Finset.mem_filter]
  constructor
  · intro h; exact ⟨h, one_dvd n⟩
  · intro h; exact h.1

/-- **Companion §9, (9.6)**: with the density tail included, `(1.7)` holds *exactly* for the
squarefree-supported sequence `ã` and the density `g̃`. -/
theorem approx_atil (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ) (x : ℝ)
    (happ : Approx a g r x) :
    Approx (atil a) gtil (rtildeFull r g gtil a) x := by
  intro d m
  have h := AtilAd_eq_gtil_mul_add a g r d m gtil happ
  simp only [rtildeFull, rtilde, gtail, Acount_atil_eq a m, AtilAd] at *
  rw [h]
  ring

/-- The pointwise bound of the full remainder by the two pieces. -/
lemma abs_rtildeFull_le (r : ℕ → ℕ → ℝ) (g gtil : ℕ → ℝ) (a : ℕ → ℝ) (d m : ℕ) :
    |rtildeFull r g gtil a d m|
      ≤ |rtilde r gtil d m| + |Acount a m| * |gtail g gtil d m| := by
  rw [rtildeFull]
  refine le_trans (abs_add_le _ _) (le_of_eq ?_)
  rw [abs_mul]

/-- **Companion §9, (9.7)** for the honest remainder: the bound for `r̃` plus the density tail. -/
theorem RtildeFull_sum_le (r : ℕ → ℕ → ℝ) (g gtil : ℕ → ℝ) (a : ℕ → ℝ) (t D : ℕ) {R T : ℝ}
    (hR : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtilde r gtil d t|) ≤ R)
    (hT : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtail g gtil d t|) ≤ T) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtildeFull r g gtil a d t|)
      ≤ R + |Acount a t| * T := by
  refine le_trans (Finset.sum_le_sum (fun d _ => abs_rtildeFull_le r g gtil a d t)) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add hR ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hT (abs_nonneg _)


/-! ### The hypotheses (1.4) and (1.6) for the squarefree-supported sequence `ã` -/

/-- `ã_n ≤ a_n` (for `a ≥ 0`), so the congruence sums of `ã` are dominated by those of `a`. -/
lemma Ad_atil_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ℕ) (x : ℝ) :
    Ad (atil a) d x ≤ Ad a d x := by
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [atil]
  have h1 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
    rw [moebius_sq_cast n]; split_ifs <;> norm_num
  calc ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * a n ≤ 1 * a n :=
        mul_le_mul_of_nonneg_right h1 (ha n)
    _ = a n := one_mul _

/-- `ã_n ≤ a_n` pointwise for `a ≥ 0`. -/
lemma atil_le_self (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) : atil a n ≤ a n := by
  rw [atil]
  have h1 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
    rw [moebius_sq_cast n]; split_ifs <;> norm_num
  calc ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * a n ≤ 1 * a n :=
        mul_le_mul_of_nonneg_right h1 (ha n)
    _ = a n := one_mul _

/-- `Acount (atil a) ≤ Acount a`. -/
lemma Acount_atil_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (x : ℝ) :
    Acount (atil a) x ≤ Acount a x := by
  rw [Acount, Acount]
  exact Finset.sum_le_sum (fun n _ => atil_le_self a ha n)

/-- **Companion §9, hypothesis (1.6) for `ã`**: with (1.6) for `a` and the density bound
`Ã(x) ≥ c·A(x)` (from (9.12)), `Ã_d(x) ≪ d^{−1}τ(d)^8·Ã(x)`. -/
theorem atil_16 (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (h912 : ∀ x : ℕ, c * Acount a (x : ℝ) ≤ Acount (atil a) (x : ℝ))
    (h16 : ∀ d x : ℕ,
      Ad a d (x : ℝ) ≤ C * (((d.divisors.card : ℝ)) ^ 8 / (d : ℝ)) * Acount a (x : ℝ))
    (d x : ℕ) :
    Ad (atil a) d (x : ℝ)
      ≤ (C / c) * (((d.divisors.card : ℝ)) ^ 8 / (d : ℝ)) * Acount (atil a) (x : ℝ) := by
  refine le_trans (Ad_atil_le a ha d (x : ℝ)) ?_
  refine le_trans (h16 d x) ?_
  have hA : Acount a (x : ℝ) ≤ Acount (atil a) (x : ℝ) / c := by
    rw [le_div_iff₀ hc]
    linarith [h912 x]
  calc C * (((d.divisors.card : ℝ)) ^ 8 / (d : ℝ)) * Acount a (x : ℝ)
      ≤ C * (((d.divisors.card : ℝ)) ^ 8 / (d : ℝ)) * (Acount (atil a) (x : ℝ) / c) :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hC (by positivity))
    _ = (C / c) * (((d.divisors.card : ℝ)) ^ 8 / (d : ℝ)) * Acount (atil a) (x : ℝ) := by ring

/-- **Companion §9, hypothesis (1.4) for `ã`**: with (1.4) for `a` and the density bound
`Ã(x) ≥ c·A(x)`, the sequence `ã` satisfies `Ã(x) ≫ Ã(√x)(log x)^2`. -/
theorem atil_14 (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (h912 : ∀ x : ℕ, c * Acount a (x : ℝ) ≤ Acount (atil a) (x : ℝ))
    (h4 : ∀ x : ℕ, K * Acount a ((Nat.sqrt x : ℕ) : ℝ) * (Real.log (x : ℝ)) ^ 2
      ≤ Acount a (x : ℝ))
    (x : ℕ) :
    c * K * Acount (atil a) ((Nat.sqrt x : ℕ) : ℝ) * (Real.log (x : ℝ)) ^ 2
      ≤ Acount (atil a) (x : ℝ) := by
  have hsqrt : Acount (atil a) ((Nat.sqrt x : ℕ) : ℝ) ≤ Acount a ((Nat.sqrt x : ℕ) : ℝ) :=
    Acount_atil_le a ha _
  have hlog : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ 2 := sq_nonneg _
  have h1 : c * Acount a (x : ℝ) ≤ Acount (atil a) (x : ℝ) := h912 x
  have h4x := h4 x
  have hnn : (0 : ℝ) ≤ Acount a ((Nat.sqrt x : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun n _ => ha n)
  nlinarith [h1, h4x, hsqrt, hlog, hnn, mul_nonneg (le_of_lt hc) (le_of_lt hK),
    mul_nonneg (mul_nonneg (le_of_lt hc) (le_of_lt hK)) hlog]

end

end Submission.ASP
