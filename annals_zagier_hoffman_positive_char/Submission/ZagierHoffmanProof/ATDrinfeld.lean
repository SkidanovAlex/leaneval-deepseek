import Submission.ZagierHoffmanProof.ATPsi

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The Carlitz module action is given by additive polynomials

Let `A = F[X]`, `q = Nat.card F` and `C_a` the Carlitz module action on power series
(`CarlitzModule.lean`).  This file proves the structure theorem

`carlitzAct a f = ∑_{k ≤ deg a} Ψ_k(a) · f ^ (q ^ k)`,

i.e. the endomorphism `C_a` of the additive group is given by an additive (`F_q`-linear)
polynomial, whose coefficients are the Anderson–Thakur polynomials `Ψ_k` (`ATPsi.lean`).
Equivalently, the Carlitz module is a Drinfeld module `A → End(G_a)` of rank one.

The proof is the iteration formula for the coefficients: `C_a(x) = ∑_k c_k x^(q^k)` holds for
`x` replaced by any power series, because the substitution `x ↦ x^(q)` acts on the expansion by
shifting indices, and the coefficient recursion is exactly the one defining `C_{θ^{i+1}}` from
`C_{θ^i}`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Coeffs

open PowerSeries

/-- The Carlitz `q`-binomial coefficients: the coefficient of `x ^ (q ^ k)` in `C_{θ ^ i}(x)`. -/
noncomputable def atQBinom (i k : ℕ) : RatFunc F :=
  PowerSeries.coeff (Nat.card F ^ k) (carlitzAction F i PowerSeries.X)

lemma atQBinom_eq_zero_of_gt {i k : ℕ} (h : i < k) : atQBinom F i k = 0 :=
  (carlitzAction_X_coeff F i).2 (Nat.card F ^ k)
    (Nat.pow_lt_pow_right (by have := carlitz_card_ge_two F; omega) h)

lemma atQBinom_zero_zero : atQBinom F 0 0 = 1 := by
  rw [atQBinom, carlitzAction_zero, pow_zero, PowerSeries.coeff_X, if_pos rfl]

/-- The recursion of the Carlitz `q`-binomial coefficients (the `q`-Pascal rule). -/
lemma atQBinom_succ (i k : ℕ) :
    atQBinom F (i + 1) k = carlitzTheta F * atQBinom F i k
      + (if k = 0 then 0 else (atQBinom F i (k - 1)) ^ (Nat.card F)) := by
  have h2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  unfold atQBinom
  rw [carlitzAction_succ, map_add, PowerSeries.coeff_C_mul, coeff_pow_card]
  by_cases hk : k = 0
  · subst hk
    rw [if_neg (by
      intro hdvd
      have h1 : Nat.card F = 1 := Nat.dvd_one.mp (by simpa using hdvd)
      omega), if_pos rfl]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hdiv : Nat.card F ^ k / Nat.card F = Nat.card F ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk1).symm]
      rw [pow_succ, Nat.mul_div_cancel _ (by omega : 0 < Nat.card F)]
    rw [if_pos (dvd_pow_self _ hk), if_neg hk, hdiv]

end Coeffs

section Shift

open PowerSeries

/-- The Frobenius `x ↦ x ^ q` on power series is additive, hence commutes with finite sums. -/
lemma sum_pow_card {ι : Type*} (s : Finset ι) (g : ι → PowerSeries (RatFunc F)) :
    (∑ i ∈ s, g i) ^ (Nat.card F) = ∑ i ∈ s, (g i) ^ (Nat.card F) := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty,
        zero_pow (by have := carlitz_card_ge_two F; omega)]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ps_add_pow_card F, ih]

/-- Shifting the summation index by one. -/
lemma sum_range_shift {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), g (k + 1))
      = (∑ k ∈ Finset.range (N + 1), (if k = 0 then 0 else g k)) + g (N + 1) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_one, Finset.sum_range_one]
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ (fun k => g (k + 1)) (N + 1), ih,
        Finset.sum_range_succ (fun k => if k = 0 then 0 else g k) (N + 1),
        if_neg (Nat.succ_ne_zero N)]

end Shift

lemma carlitzAction_eq_sum' (i N : ℕ) (hN : i ≤ N) (f : PowerSeries (RatFunc F)) :
    carlitzAction F i f = ∑ k ∈ Finset.range (N + 1),
      PowerSeries.C (atQBinom F i k) * f ^ (Nat.card F ^ k) := by
  induction i with
  | zero =>
      rw [carlitzAction_zero, Finset.sum_eq_single 0]
      · rw [atQBinom_zero_zero, pow_zero, pow_one, map_one, one_mul]
      · intro k _ hk
        rw [atQBinom_eq_zero_of_gt F (Nat.pos_of_ne_zero hk), map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le N))) h
  | succ i ih =>
      have hi : i ≤ N := by omega
      rw [carlitzAction_succ, ih hi, Finset.mul_sum, sum_pow_card]
      have h1 : (∑ k ∈ Finset.range (N + 1), PowerSeries.C (carlitzTheta F) *
            (PowerSeries.C (atQBinom F i k) * f ^ (Nat.card F ^ k)))
          = ∑ k ∈ Finset.range (N + 1),
              PowerSeries.C (carlitzTheta F * atQBinom F i k) * f ^ (Nat.card F ^ k) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← mul_assoc, ← map_mul]
      have h2 : (∑ k ∈ Finset.range (N + 1),
            (PowerSeries.C (atQBinom F i k) * f ^ (Nat.card F ^ k)) ^ (Nat.card F))
          = ∑ k ∈ Finset.range (N + 1),
              PowerSeries.C ((atQBinom F i k) ^ (Nat.card F)) * f ^ (Nat.card F ^ (k + 1)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [mul_pow, ← map_pow, ← pow_mul,
          show Nat.card F ^ k * Nat.card F = Nat.card F ^ (k + 1) from (pow_succ _ _).symm]
      rw [h1, h2]
      have hg : (∑ k ∈ Finset.range (N + 1), PowerSeries.C ((atQBinom F i k) ^ (Nat.card F))
            * f ^ (Nat.card F ^ (k + 1)))
          = ∑ k ∈ Finset.range (N + 1), PowerSeries.C ((atQBinom F i ((k + 1) - 1)) ^ (Nat.card F))
            * f ^ (Nat.card F ^ (k + 1)) := by
        refine Finset.sum_congr rfl (fun k _ => by rw [Nat.add_sub_cancel])
      rw [hg, sum_range_shift (fun j => PowerSeries.C ((atQBinom F i (j - 1)) ^ (Nat.card F))
        * f ^ (Nat.card F ^ j)) N, Nat.add_sub_cancel]
      have hz : PowerSeries.C (0 : RatFunc F) = 0 := map_zero PowerSeries.C
      rw [atQBinom_eq_zero_of_gt F (by omega : i < N),
        zero_pow (by have := carlitz_card_ge_two F; omega), hz, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [atQBinom_succ]
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hif : (if k = 0 then (0 : RatFunc F) else (atQBinom F i (k - 1)) ^ (Nat.card F))
            = (atQBinom F i (k - 1)) ^ (Nat.card F) := if_neg hk0
        have hif2 : (if k = 0 then (0 : PowerSeries (RatFunc F))
            else PowerSeries.C ((atQBinom F i (k - 1)) ^ (Nat.card F)) * f ^ (Nat.card F ^ k))
            = PowerSeries.C ((atQBinom F i (k - 1)) ^ (Nat.card F)) * f ^ (Nat.card F ^ k) :=
          if_neg hk0
        rw [hif, hif2, map_add, add_mul]

lemma atPsi_eq_sum_binom (k : ℕ) (a : F[X]) :
    atPsi F k a = ∑ i ∈ Finset.range (a.natDegree + 1),
      algebraMap F (RatFunc F) (a.coeff i) * atQBinom F i k := by
  rw [atPsi, carlitzAct, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [PowerSeries.coeff_C_mul]
  rfl

theorem carlitzAct_eq_sum (a : F[X]) (f : PowerSeries (RatFunc F)) :
    carlitzAct F a f = ∑ k ∈ Finset.range (a.natDegree + 1),
      PowerSeries.C (atPsi F k a) * f ^ (Nat.card F ^ k) := by
  rw [carlitzAct]
  have h2 : (∑ i ∈ Finset.range (a.natDegree + 1), PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i))
        * carlitzAction F i f)
      = ∑ i ∈ Finset.range (a.natDegree + 1), PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i))
        * ∑ k ∈ Finset.range (a.natDegree + 1),
            PowerSeries.C (atQBinom F i k) * f ^ (Nat.card F ^ k) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [carlitzAction_eq_sum' F i a.natDegree (by omega) f]
  rw [h2]
  rw [Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by
    rw [← mul_assoc, ← map_mul]))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun k _ => (Finset.sum_mul _ _ _).symm)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← map_sum PowerSeries.C, ← atPsi_eq_sum_binom F k a]


section Recursion

open PowerSeries

lemma carlitzAct_X_apply (f : PowerSeries (RatFunc F)) :
    carlitzAct F Polynomial.X f = PowerSeries.C (carlitzTheta F) * f + f ^ (Nat.card F) := by
  rw [carlitzAct_eq_sum, Polynomial.natDegree_X, Finset.sum_range_succ, Finset.sum_range_one,
    show (Polynomial.X : F[X]) = Polynomial.X ^ 1 from (pow_one _).symm,
    atPsi_X_pow, atPsi_zero_eq, map_pow,
    show (algebraMap F[X] (RatFunc F)) Polynomial.X = carlitzTheta F from rfl]
  simp

theorem atPsi_X_mul (k : ℕ) (a : F[X]) :
    atPsi F k (Polynomial.X * a) = carlitzTheta F * atPsi F k a
      + (if k = 0 then 0 else (atPsi F (k - 1) a) ^ (Nat.card F)) := by
  unfold atPsi
  rw [carlitzAct_mul F Polynomial.X a PowerSeries.X, carlitzAct_X_apply, map_add,
    PowerSeries.coeff_C_mul, coeff_pow_card_pow]


end Recursion

end ZagierHoffmanPositiveChar
