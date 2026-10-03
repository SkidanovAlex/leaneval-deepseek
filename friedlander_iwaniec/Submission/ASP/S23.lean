/-
  **The aggregate `(2.1)`-type bound for X² + Y⁴.**

  The companion paper's hypothesis `(1.6)` (pointwise `A_d(x) ≤ C d⁻¹ τ(d)^8 A(x)`) is FALSE for
  the sequence `a_n = #{(a,c) : a² + c⁴ = n}` (at `d = p⁴` the true density is `g(p⁴) ≍ p⁻³`,
  which exceeds `d⁻¹τ(d)^8` for `p > 5^8`).  What the main paper actually uses for the sequence is
  the *aggregate*

    `(2.1)   ∑_{d ≤ x} τ(d)^{20/3} A_d(x) ≪ A(x)(log x)^{2^48}`,

  which is obtained from the *cube* range `d ≤ x^{1/3}` of the congruence sums via
  `τ(n)^8 ≤ ∑_{d ∣ n, d³ ≤ n}(2τ(d))^{40}`.

  This file provides the elementary half of that: every `τ^{20/3}`-weighted sum over the modulus
  range `D ≤ t^{3/4}` where the main paper's Lemma 3.1 `(3.3)` applies.  The second input is the
  weighted root count `(K2)`: `∑_{d ≤ D} τ(d)^{20/3} ρ(c²;d)/d ≤ C₂(log(D+2))^{B₂}` uniformly in `c`,
  which is the honest replacement of `(1.6)` for the main term `M_d`.
-/
import Mathlib
import Submission.ASP.S22
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.Sieve.sum_squarefree_tau_pow_mul_gdens_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_sum_int_sqrt
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_hdens_cubefree_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_mul_of_coprime
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset

noncomputable section

/-! ## `(2.2)` for the local density `g` -/

/-- A squarefree number is not divisible by `4`. -/
lemma sqfree_not_four_dvd {d : ℕ} (hd : Squarefree d) : ¬ 4 ∣ d := by
  intro h
  have h2 : 2 * 2 ∣ d := by simpa using h
  exact (Nat.squarefree_iff_prime_squarefree.mp hd 2 Nat.prime_two) h2

theorem sum_sqfree_tau_pow_gdens_le :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 2 ≤ x →
      (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * (Submission.gdens d : ℝ))
        ≤ C * (Real.log ((x : ℝ) + 2)) ^ K := by
  obtain ⟨C₀, hC₀, K₀, hK₀0, h⟩ := Commons.NumberTheory.Sieve.sum_squarefree_tau_pow_mul_gdens_le
    (g := fun d => (Submission.gdens d : ℝ))
    (fun p hp => by
      rw [Submission.gdens]
      push_cast
      exact div_nonneg (by positivity) (sq_nonneg _))
    (fun m n hcop => by
      rw [Submission.gdens_mul_of_coprime hcop]
      push_cast
      ring)
    (by
      refine ⟨2, by norm_num, fun p hp => ?_⟩
      have hp0 : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      have h1 : (Submission.gdens p : ℝ) * (p : ℝ) ≤ 2 := by
        have := Submission.gdens_prime_mul_le hp
        exact_mod_cast this
      rw [le_div_iff₀ hp0]
      exact h1)
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₀ * max 1 ((Real.log 2) ^ K₀), by positivity, max K₀ 0, le_max_right _ _,
    fun x hx => ?_⟩
  have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hlogx1 : (0:ℝ) < Real.log (x:ℝ) :=
    lt_of_lt_of_le hlog2pos (Real.log_le_log (by norm_num) hx2)
  have hlogxle : Real.log (x:ℝ) ≤ Real.log ((x:ℝ)+2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hcomp : (Real.log (x:ℝ)) ^ K₀
      ≤ max 1 ((Real.log 2) ^ K₀) * (Real.log ((x:ℝ)+2)) ^ (max K₀ 0) := by
    have hlog20 : (0:ℝ) < Real.log 2 := hlog2pos
    rcases lt_or_ge K₀ 0 with h0 | h0
    · have h1 : (Real.log (x:ℝ)) ^ K₀ ≤ (Real.log 2) ^ K₀ :=
        Real.rpow_le_rpow_of_nonpos hlog20 (Real.log_le_log (by norm_num) hx2) h0.le
      rw [max_eq_right h0.le, Real.rpow_zero, mul_one]
      exact le_trans h1 (le_max_right _ _)
    · have h1 : (Real.log (x:ℝ)) ^ K₀ ≤ (Real.log ((x:ℝ)+2)) ^ K₀ :=
        Real.rpow_le_rpow (le_of_lt hlogx1) hlogxle h0
      rw [max_eq_left h0]
      have h3 : (0:ℝ) ≤ (Real.log ((x:ℝ)+2)) ^ K₀ :=
        Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hlogx1 hlogxle)) _
      calc (Real.log (x:ℝ)) ^ K₀ ≤ (Real.log ((x:ℝ)+2)) ^ K₀ := h1
        _ = 1 * (Real.log ((x:ℝ)+2)) ^ K₀ := by ring
        _ ≤ max 1 ((Real.log 2) ^ K₀) * (Real.log ((x:ℝ)+2)) ^ K₀ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) h3
  calc (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * (Submission.gdens d : ℝ))
      ≤ C₀ * (Real.log (x : ℝ)) ^ K₀ := h x hx
    _ ≤ C₀ * (max 1 ((Real.log 2) ^ K₀) * (Real.log ((x:ℝ)+2)) ^ (max K₀ 0)) :=
        mul_le_mul_of_nonneg_left hcomp hC₀.le
    _ = (C₀ * max 1 ((Real.log 2) ^ K₀)) * (Real.log ((x:ℝ)+2)) ^ (max K₀ 0) := by ring

/-! ## The main-term (`M_d`) part of the aggregate -/

/-- `MdNum` is nonnegative: it equals `2 ∑_c ρ(c²;d)(2√(t-c⁴)+1) + 2√t ρ(0;d)`. -/
lemma MdNum_nonneg (d t : ℕ) : 0 ≤ Submission.MdNum d t := by
  rw [Submission.MdNum_reindex]
  positivity

/-- Swapping the `c`-sum (roots) with the `d`-sum (moduli) in a weighted density sum. -/
lemma sum_swap_density (s R : Finset ℕ) (T : ℕ → ℝ) (Pr : ℕ → ℕ → ℝ) (M : ℕ → ℝ)
    (d0 : ℕ → ℝ) :
    (∑ d ∈ s, T d * ((∑ c ∈ R, Pr c d * M c) / d0 d))
      = ∑ c ∈ R, M c * (∑ d ∈ s, T d * (Pr c d / d0 d)) := by
  calc ∑ d ∈ s, T d * ((∑ c ∈ R, Pr c d * M c) / d0 d)
      = ∑ d ∈ s, ∑ c ∈ R, M c * (T d * (Pr c d / d0 d)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_div, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ c ∈ R, ∑ d ∈ s, M c * (T d * (Pr c d / d0 d)) := Finset.sum_comm
    _ = ∑ c ∈ R, M c * (∑ d ∈ s, T d * (Pr c d / d0 d)) := by
        exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]

/-- The pointwise expansion of `M_d(t)` into the weighted root sum. -/
lemma Md_eq_rho_sum (d t : ℕ) :
    ((Submission.Md d t : ℚ) : ℝ)
      = (2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
            (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
          + 2 * (Nat.sqrt t : ℝ) * (Submission.rho 0 d : ℝ)) / (d : ℝ) := by
  have h1 : ((Submission.Md d t : ℚ) : ℝ) = ((Submission.MdNum d t : ℕ) : ℝ) / (d : ℝ) := by
    rw [Submission.Md]
    push_cast
    ring
  rw [h1, Submission.MdNum_reindex]
  push_cast
  ring

/-- **The main-term aggregate.**  From `(K2)` (uniform in `c`),
`∑_{d ≤ D} τ(d)^{20/3} M_d(t) ≤ C A(t) (log(D+2))^{B₂}`. -/
theorem sum_Md_tau_pow_le {C2 B2 : ℝ} (hC2 : 0 ≤ C2)
    (hK2 : ∀ c D : ℕ, (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t D : ℕ, 1 ≤ t → 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ))
        ≤ C * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by
  refine ⟨4 * C2 + 1, by positivity, fun t D ht hD => ?_⟩
  have hlog0 : (0:ℝ) ≤ Real.log ((D:ℝ) + 2) := by
    apply Real.log_nonneg
    linarith [show (0:ℝ) ≤ (D:ℝ) by positivity]
  have hpw : (0:ℝ) ≤ (Real.log ((D:ℝ) + 2)) ^ B2 := Real.rpow_nonneg hlog0 _
  have hC2P : (0:ℝ) ≤ C2 * (Real.log ((D:ℝ) + 2)) ^ B2 := mul_nonneg hC2 hpw
  -- split each summand, then swap the root sum with the modulus sum
  have hsplit : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ))
      = 2 * (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
              * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                  (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                    / (d : ℝ)))
        + 2 * (Nat.sqrt t : ℝ) * (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho 0 d : ℝ) / (d : ℝ))) := by
    have hpt : ∀ d : ℕ,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ)
          = 2 * (((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
                * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                    (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                      / (d : ℝ)))
            + 2 * (Nat.sqrt t : ℝ) * (((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
                * ((Submission.rho 0 d : ℝ) / (d : ℝ))) := by
      intro d
      rw [Md_eq_rho_sum d t]
      ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_add_distrib,
      Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  -- bound the two pieces
  have hQ : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
          * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                / (d : ℝ)))
      = ∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
          ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
            * (∑ d ∈ Finset.Icc 1 D,
                ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))) :=
    sum_swap_density _ _ _ _ _ _
  have hQ0 : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho 0 d : ℝ) / (d : ℝ)))
      ≤ C2 * (Real.log ((D : ℝ) + 2)) ^ B2 := by
    simpa only [pow_two, mul_zero] using hK2 0 D
  have hQb : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
        ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))))
      ≤ (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
          * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h1 : ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :=
      mul_le_mul_of_nonneg_left (hK2 c D) (by positivity)
    calc ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) := h1
      _ = (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
          * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ) := by ring
  -- the `A`-comparison
  have hAc : ((Submission.Aseq t : ℕ) : ℝ)
      = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)) + (2 * (Nat.sqrt t : ℝ) + 1) := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_sum_int_sqrt t
    simp only [Submission.Aseq, Submission.an] at h ⊢
    rw [h]; push_cast; ring
  have hS0 : (0:ℝ) ≤ ∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
      ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ) := by positivity
  have hA0 : (0:ℝ) ≤ (Submission.Aseq t : ℝ) := by positivity
  have hSle : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
      ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)) ≤ (Submission.Aseq t : ℝ) := by
    linarith [hAc, hS0, show (0:ℝ) ≤ (Nat.sqrt t : ℝ) by positivity]
  have hst : 2 * (Nat.sqrt t : ℝ) ≤ (Submission.Aseq t : ℝ) := by
    linarith [hAc, hS0, show (0:ℝ) ≤ (Nat.sqrt t : ℝ) by positivity]
  calc 2 * (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
            * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                  / (d : ℝ)))
        + 2 * (Nat.sqrt t : ℝ) * (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho 0 d : ℝ) / (d : ℝ)))
      = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
            ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
              * (∑ d ∈ Finset.Icc 1 D,
                  ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))))
        + 2 * (Nat.sqrt t : ℝ) * (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho 0 d : ℝ) / (d : ℝ))) := by
        rw [hQ]
    _ ≤ 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
          * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)))
        + 2 * (Nat.sqrt t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :=
        add_le_add (mul_le_mul_of_nonneg_left hQb (by norm_num))
          (mul_le_mul_of_nonneg_left hQ0 (by positivity))
    _ ≤ (4 * C2 + 1) * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by
        have h1 : 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
              * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                  ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)))
            ≤ 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSle hC2P) (by norm_num)
        have h2 : 2 * (Nat.sqrt t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
            ≤ (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ) := by
          calc 2 * (Nat.sqrt t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
              = (2 * (Nat.sqrt t : ℝ)) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) := by ring
            _ ≤ (Submission.Aseq t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :=
                mul_le_mul_of_nonneg_right hst hC2P
            _ = (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ) := by ring
        have h3 : (0:ℝ) ≤ 3 * C2 + 1 := by linarith
        have h4 : 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ))
              + (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ)
            = (3 * C2) * (Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ) := by ring
        have h5 : (3 * C2) * (Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)
            ≤ (4 * C2 + 1) * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by
          have h6 : (3 * C2) ≤ (4 * C2 + 1) := by linarith
          calc (3 * C2) * (Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)
              = (3 * C2) * ((Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)) := by ring
            _ ≤ (4 * C2 + 1) * ((Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)) :=
                mul_le_mul_of_nonneg_right h6 (by positivity)
            _ = (4 * C2 + 1) * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by ring
        linarith [h1, h2, h4.le, h4.ge, h5]

/-! ## The error part: `(3.3)` with the `τ^{20/3}` weight -/

/-- The `τ^{20/3}`-weighted `(3.3)`: for `D ≤ t^{3/4}` the weighted sum of `|A_d(t) - M_d(t)|` is
bounded by the unweighted `(3.3)` bound, up to `D^{1/100}`. -/
theorem sum_Ad_sub_Md_tau_pow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t D : ℕ, 1 ≤ t → 1 ≤ D → D ≤ ⌊(t:ℝ)^((3:ℝ)/4)⌋₊ →
      (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
        * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
        ≤ C * (D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100) := by
  obtain ⟨Cτ, hCτ, hτ⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/1000) (by norm_num)
  obtain ⟨CAd, hCAd, hAd⟩ := Submission.X2Y4R.Ad_sub_Md_sum_le
  refine ⟨Cτ ^ ((20:ℝ)/3) * CAd + 1, by positivity, fun t D ht hD hDle => ?_⟩
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hτb : ∀ d ∈ Finset.Icc 1 D,
      ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) ≤ Cτ ^ ((20:ℝ)/3) * (D:ℝ)^((1:ℝ)/100) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdD : (d:ℝ) ≤ (D:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have h1 : (d.divisors.card : ℝ) ≤ Cτ * (d:ℝ)^((1:ℝ)/1000) := hτ d
    have h2 : (d.divisors.card : ℝ) ^ ((20:ℝ)/3) ≤ (Cτ * (d:ℝ)^((1:ℝ)/1000)) ^ ((20:ℝ)/3) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : (Cτ * (d:ℝ)^((1:ℝ)/1000)) ^ ((20:ℝ)/3)
        = Cτ ^ ((20:ℝ)/3) * (d:ℝ)^((1:ℝ)/150) := by
      rw [Real.mul_rpow hCτ.le (by positivity), ← Real.rpow_mul (le_of_lt hd0)]
      norm_num
    rw [h3] at h2
    refine le_trans h2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 : (d:ℝ)^((1:ℝ)/150) ≤ (D:ℝ)^((1:ℝ)/150) :=
      Real.rpow_le_rpow (le_of_lt hd0) hdD (by norm_num)
    exact le_trans h4 (Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num))
  have hDa : (D:ℝ)^((1:ℝ)/100) * (D:ℝ)^((1:ℝ)/4) = (D:ℝ)^((1:ℝ)/4 + 1/100) := by
    rw [← Real.rpow_add hDpos]; congr 1; ring
  calc (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
        * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
      ≤ ∑ d ∈ Finset.Icc 1 D, (Cτ ^ ((20:ℝ)/3) * (D:ℝ)^((1:ℝ)/100))
          * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)| :=
        Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_right (hτb d hd) (abs_nonneg _)
    _ = (Cτ ^ ((20:ℝ)/3) * (D:ℝ)^((1:ℝ)/100))
          * (∑ d ∈ Finset.Icc 1 D, |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|) := by
        rw [Finset.mul_sum]
    _ ≤ (Cτ ^ ((20:ℝ)/3) * (D:ℝ)^((1:ℝ)/100))
          * (CAd * (D:ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100)) :=
        mul_le_mul_of_nonneg_left (hAd t D ht hD hDle) (by positivity)
    _ = (Cτ ^ ((20:ℝ)/3) * CAd) * ((D:ℝ)^((1:ℝ)/100) * (D:ℝ)^((1:ℝ)/4))
          * (t:ℝ)^((9:ℝ)/16 + 1/100) := by ring
    _ = (Cτ ^ ((20:ℝ)/3) * CAd) * (D:ℝ)^((1:ℝ)/4 + 1/100)
          * (t:ℝ)^((9:ℝ)/16 + 1/100) := by rw [hDa]
    _ ≤ (Cτ ^ ((20:ℝ)/3) * CAd + 1) * (D:ℝ)^((1:ℝ)/4 + 1/100)
          * (t:ℝ)^((9:ℝ)/16 + 1/100) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith

/-! ## The aggregate -/

/-- **The `(2.1)`-type aggregate for X² + Y⁴ on the range `D ≤ t^{3/4}`.**  From `(3.3)` and the
weighted root-count bound `(K2)`, the `τ^{20/3}`-weighted congruence sums are bounded by
`C(D^{1/4+1/100} t^{9/16+1/100} + A(t)(log(D+2))^{B₂})`. -/
theorem X2Y4_Ad_aggregate_le {C2 B2 : ℝ} (hC2 : 0 ≤ C2)
    (hK2 : ∀ c D : ℕ, (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t D : ℕ, 1 ≤ t → 1 ≤ D → D ≤ ⌊(t:ℝ)^((3:ℝ)/4)⌋₊ →
      (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * (Submission.Ad d t : ℝ))
        ≤ C * ((D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100)
            + (Submission.Aseq t : ℝ) * (Real.log ((D:ℝ)+2)) ^ B2) := by
  obtain ⟨C1, hC1, h1⟩ := sum_Ad_sub_Md_tau_pow_le
  obtain ⟨C2', hC2', h2⟩ := sum_Md_tau_pow_le hC2 hK2
  refine ⟨C1 + C2' + 1, by positivity, fun t D ht hD hDle => ?_⟩
  have hpt : ∀ d ∈ Finset.Icc 1 D,
      ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * (Submission.Ad d t : ℝ)
        ≤ ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
            * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
          + ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ) := by
    intro d hd
    have hMd0 : (0:ℝ) ≤ ((Submission.Md d t : ℚ) : ℝ) := by
      have h0 := MdNum_nonneg d t
      rw [Submission.Md]
      push_cast
      positivity
    have hle : (Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)
        ≤ |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)| := le_abs_self _
    have h2' : (Submission.Ad d t : ℝ)
        ≤ |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)| + ((Submission.Md d t : ℚ) : ℝ) := by
      linarith
    calc ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * (Submission.Ad d t : ℝ)
        ≤ ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
            * (|(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
              + ((Submission.Md d t : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
            * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
          + ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ) := by ring
  calc (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * (Submission.Ad d t : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 D, (((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
            * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
          + ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ)) :=
        Finset.sum_le_sum hpt
    _ = (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3))
            * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
          + (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ ((20 : ℝ) / 3)) * ((Submission.Md d t : ℚ) : ℝ)) :=
        Finset.sum_add_distrib
    _ ≤ C1 * (D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100)
          + C2' * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 :=
        add_le_add (h1 t D ht hD hDle) (h2 t D ht hD)
    _ ≤ (C1 + C2' + 1) * ((D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100)
          + (Submission.Aseq t : ℝ) * (Real.log ((D:ℝ)+2)) ^ B2) := by
        have hD0 : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100) := by positivity
        have hA0 : (0:ℝ) ≤ (Submission.Aseq t : ℝ) * (Real.log ((D:ℝ)+2)) ^ B2 := by
          refine mul_nonneg (by positivity) ?_
          refine Real.rpow_nonneg ?_ _
          apply Real.log_nonneg
          linarith [show (0:ℝ) ≤ (D:ℝ) by positivity]
        have hc1 : (0:ℝ) ≤ C1 := le_of_lt hC1
        have hc2 : (0:ℝ) ≤ C2' := le_of_lt hC2'
        set X : ℝ := (D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100) with hX
        set Y : ℝ := (Submission.Aseq t : ℝ) * (Real.log ((D:ℝ)+2)) ^ B2 with hY
        have hX0 : 0 ≤ X := by rw [hX]; exact hD0
        have hY0 : 0 ≤ Y := by rw [hY]; exact hA0
        have h6 : C1 ≤ C1 + C2' + 1 := by linarith
        have h7 : C2' ≤ C1 + C2' + 1 := by linarith
        have h8 : C1 * X ≤ (C1 + C2' + 1) * X := mul_le_mul_of_nonneg_right h6 hX0
        have h9 : C2' * Y ≤ (C1 + C2' + 1) * Y := mul_le_mul_of_nonneg_right h7 hY0
        calc C1 * (D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100)
              + C2' * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2
            = C1 * X + C2' * Y := by rw [hX, hY]; ring
          _ ≤ (C1 + C2' + 1) * X + (C1 + C2' + 1) * Y := add_le_add h8 h9
          _ = (C1 + C2' + 1) * (X + Y) := by ring
          _ = (C1 + C2' + 1) * ((D:ℝ)^((1:ℝ)/4 + 1/100) * (t:ℝ)^((9:ℝ)/16 + 1/100)
                + (Submission.Aseq t : ℝ) * (Real.log ((D:ℝ)+2)) ^ B2) := by rw [hX, hY]

/-! ## The `(2.3)`-type remainder bound for X² + Y⁴ -/

end

end Submission.ASP
