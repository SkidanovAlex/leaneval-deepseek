import Mathlib
import Submission.Helpers
import Submission.Commons.Analysis.SpecialFunctions.four_kappa_div_pi_gt
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs_asymptotic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.infinite_X2Y4_primes_of_lambda_sum_lower_bound

/-!
# The endgame of Friedlander–Iwaniec, assembled

This file records the *exact* remaining interface of the proof of

  `{p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite`

(Theorem 1 of J. Friedlander, H. Iwaniec, *The polynomial X² + Y⁴ captures its
primes*, Ann. of Math. **148** (1998), 945–1040).

Everything in the paper (and in its companion, *Asymptotic sieve for primes*,
Ann. of Math. **148** (1998), 1041–1065) is contained in the single asymptotic

  `∑_{p ≤ x} a⁺_p log p = (4/π) κ x^{3/4} (1 + O(log log x / log x))`,   (★)

where `a⁺_n = #{(a,b) ∈ ℕ² : a, b ≥ 1, a² + b⁴ = n}` and `κ = ∫₀¹ √(1-u⁴) du`
(the main term of `A⁺(x) = ∑_{n≤x} a⁺_n`, proved in the commons:
`card_sq_add_pow_four_natpairs_asymptotic`).

`friedlander_iwaniec_of_sieve_main_term` below shows that (★) alone implies the
challenge theorem; the numerical input is `4κ/π > 1.11`
(commons lemma `Commons.Analysis.SpecialFunctions.four_kappa_div_pi_gt`) together
with the positivity of the von Mangoldt function.
-/

namespace Submission

open Filter Finset

/-- `a⁺_n = #{(a, b) ∈ ℕ × ℕ : 1 ≤ a, 1 ≤ b, a² + b⁴ = n}`: the Friedlander–Iwaniec
sequence, counting representations by *positive* integers. -/
noncomputable def apos (n : ℕ) : ℕ :=
  ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = n}).ncard

/-- `A⁺(x) = ∑_{n ≤ x} a⁺_n`. -/
noncomputable def Apos (x : ℕ) : ℕ := ∑ n ∈ Finset.range (x + 1), apos n

/-- The prime sum `∑_{p ≤ x} a⁺_p log p`. -/
noncomputable def primeSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (x + 1), Real.log (p : ℝ) * (apos p : ℝ)

/-- The Λ-sum `∑_{n ≤ x} Λ(n) a⁺_n`. -/
noncomputable def lambdaSum (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n * (apos n : ℝ)

/-- `κ = ∫₀¹ √(1-u⁴) du`, the constant of the main term `A⁺(x) = κ x^{3/4} + O(√x)`. -/
noncomputable def kappa : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4)

lemma kappa_nonneg : 0 ≤ kappa := by
  rw [kappa]
  exact intervalIntegral.integral_nonneg (by norm_num) fun t _ => Real.sqrt_nonneg _

/-- The prime sum is at most the von Mangoldt sum (`Λ ≥ 0`, `Λ(p) = log p`). -/
theorem primeSum_le_lambdaSum (x : ℕ) : primeSum x ≤ lambdaSum x := by
  unfold primeSum lambdaSum
  rw [Nat.primesBelow_eq_filter_range]
  calc ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (apos p : ℝ)
      = ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt p * (apos p : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    _ ≤ ∑ n ∈ Finset.range (x + 1),
          ArithmeticFunction.vonMangoldt n * (apos n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by
            have h := ArithmeticFunction.vonMangoldt_nonneg (n := i)
            positivity)

/-- **The endgame I**: a lower bound for the prime sum over `a⁺` gives the theorem. -/
theorem friedlander_iwaniec_of_prime_sum_lower
    (h : ∀ᶠ x : ℕ in atTop,
      (1.11 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ) ≤ primeSum x) :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite :=
  Commons.NumberTheory.FriedlanderIwaniec.infinite_X2Y4_primes_of_lambda_sum_lower_bound
    (h.mono fun x hx => le_trans hx (primeSum_le_lambdaSum x))

lemma four_pi_kappa_eq :
    (4 : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) / Real.pi = 4 / Real.pi * kappa := by
  rw [kappa]; ring

lemma four_pi_kappa_pos : 0 < 4 / Real.pi * kappa := by
  have h0 := Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hk : 0 < kappa := by
    rw [kappa]; linarith
  positivity

lemma one_lt_four_pi_kappa : (1.11 : ℝ) < 4 / Real.pi * kappa := by
  have h0 := Commons.Analysis.SpecialFunctions.four_kappa_div_pi_gt
  rw [four_pi_kappa_eq] at h0
  exact h0

/-- The asymptotic sieve input (★), in the *absolute margin* form in which we use it:
the error is smaller than half of the numerical margin `4κ/π - 1.11`. -/
def SieveMarginForm : Prop :=
  ∀ᶠ x : ℕ in atTop,
    |primeSum x - (4 / Real.pi) * kappa * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ ((4 / Real.pi) * kappa - 1.11) / 2 * (x : ℝ) ^ (3 / 4 : ℝ)

/-- **The endgame II**: the asymptotic sieve (★) in margin form implies the challenge
theorem. -/
theorem friedlander_iwaniec_of_sieve_margin (h : SieveMarginForm) :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite := by
  apply friedlander_iwaniec_of_prime_sum_lower
  filter_upwards [h] with x hx
  have h1 := (abs_le.mp hx).1
  have hx0 : (0 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have h2 : (4 / Real.pi * kappa - ((4 / Real.pi * kappa - 1.11) / 2)) * (x : ℝ) ^ (3 / 4 : ℝ)
      = (4 / Real.pi * kappa + 1.11) / 2 * (x : ℝ) ^ (3 / 4 : ℝ) := by ring
  have h3 : (1.11 : ℝ) < 4 / Real.pi * kappa - ((4 / Real.pi * kappa - 1.11) / 2) := by
    linarith [one_lt_four_pi_kappa]
  calc (1.11 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ)
      ≤ (4 / Real.pi * kappa - ((4 / Real.pi * kappa - 1.11) / 2)) * (x : ℝ) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h3.le hx0
    _ ≤ primeSum x := by linarith

/-- The asymptotic sieve (★) in the paper's *relative-error* form,
`∑_{p ≤ x} a⁺_p log p = (4/π) κ x^{3/4} (1 + O(log log x / log x))`. -/
def SieveAsymptotic : Prop :=
  ∀ᶠ x : ℕ in atTop,
    |primeSum x - (4 / Real.pi) * kappa * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ (4 / Real.pi) * kappa * (x : ℝ) ^ (3 / 4 : ℝ) * (Real.log (Real.log x) / Real.log x)

/-- `log log x / log x → 0`. -/
lemma tendsto_loglog_div_log :
    Tendsto (fun x : ℕ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) :=
  ((Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop

/-- **The endgame III**: the asymptotic sieve (★) in its relative-error form implies
the challenge theorem. -/
theorem friedlander_iwaniec_of_sieve_asymptotic (h : SieveAsymptotic) :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite := by
  apply friedlander_iwaniec_of_sieve_margin
  have hK := four_pi_kappa_pos
  set c : ℝ := (4 / Real.pi * kappa - 1.11) / (2 * (4 / Real.pi * kappa)) with hc
  have hkpos : 0 < kappa := by
    have h4 : (0:ℝ) < 4 / Real.pi := div_pos (by norm_num) Real.pi_pos
    nlinarith [four_pi_kappa_pos, h4]
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos (by linarith [one_lt_four_pi_kappa]) (by linarith [four_pi_kappa_pos])
  have hcval : 4 / Real.pi * kappa * c = (4 / Real.pi * kappa - 1.11) / 2 := by
    rw [hc]; field_simp
  have hev : ∀ᶠ x : ℕ in atTop, Real.log (Real.log x) / Real.log x ≤ c :=
    tendsto_loglog_div_log.eventually (eventually_le_nhds hcpos)
  filter_upwards [h, hev] with x hx hcv
  have hx0 : (0 : ℝ) ≤ 4 / Real.pi * kappa * (x : ℝ) ^ (3 / 4 : ℝ) :=
    mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  have hxx : (0 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  calc |primeSum x - 4 / Real.pi * kappa * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ 4 / Real.pi * kappa * (x : ℝ) ^ (3 / 4 : ℝ) * (Real.log (Real.log x) / Real.log x) := hx
    _ ≤ 4 / Real.pi * kappa * (x : ℝ) ^ (3 / 4 : ℝ) * c :=
        mul_le_mul_of_nonneg_left hcv hx0
    _ = (4 / Real.pi * kappa - 1.11) / 2 * (x : ℝ) ^ (3 / 4 : ℝ) := by
        rw [show (4:ℝ) / Real.pi * kappa * (x : ℝ) ^ (3 / 4 : ℝ) * c
            = (4 / Real.pi * kappa * c) * (x : ℝ) ^ (3 / 4 : ℝ) from by ring, hcval]
end Submission
