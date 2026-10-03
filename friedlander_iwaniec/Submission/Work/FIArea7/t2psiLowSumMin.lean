import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

namespace Work.FIArea7

open Finset

/-- `τ(c)^4 · √c ≪ c`, obtained from the divisor bound `τ(n) ≤ C n^{1/8}`
(with `eps = 1/8`, from `Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`,
already imported by `Submission.Work.FIArea7.S2Imports`). -/
private lemma tau_four_sqrt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ, 1 ≤ c →
      (((c.divisors.card : ℕ):ℝ))^4 * Real.sqrt (c:ℝ) ≤ C * (c:ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/8) (by norm_num)
  refine ⟨C0^4, by positivity, ?_⟩
  intro c hc
  have hcpos : (0:ℝ) < (c:ℝ) := by exact_mod_cast (by omega : 0 < c)
  have h1 : ((c.divisors.card:ℕ):ℝ) ≤ C0 * (c:ℝ)^((1:ℝ)/8) := hC0 c
  have h2 : ((c.divisors.card:ℕ):ℝ)^4 ≤ (C0 * (c:ℝ)^((1:ℝ)/8))^4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (C0 * (c:ℝ)^((1:ℝ)/8))^4 = C0^4 * (c:ℝ)^((1:ℝ)/2) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((c:ℝ)^((1:ℝ)/8)) 4, ← Real.rpow_mul (le_of_lt hcpos)]
    norm_num
  have h4 : Real.sqrt (c:ℝ) = (c:ℝ)^((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have h5 : (c:ℝ)^((1:ℝ)/2) * (c:ℝ)^((1:ℝ)/2) = (c:ℝ) := by
    rw [← Real.rpow_add hcpos]
    norm_num
  have hs0 : (0:ℝ) ≤ Real.sqrt (c:ℝ) := Real.sqrt_nonneg _
  calc ((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)
      ≤ (C0^4 * (c:ℝ)^((1:ℝ)/2)) * Real.sqrt (c:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hs0
        rw [← h3]; exact h2
    _ = (C0^4 * (c:ℝ)^((1:ℝ)/2)) * (c:ℝ)^((1:ℝ)/2) := by rw [h4]
    _ = C0^4 * ((c:ℝ)^((1:ℝ)/2) * (c:ℝ)^((1:ℝ)/2)) := by ring
    _ = C0^4 * (c:ℝ) := by rw [h5]

/-- `∑_{a ≤ A} τ(a)^4 a^{-1/4} ≤ C A^{3/4} (log(A+2))^{16}`, obtained from the
divisor-power estimate `∑_{a ≤ y} τ(a)^4 / a ≤ C' (log y)^{16}`
(`k = 4` in `Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit`,
already imported by `Submission.Work.FIArea7.S2Imports`) together with
`a^{-1/4} = a^{3/4} · a^{-1}` and `a^{3/4} ≤ A^{3/4}`. -/
private lemma sum_tau_four_rpow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ,
      (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 * (a:ℝ)^(-((1:ℝ)/4)))
        ≤ C * (A:ℝ)^((3:ℝ)/4) * (Real.log ((A:ℝ)+2))^16 := by
  obtain ⟨C', hC'pos, hC'⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit 4
  refine ⟨max C' (1/(Real.log 3)^16), lt_of_lt_of_le hC'pos (le_max_left _ _), ?_⟩
  intro A
  rcases Nat.eq_zero_or_pos A with hA0 | hApos
  · subst hA0; simp
  · have hstep1 : (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 * (a:ℝ)^(-((1:ℝ)/4)))
        ≤ (A:ℝ)^((3:ℝ)/4) * ∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 / (a:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      have ha1 : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp ha).1
      have hapos : (0:ℝ) < (a:ℝ) := by linarith
      have haA : (a:ℝ) ≤ (A:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp ha).2
      have hA34 : (a:ℝ)^((3:ℝ)/4) ≤ (A:ℝ)^((3:ℝ)/4) :=
        Real.rpow_le_rpow (by positivity) haA (by norm_num)
      have hrw : (a:ℝ)^(-((1:ℝ)/4)) = (a:ℝ)^((3:ℝ)/4) / (a:ℝ) := by
        have h3m1 : (-((1:ℝ)/4)) = (3:ℝ)/4 - 1 := by norm_num
        rw [h3m1, Real.rpow_sub hapos, Real.rpow_one]
      rw [hrw]
      calc (((a.divisors.card : ℕ):ℝ))^4 * ((a:ℝ)^((3:ℝ)/4) / (a:ℝ))
          = ((((a.divisors.card : ℕ):ℝ))^4 * (a:ℝ)^((3:ℝ)/4)) / (a:ℝ) := by ring
        _ ≤ ((((a.divisors.card : ℕ):ℝ))^4 * (A:ℝ)^((3:ℝ)/4)) / (a:ℝ) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hA34 (by positivity)) (le_of_lt hapos)
        _ = (A:ℝ)^((3:ℝ)/4) * ((((a.divisors.card : ℕ):ℝ))^4 / (a:ℝ)) := by ring
    have hstep2 : (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 / (a:ℝ))
        ≤ (max C' (1/(Real.log 3)^16)) * (Real.log ((A:ℝ)+2))^16 := by
      rcases Nat.lt_or_ge A 2 with hA1 | hA2
      · have hAeq : A = 1 := by omega
        subst hAeq
        have hsum : (∑ a ∈ (Finset.Icc 1 1 : Finset ℕ),
            (((a.divisors.card : ℕ):ℝ))^4 / (a:ℝ)) = 1 := by
          rw [Finset.Icc_self, Finset.sum_singleton]; simp [Nat.divisors_one]
        rw [hsum]
        have hlog3 : Real.log (((1:ℕ):ℝ) + 2) = Real.log 3 := by norm_num
        rw [hlog3]
        have hmem : 1/(Real.log 3)^16 ≤ max C' (1/(Real.log 3)^16) := le_max_right _ _
        calc (1:ℝ) = (1/(Real.log 3)^16) * (Real.log 3)^16 := by
              rw [one_div, inv_mul_cancel₀ (by positivity : (Real.log 3)^16 ≠ 0)]
          _ ≤ (max C' (1/(Real.log 3)^16)) * (Real.log 3)^16 :=
              mul_le_mul_of_nonneg_right hmem (by positivity)
      · have hlogAge0 : 0 ≤ Real.log (A:ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ A))
        have hlogAge : Real.log (A:ℝ) ≤ Real.log ((A:ℝ)+2) :=
          Real.log_le_log (by positivity) (by linarith)
        have hp : (Real.log (A:ℝ))^16 ≤ (Real.log ((A:ℝ)+2))^16 :=
          pow_le_pow_left₀ hlogAge0 hlogAge 16
        calc (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 / (a:ℝ))
            ≤ C' * (Real.log (A:ℝ))^16 := by
              have heq : C' * Real.rpow (Real.log (A:ℝ)) ((2:ℝ)^4)
                  = C' * (Real.log (A:ℝ))^16 := by
                congr 1
                rw [show (2:ℝ)^4 = (16:ℝ) by norm_num]
                exact Real.rpow_natCast _ 16
              exact le_of_le_of_eq (hC' A hA2) heq
          _ ≤ (max C' (1/(Real.log 3)^16)) * (Real.log ((A:ℝ)+2))^16 :=
              mul_le_mul (le_max_left _ _) hp (by positivity) (by positivity)
    calc (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 * (a:ℝ)^(-((1:ℝ)/4)))
        ≤ (A:ℝ)^((3:ℝ)/4) * ∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ):ℝ))^4 / (a:ℝ) :=
          hstep1
      _ ≤ (A:ℝ)^((3:ℝ)/4) * ((max C' (1/(Real.log 3)^16)) * (Real.log ((A:ℝ)+2))^16) :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ = (max C' (1/(Real.log 3)^16)) * (A:ℝ)^((3:ℝ)/4)
            * (Real.log ((A:ℝ)+2))^16 := by ring

theorem t2psiLowSumMin :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N c Y : ℕ), 1 ≤ N → 1 ≤ c → 1 ≤ Y →
        ∑ a ∈ Finset.Icc 1 (min Y N),
            (((c * a).divisors.card : ℕ) : ℝ) ^ 4 * Real.sqrt (((c * a : ℕ) : ℝ))
              * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
          ≤ K * (c : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * (Y : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 16 := by
  obtain ⟨CA, hCApos, hA⟩ := sum_tau_four_rpow_le
  obtain ⟨CB, hCBpos, hB⟩ := tau_four_sqrt_le
  refine ⟨CA*CB, by positivity, ?_⟩
  intro N c Y hN hc hY
  set m : ℕ := min Y N with hm
  set L : ℝ := Real.log ((c:ℝ)*(N:ℝ)+2) with hL
  have hcR : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hmY : m ≤ Y := by rw [hm]; exact Nat.min_le_left Y N
  have hmN : m ≤ N := by rw [hm]; exact Nat.min_le_right Y N
  have hpt : ∀ a ∈ Finset.Icc 1 m,
      (((c * a).divisors.card : ℕ) : ℝ) ^ 4 * Real.sqrt (((c * a : ℕ) : ℝ))
        * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
      ≤ ((((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)) * (N:ℝ)^((3:ℝ)/4))
        * ((((a.divisors.card:ℕ):ℝ)^4 * (a:ℝ)^(-((1:ℝ)/4)))) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haposR : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
    have h1 : (((c*a).divisors.card:ℕ):ℝ)
        ≤ ((c.divisors.card:ℕ):ℝ) * ((a.divisors.card:ℕ):ℝ) := by
      exact_mod_cast (Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le c a)
    have h1p : (((c*a).divisors.card:ℕ):ℝ)^4
        ≤ ((((c.divisors.card:ℕ):ℝ) * ((a.divisors.card:ℕ):ℝ)))^4 :=
      pow_le_pow_left₀ (by positivity) h1 4
    have e2 : Real.sqrt (((c*a:ℕ):ℝ)) = Real.sqrt (c:ℝ) * Real.sqrt (a:ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    have e3 : (((N:ℝ)/(a:ℝ))^((3:ℝ)/4)) = (N:ℝ)^((3:ℝ)/4) * (a:ℝ)^(-((3:ℝ)/4)) := by
      rw [Real.div_rpow (by positivity) (le_of_lt haposR) ((3:ℝ)/4), div_eq_mul_inv,
          ← Real.rpow_neg (le_of_lt haposR) ((3:ℝ)/4)]
    have e4 : Real.sqrt (a:ℝ) * (a:ℝ)^(-((3:ℝ)/4)) = (a:ℝ)^(-((1:ℝ)/4)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add haposR]; congr 1; norm_num
    have key : ((((c.divisors.card:ℕ):ℝ) * ((a.divisors.card:ℕ):ℝ))^4)
                 * (Real.sqrt (c:ℝ) * Real.sqrt (a:ℝ))
                 * ((N:ℝ)^((3:ℝ)/4) * (a:ℝ)^(-((3:ℝ)/4)))
             = ((((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)) * (N:ℝ)^((3:ℝ)/4))
                 * ((((a.divisors.card:ℕ):ℝ)^4 * (a:ℝ)^(-((1:ℝ)/4)))) := by
      rw [mul_pow, ← e4]; ring
    calc (((c * a).divisors.card : ℕ) : ℝ) ^ 4 * Real.sqrt (((c * a : ℕ) : ℝ))
            * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
        = (((c*a).divisors.card:ℕ):ℝ)^4 * (Real.sqrt (c:ℝ)*Real.sqrt (a:ℝ))
            * ((N:ℝ)^((3:ℝ)/4) * (a:ℝ)^(-((3:ℝ)/4))) := by rw [e2, e3]
      _ ≤ ((((c.divisors.card:ℕ):ℝ) * ((a.divisors.card:ℕ):ℝ))^4)
            * (Real.sqrt (c:ℝ)*Real.sqrt (a:ℝ))
            * ((N:ℝ)^((3:ℝ)/4) * (a:ℝ)^(-((3:ℝ)/4))) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right h1p (by positivity)
          · positivity
      _ = ((((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)) * (N:ℝ)^((3:ℝ)/4))
            * ((((a.divisors.card:ℕ):ℝ)^4 * (a:ℝ)^(-((1:ℝ)/4)))) := key
  have hlog_le : (Real.log ((m:ℝ)+2))^16 ≤ L^16 := by
    have hmNR : (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast hmN
    have hNcN : (N:ℝ) ≤ (c:ℝ)*(N:ℝ) := by
      calc (N:ℝ) = 1*(N:ℝ) := by ring
        _ ≤ (c:ℝ)*(N:ℝ) := mul_le_mul_of_nonneg_right hcR (by positivity)
    have h1 : (m:ℝ)+2 ≤ (c:ℝ)*(N:ℝ)+2 := by linarith
    have h2 : Real.log ((m:ℝ)+2) ≤ Real.log ((c:ℝ)*(N:ℝ)+2) :=
      Real.log_le_log (by positivity) h1
    have h3 : 0 ≤ Real.log ((m:ℝ)+2) := Real.log_nonneg (by linarith)
    rw [hL]
    exact pow_le_pow_left₀ h3 h2 16
  have hm34 : (m:ℝ)^((3:ℝ)/4) ≤ (Y:ℝ)^((3:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmY) (by norm_num)
  have hS : (∑ a ∈ Finset.Icc 1 m, (((a.divisors.card:ℕ):ℝ)^4 * (a:ℝ)^(-((1:ℝ)/4))))
      ≤ CA * (m:ℝ)^((3:ℝ)/4) * (Real.log ((m:ℝ)+2))^16 := hA m
  calc ∑ a ∈ Finset.Icc 1 m,
          (((c * a).divisors.card : ℕ) : ℝ) ^ 4 * Real.sqrt (((c * a : ℕ) : ℝ))
            * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
      ≤ ∑ a ∈ Finset.Icc 1 m,
          ((((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)) * (N:ℝ)^((3:ℝ)/4))
          * ((((a.divisors.card:ℕ):ℝ)^4 * (a:ℝ)^(-((1:ℝ)/4)))) := Finset.sum_le_sum hpt
    _ = ((((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)) * (N:ℝ)^((3:ℝ)/4))
          * (∑ a ∈ Finset.Icc 1 m,
              ((((a.divisors.card:ℕ):ℝ)^4 * (a:ℝ)^(-((1:ℝ)/4))))) := by
          rw [Finset.mul_sum]
    _ ≤ ((((c.divisors.card:ℕ):ℝ)^4 * Real.sqrt (c:ℝ)) * (N:ℝ)^((3:ℝ)/4))
          * (CA * (m:ℝ)^((3:ℝ)/4) * (Real.log ((m:ℝ)+2))^16) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (CB * (c:ℝ) * (N:ℝ)^((3:ℝ)/4)) * (CA * (Y:ℝ)^((3:ℝ)/4) * L^16) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (hB c hc) (by positivity)
          · apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hm34 (le_of_lt hCApos)
            · exact hlog_le
            · positivity
            · positivity
          · positivity
          · positivity
    _ = (CA*CB) * (c:ℝ) * (N:ℝ)^((3:ℝ)/4) * (Y:ℝ)^((3:ℝ)/4) * L^16 := by ring

end Work.FIArea7
