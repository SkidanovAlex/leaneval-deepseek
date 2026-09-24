import Mathlib
import Submission.Commons.NumberTheory.Linnik.polyaVinogradov
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_normSq_eq_conductor
import Submission.Commons.NumberTheory.Divisors.card_divisors_le_two_mul_sqrt
import Submission.Commons.NumberTheory.DirichletCharacter.sum_filter_dvd_char_range
import Submission.Commons.NumberTheory.DirichletCharacter.char_eq_moebius_sum

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.DirichletCharacter

/-- The norm of (the image in `ℂ` of) the Möbius function is at most `1`. -/
private lemma norm_moebius_le_one (c : ℕ) : ‖(ArithmeticFunction.moebius c : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := c)

theorem polya_vinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (_hχ : χ ≠ 1)
      (N : ℕ), ‖∑ n ∈ Finset.range (N + 1), χ n‖ ≤ C * Real.sqrt q * Real.log q := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.NumberTheory.Linnik.polyaVinogradov
  refine ⟨6 * C0, by positivity, ?_⟩
  intro q hq χ hχ N
  haveI hq_ne : NeZero q := ⟨by omega⟩
  haveI hd_ne : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hmul : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hdvd
  have hm0 : q / χ.conductor ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact (NeZero.ne q) hmul.symm
  have hψprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hψ_ne_one : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
    have hc := congrArg DirichletCharacter.conductor h
    rw [DirichletCharacter.conductor_one] at hc
    rwa [χ.primitiveCharacter_isPrimitive] at hc
  -- The character identity and the resulting sum identity.
  have hsum :
      ∑ n ∈ Finset.range (N + 1), (χ (n : ZMod q) : ℂ)
        = ∑ c ∈ (q / χ.conductor).divisors,
            (ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)
              * (∑ k ∈ Finset.range (N / c + 1),
                  (χ.primitiveCharacter (k : ZMod χ.conductor) : ℂ)) := by
    rw [Finset.sum_congr rfl (fun n _ => char_eq_moebius_sum χ hχ n)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have hcpos : 0 < c := by
      rw [Nat.mem_divisors] at hc
      exact Nat.pos_of_dvd_of_pos hc.1 (Nat.pos_of_ne_zero hm0)
    rw [show (∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)
            * (if c ∣ n then (1 : ℂ) else 0))
        = (ArithmeticFunction.moebius c : ℂ)
            * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => c ∣ n),
                (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) from by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : c ∣ n <;> simp [h]]
    rw [sum_filter_dvd_char_range χ.primitiveCharacter c N hcpos]
    ring
  rw [hsum]
  -- termwise bound
  have hper (c : ℕ) :
      ‖(ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)
        * (∑ k ∈ Finset.range (N / c + 1),
            (χ.primitiveCharacter (k : ZMod χ.conductor) : ℂ))‖
      ≤ C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2) := by
    have hV := hC0 (q := χ.conductor) χ.primitiveCharacter hψ_ne_one hψprim (N / c + 1)
    have hμψ : ‖(ArithmeticFunction.moebius c : ℂ)
        * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)‖ ≤ 1 := by
      calc ‖(ArithmeticFunction.moebius c : ℂ)
            * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)‖
          ≤ ‖(ArithmeticFunction.moebius c : ℂ)‖
              * ‖(χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (norm_moebius_le_one c)
              (DirichletCharacter.norm_le_one _ _) (by positivity) (by norm_num)
        _ = 1 := by ring
    calc ‖(ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)
            * (∑ k ∈ Finset.range (N / c + 1),
                (χ.primitiveCharacter (k : ZMod χ.conductor) : ℂ))‖
        ≤ ‖(ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)‖
            * ‖(∑ k ∈ Finset.range (N / c + 1),
                (χ.primitiveCharacter (k : ZMod χ.conductor) : ℂ))‖ := norm_mul_le _ _
      _ ≤ 1 * (C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2)) :=
            mul_le_mul hμψ hV (norm_nonneg _) (by norm_num)
      _ = C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2) := by ring
  have hd0 : (0 : ℝ) < (χ.conductor : ℝ) := by
    have : 0 < χ.conductor := Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    exact_mod_cast this
  have hLnn : 0 ≤ Real.log ((χ.conductor : ℝ) + 2) := by
    apply Real.log_nonneg; linarith [hd0]
  have hC0nn : 0 ≤ C0 := le_of_lt hC0pos
  -- numeric endgame
  have hfinal : (2 * (Nat.sqrt (q / χ.conductor) : ℝ) + 1)
        * (C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2))
      ≤ 6 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    have hm0' : (0 : ℝ) < ((q / χ.conductor : ℕ) : ℝ) := by
      have : 0 < q / χ.conductor := Nat.pos_of_ne_zero hm0
      exact_mod_cast this
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      exact_mod_cast this
    have hsqrtq : Real.sqrt (q : ℝ)
        = Real.sqrt (χ.conductor : ℝ) * Real.sqrt ((q / χ.conductor : ℕ) : ℝ) := by
      have hcast : (q : ℝ) = (χ.conductor : ℝ) * ((q / χ.conductor : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, hmul]
      rw [hcast, Real.sqrt_mul (le_of_lt hd0)]
    have hA : 0 ≤ Real.sqrt (χ.conductor : ℝ) := Real.sqrt_nonneg _
    have hsm : (Nat.sqrt (q / χ.conductor) : ℝ) ≤ Real.sqrt ((q / χ.conductor : ℕ) : ℝ) := by
      have h1 : ((Nat.sqrt (q / χ.conductor) : ℕ) : ℝ) ^ 2 ≤ ((q / χ.conductor : ℕ) : ℝ) := by
        rw [← Nat.cast_pow]; exact_mod_cast Nat.sqrt_le' (q / χ.conductor)
      calc (Nat.sqrt (q / χ.conductor) : ℝ)
          = Real.sqrt (((Nat.sqrt (q / χ.conductor) : ℕ) : ℝ) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt ((q / χ.conductor : ℕ) : ℝ) := Real.sqrt_le_sqrt h1
    have hsqrtd_le : Real.sqrt (χ.conductor : ℝ) ≤ Real.sqrt (q : ℝ) :=
      Real.sqrt_le_sqrt (by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd)
    have hlog : Real.log ((χ.conductor : ℝ) + 2) ≤ 2 * Real.log (q : ℝ) := by
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hdd_le : (χ.conductor : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd
      have hle : (χ.conductor : ℝ) + 2 ≤ (q : ℝ) ^ 2 := by nlinarith
      have hpos : 0 < (χ.conductor : ℝ) + 2 := by linarith [hd0]
      calc Real.log ((χ.conductor : ℝ) + 2) ≤ Real.log ((q : ℝ) ^ 2) :=
            Real.log_le_log hpos hle
        _ = 2 * Real.log (q : ℝ) := by rw [Real.log_pow]; norm_num
    have hstep : (2 * (Nat.sqrt (q / χ.conductor) : ℝ) + 1) * Real.sqrt (χ.conductor : ℝ)
        ≤ 3 * Real.sqrt (q : ℝ) := by
      have h2 : (2 * Real.sqrt ((q / χ.conductor : ℕ) : ℝ) + 1) * Real.sqrt (χ.conductor : ℝ)
          ≤ 3 * Real.sqrt (q : ℝ) := by
        have hsq : 2 * Real.sqrt ((q / χ.conductor : ℕ) : ℝ) * Real.sqrt (χ.conductor : ℝ)
            = 2 * Real.sqrt (q : ℝ) := by rw [hsqrtq]; ring
        nlinarith [hsq, hsqrtd_le]
      calc (2 * (Nat.sqrt (q / χ.conductor) : ℝ) + 1) * Real.sqrt (χ.conductor : ℝ)
          ≤ (2 * Real.sqrt ((q / χ.conductor : ℕ) : ℝ) + 1) * Real.sqrt (χ.conductor : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith [hsm]) hA
        _ ≤ 3 * Real.sqrt (q : ℝ) := h2
    calc (2 * (Nat.sqrt (q / χ.conductor) : ℝ) + 1)
            * (C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2))
        = ((2 * (Nat.sqrt (q / χ.conductor) : ℝ) + 1) * Real.sqrt (χ.conductor : ℝ))
            * (C0 * Real.log ((χ.conductor : ℝ) + 2)) := by ring
      _ ≤ (3 * Real.sqrt (q : ℝ)) * (C0 * Real.log ((χ.conductor : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hstep (mul_nonneg hC0nn hLnn)
      _ ≤ (3 * Real.sqrt (q : ℝ)) * (C0 * (2 * Real.log (q : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hC0nn) (by positivity)
      _ = 6 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by ring
  calc ‖∑ c ∈ (q / χ.conductor).divisors,
          (ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)
            * (∑ k ∈ Finset.range (N / c + 1),
                (χ.primitiveCharacter (k : ZMod χ.conductor) : ℂ))‖
      ≤ ∑ c ∈ (q / χ.conductor).divisors,
          ‖(ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (c : ZMod χ.conductor) : ℂ)
            * (∑ k ∈ Finset.range (N / c + 1),
                (χ.primitiveCharacter (k : ZMod χ.conductor) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ (q / χ.conductor).divisors,
          (C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2)) :=
          Finset.sum_le_sum (fun c _ => hper c)
    _ = ((q / χ.conductor).divisors.card : ℝ)
          * (C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (Nat.sqrt (q / χ.conductor) : ℝ) + 1)
          * (C0 * Real.sqrt (χ.conductor : ℝ) * Real.log ((χ.conductor : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (mul_nonneg hC0nn (Real.sqrt_nonneg _)) hLnn)
          have h := Commons.NumberTheory.Divisors.card_divisors_le_two_mul_sqrt (q / χ.conductor)
          exact_mod_cast h
    _ ≤ 6 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := hfinal

end Commons.NumberTheory.DirichletCharacter
