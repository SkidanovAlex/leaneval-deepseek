import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.composite_part_eventually_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.prime_part_le_card_mul

namespace Commons.NumberTheory.FriedlanderIwaniec

open Filter

/-- Eventually, `Real.log x ≤ x ^ (1/4)`, in the variable `x : ℕ`. -/
lemma eventually_log_nat_le_rpow_quarter :
    ∀ᶠ x : ℕ in Filter.atTop, Real.log (x : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ (1 / 4 : ℝ) := by
    have h :=
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventuallyLE
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx1) _)] at hx
    exact hx
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal

/-- For a fixed `M`, `M · (x^{1/2} + x^{1/4})` is eventually less than
`0.01 · x^{3/4}`. -/
lemma eventually_card_mul_lt :
    ∀ M : ℕ, ∀ᶠ x : ℕ in Filter.atTop,
      (M : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) + (x : ℝ) ^ (1 / 4 : ℝ))
        < 0.01 * (x : ℝ) ^ (3 / 4 : ℝ) := by
  intro M
  rw [Filter.eventually_atTop]
  refine ⟨(200 * M + 1) ^ 4, fun x hx => ?_⟩
  set K : ℕ := 200 * M + 1 with hK
  have hx1 : 1 ≤ x := by
    have : 0 < K ^ 4 := pow_pos (by omega : 0 < K) 4
    omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hx1)
  have hxK : ((K : ℝ)) ^ 4 ≤ (x : ℝ) := by exact_mod_cast hx
  have hval : ((K : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (K : ℝ) := by
    rw [← Real.rpow_natCast (K : ℝ) 4,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (K : ℝ))]
    rw [show (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) = 1 by norm_num, Real.rpow_one]
  have haK : (K : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have hh := Real.rpow_le_rpow (show (0 : ℝ) ≤ (K : ℝ) ^ 4 by positivity) hxK
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [hval] at hh
  have haK' : (200 : ℝ) * (M : ℝ) + 1 ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have h := haK; rw [hK] at h; push_cast at h; linarith
  have ha0 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have ha2 : (x : ℝ) ^ (1 / 2 : ℝ) = ((x : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [show (1 / 2 : ℝ) = (1 / 4 : ℝ) * 2 by norm_num,
      Real.rpow_mul hx0.le (1 / 4 : ℝ) (2 : ℝ)]
    exact Real.rpow_natCast _ 2
  have ha3 : (x : ℝ) ^ (3 / 4 : ℝ) = ((x : ℝ) ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [show (3 / 4 : ℝ) = (1 / 4 : ℝ) * 3 by norm_num,
      Real.rpow_mul hx0.le (1 / 4 : ℝ) (3 : ℝ)]
    exact Real.rpow_natCast _ 3
  rw [ha2, ha3]
  nlinarith [haK', (Nat.cast_nonneg M : (0 : ℝ) ≤ (M : ℝ)), ha0]

theorem infinite_X2Y4_primes_of_lambda_sum_lower_bound
    (h : ∀ᶠ x : ℕ in Filter.atTop,
        1.11 * (x : ℝ) ^ (3 / 4 : ℝ) ≤
          ∑ n ∈ Finset.range (x + 1),
            ArithmeticFunction.vonMangoldt n *
              (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ)) :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite := by
  classical
  set T : Set ℕ := {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4} with hT
  by_contra hinf
  rw [Set.not_infinite] at hinf
  have hTfin : T.Finite := hinf
  set M : ℕ := T.ncard with hM
  -- The prime part of the sum is bounded by `M · log x · (x^{1/4}+1)`.
  have hprime_le : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt p *
            (({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}.ncard : ℕ) : ℝ))
        ≤ (M : ℝ) * (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx1
    have hb := prime_part_le_card_mul (x := x) hx1
    have hsub : ({p : ℕ | p ≤ x ∧ p.Prime ∧
          ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ p = a ^ 2 + b ^ 4} : Set ℕ) ⊆ T := by
      intro p hp
      obtain ⟨-, hpp, a, b, -, -, hab⟩ := hp
      exact ⟨hpp, a, b, hab⟩
    have hcard : ({p : ℕ | p ≤ x ∧ p.Prime ∧
          ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ p = a ^ 2 + b ^ 4} : Set ℕ).ncard ≤ M := by
      have hh := Set.ncard_le_ncard hsub hTfin
      rw [← hM] at hh
      exact hh
    have hfac : 0 ≤ Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) := by
      apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hx1))
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ (x : ℝ) by positivity) (1 / 4 : ℝ)
      linarith
    calc (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt p *
            (({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}.ncard : ℕ) : ℝ))
        ≤ Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) *
            (({p : ℕ | p ≤ x ∧ p.Prime ∧
              ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ p = a ^ 2 + b ^ 4} : Set ℕ).ncard : ℝ) := hb
      _ ≤ Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hfac
      _ = (M : ℝ) * (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) := by ring
  -- Combine both parts to contradict the assumed lower bound.
  have hbound : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ n ∈ Finset.range (x + 1),
          ArithmeticFunction.vonMangoldt n *
            (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
        < 1.11 * (x : ℝ) ^ (3 / 4 : ℝ) := by
    filter_upwards [composite_part_eventually_le, hprime_le,
      eventually_log_nat_le_rpow_quarter, eventually_card_mul_lt M,
      eventually_ge_atTop (1 : ℕ)] with x hcomp hpr hlog hbg hx1
    have hx0 : (0 : ℝ) < (x : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hx1)
    have hlog' : Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)
        ≤ (x : ℝ) ^ (1 / 2 : ℝ) + (x : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 : (x : ℝ) ^ (1 / 4 : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)
          = (x : ℝ) ^ (1 / 2 : ℝ) + (x : ℝ) ^ (1 / 4 : ℝ) := by
        have hmul : (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ)
            = (x : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
        rw [mul_add, mul_one, hmul]
      calc Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)
          ≤ (x : ℝ) ^ (1 / 4 : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hlog (by positivity)
        _ = (x : ℝ) ^ (1 / 2 : ℝ) + (x : ℝ) ^ (1 / 4 : ℝ) := h1
    have hstep : (M : ℝ) * (Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1))
        < 0.01 * (x : ℝ) ^ (3 / 4 : ℝ) :=
      calc (M : ℝ) * (Real.log (x : ℝ) * ((x : ℝ) ^ (1 / 4 : ℝ) + 1))
          ≤ (M : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) + (x : ℝ) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ < 0.01 * (x : ℝ) ^ (3 / 4 : ℝ) := hbg
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range (x + 1))
      (p := fun n : ℕ => n.Prime)
      (f := fun n : ℕ => ArithmeticFunction.vonMangoldt n *
        (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
    calc (∑ n ∈ Finset.range (x + 1),
          ArithmeticFunction.vonMangoldt n *
            (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
        = (∑ n ∈ (Finset.range (x + 1)).filter (fun n : ℕ => n.Prime),
            ArithmeticFunction.vonMangoldt n *
              (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
          + (∑ n ∈ (Finset.range (x + 1)).filter (fun n : ℕ => ¬ n.Prime),
            ArithmeticFunction.vonMangoldt n *
              (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ)) :=
          hsplit.symm
      _ ≤ (M : ℝ) * (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1))
            + 1.1 * (x : ℝ) ^ (3 / 4 : ℝ) := add_le_add hpr hcomp
      _ < 0.01 * (x : ℝ) ^ (3 / 4 : ℝ) + 1.1 * (x : ℝ) ^ (3 / 4 : ℝ) := by
          linarith [hstep]
      _ = 1.11 * (x : ℝ) ^ (3 / 4 : ℝ) := by ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp hbound
  have h1 := hN (max N N') (le_max_left _ _)
  have h2 := hN' (max N N') (le_max_right _ _)
  linarith

end Commons.NumberTheory.FriedlanderIwaniec
