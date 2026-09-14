import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

namespace Commons.NumberTheory.Height.MvPolynomial

open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ]

/-! ### Auxiliary lemmas -/

/-- Every archimedean absolute value on `ℚ` is the usual absolute value: it takes a natural
number `n` to `n`. -/
lemma archAbsVal_apply_natCast {a : AbsoluteValue ℚ ℝ}
    (ha : a ∈ Height.AdmissibleAbsValues.archAbsVal (K := ℚ)) (n : ℕ) :
    a (n : ℚ) = (n : ℝ) := by
  obtain ⟨w, hw⟩ := NumberField.isInfinitePlace_iff a |>.mp
    (NumberField.mem_multisetInfinitePlace.mp ha)
  rw [← hw]
  exact NumberField.InfinitePlace.map_natCast w n

/-- The product of binomial coefficients `∏ i, choose (m i) (ν i)` is bounded by
`2 ^ (∑ i, m i)`. -/
lemma choose_prod_cast_le_two_pow (m ν : σ →₀ ℕ) :
    (∏ i : σ, (Nat.choose (m i) (ν i) : ℝ)) ≤ (2 : ℝ) ^ (∑ i, m i) := by
  have h1 : ∀ i : σ, (Nat.choose (m i) (ν i) : ℝ) ≤ (2 : ℝ) ^ (m i) := by
    intro i
    exact_mod_cast Nat.choose_le_two_pow (m i) (ν i)
  calc ∏ i : σ, (Nat.choose (m i) (ν i) : ℝ)
      ≤ ∏ i : σ, (2 : ℝ) ^ (m i) :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => h1 i)
    _ = (2 : ℝ) ^ (∑ i, m i) := by rw [Finset.prod_pow_eq_pow_sum]

/-- Version of `choose_prod_cast_le_two_pow` for a natural-number product cast to `ℝ`. -/
lemma choose_prod_natCast_le_two_pow (m ν : σ →₀ ℕ) :
    ((∏ i : σ, Nat.choose (m i) (ν i) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (∑ i, m i) := by
  rw [Nat.cast_prod]
  exact choose_prod_cast_le_two_pow m ν

/-- Archimedean part of the coefficient bound: the sup of the coefficients of `Q` at an
archimedean place is bounded by `2 ^ (∑ r)` times that of `P`. -/
lemma coeffSup_arch_le (r : σ → ℕ) (ν : σ →₀ ℕ) (P Q : MvPolynomial σ ℚ)
    (hQ : ∀ n : σ →₀ ℕ, MvPolynomial.coeff n Q =
      MvPolynomial.coeff (n + ν) P * ∏ i : σ, Nat.choose ((n + ν) i) (ν i))
    (h : ∀ t ∈ P.support, ∀ j : σ, t j ≤ r j)
    {a : AbsoluteValue ℚ ℝ} (ha : a ∈ Height.AdmissibleAbsValues.archAbsVal (K := ℚ)) :
    coeffSup a Q ≤ (2 : ℝ) ^ (∑ j, r j) * coeffSup a P := by
  refine ciSup_le (fun n => ?_)
  rw [hQ n, map_mul, archAbsVal_apply_natCast ha]
  by_cases hmem : (n + ν) ∈ P.support
  · have hle : a (MvPolynomial.coeff (n + ν) P) ≤ coeffSup a P := le_coeffSup a P (n + ν)
    have hprod : ((∏ i : σ, Nat.choose ((n + ν) i) (ν i) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (∑ j, r j) := by
      refine le_trans (choose_prod_natCast_le_two_pow (n + ν) ν) ?_
      refine pow_le_pow_right₀ (by norm_num) ?_
      exact_mod_cast Finset.sum_le_sum (fun j _ => h (n + ν) hmem j)
    have hprod_nn : 0 ≤ ((∏ i : σ, Nat.choose ((n + ν) i) (ν i) : ℕ) : ℝ) := by positivity
    calc a (MvPolynomial.coeff (n + ν) P) *
            ((∏ i : σ, Nat.choose ((n + ν) i) (ν i) : ℕ) : ℝ)
        ≤ coeffSup a P * (2 : ℝ) ^ (∑ j, r j) :=
          mul_le_mul hle hprod hprod_nn (coeffSup_nonneg a P)
      _ = (2 : ℝ) ^ (∑ j, r j) * coeffSup a P := by ring
  · have hzero : MvPolynomial.coeff (n + ν) P = 0 := MvPolynomial.notMem_support_iff.mp hmem
    rw [hzero, AbsoluteValue.map_zero, zero_mul]
    exact mul_nonneg (by positivity) (coeffSup_nonneg a P)

/-- Nonarchimedean part of the coefficient bound: at a nonarchimedean place the sup of the
coefficients of `Q` is bounded by that of `P`. -/
lemma coeffSup_nonarch_le (r : σ → ℕ) (ν : σ →₀ ℕ) (P Q : MvPolynomial σ ℚ)
    (hQ : ∀ n : σ →₀ ℕ, MvPolynomial.coeff n Q =
      MvPolynomial.coeff (n + ν) P * ∏ i : σ, Nat.choose ((n + ν) i) (ν i))
    (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)) :
    coeffSup v.val Q ≤ coeffSup v.val P := by
  have hv : IsNonarchimedean (⇑v.val : ℚ → ℝ) :=
    Height.AdmissibleAbsValues.isNonarchimedean v.val v.prop
  refine ciSup_le (fun n => ?_)
  rw [hQ n, map_mul]
  have h2 : v.val (((∏ i : σ, Nat.choose ((n + ν) i) (ν i) : ℕ) : ℕ) : ℚ) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one hv
  calc v.val (MvPolynomial.coeff (n + ν) P) *
          v.val ((∏ i : σ, Nat.choose ((n + ν) i) (ν i) : ℕ) : ℚ)
      ≤ coeffSup v.val P * 1 :=
        mul_le_mul (le_coeffSup v.val P (n + ν)) h2 (v.val.nonneg _) (coeffSup_nonneg v.val P)
    _ = coeffSup v.val P := mul_one _

/-! ### The main statement -/

theorem logHeight_gP_of_coeff_bound {σ : Type*} [Fintype σ] (r : σ → ℕ) (ν : σ →₀ ℕ)
    (P Q : MvPolynomial σ ℚ)
    (hQ : ∀ n : σ →₀ ℕ, MvPolynomial.coeff n Q =
      MvPolynomial.coeff (n + ν) P * ∏ i : σ, Nat.choose ((n + ν) i) (ν i))
    (h : ∀ t ∈ P.support, ∀ j : σ, t j ≤ r j) :
    Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP Q) ≤
      Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP P) +
        ((∑ j : σ, r j : ℕ) : ℝ) * Real.log 2 := by
  classical
  set C : ℝ := (2 : ℝ) ^ (∑ j, r j) with hCdef
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact one_le_pow₀ (by norm_num)
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hCne : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  -- the single archimedean place of `ℚ`
  have hcard : (Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).card = 1 := by
    rw [← Height.totalWeight, NumberField.totalWeight_eq_finrank]
    simp [Module.finrank_self]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  have hamem : a ∈ Height.AdmissibleAbsValues.archAbsVal (K := ℚ) := by
    rw [ha]; exact Multiset.mem_singleton_self a
  -- archimedean comparison
  have harch : ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
        (fun v => max 1 (coeffSup v Q))).prod
      ≤ C * ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
            (fun v => max 1 (coeffSup v P))).prod := by
    rw [ha]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    have hstep := max_one_le_of_mul_le (a := coeffSup a Q) (x := C) (y := coeffSup a P)
      hC0 (coeffSup_nonneg a P) (by rw [hCdef]; exact coeffSup_arch_le r ν P Q hQ h hamem)
    rwa [max_eq_right hC1] at hstep
  -- nonarchimedean comparison
  have hnonarch : (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
        (⨆ i : tP Q, v.val (gP Q i)))
      ≤ (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
            (⨆ i : tP P, v.val (gP P i))) := by
    have hfQ : (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ) =>
        (⨆ i : tP Q, v.val (gP Q i))).HasFiniteMulSupport := by
      fun_prop (disch := exact gP_restrict_ne_zero Q)
    have hfP : (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ) =>
        (⨆ i : tP P, v.val (gP P i))).HasFiniteMulSupport := by
      fun_prop (disch := exact gP_restrict_ne_zero P)
    refine finprod_le_finprod hfQ (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _) hfP
      (fun v => ?_)
    rw [iSup_gP_eq v.val Q, iSup_gP_eq v.val P]
    exact max_le_max le_rfl (coeffSup_nonarch_le r ν P Q hQ v)
  -- assemble the multiplicative inequality
  have hmain : Height.mulHeight (gP Q) ≤ C * Height.mulHeight (gP P) := by
    rw [mulHeight_gP_eq_prod Q, mulHeight_gP_eq_prod P]
    have hAPnn : 0 ≤ ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
        (fun v => max 1 (coeffSup v P))).prod :=
      Multiset.prod_nonneg (fun b hb => by
        obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hb
        exact le_trans zero_le_one (le_max_left _ _))
    have hBPnn : 0 ≤ (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
        (⨆ i : tP P, v.val (gP P i))) :=
      finprod_nonneg (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
    calc ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
            (fun v => max 1 (coeffSup v Q))).prod *
          (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
            (⨆ i : tP Q, v.val (gP Q i)))
        ≤ (C * ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
              (fun v => max 1 (coeffSup v P))).prod) *
            (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
              (⨆ i : tP P, v.val (gP P i))) :=
          mul_le_mul harch hnonarch
            (finprod_nonneg (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _))
            (mul_nonneg hC0 hAPnn)
      _ = C * (((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
              (fun v => max 1 (coeffSup v P))).prod *
            (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
              (⨆ i : tP P, v.val (gP P i)))) := by ring
  -- take logarithms
  have hposQ : 0 < Height.mulHeight (gP Q) := by
    rw [mulHeight_gP_eq Q]
    exact lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight (fun i : tP Q => gP Q i))
  have hposP : 0 < Height.mulHeight (gP P) := by
    rw [mulHeight_gP_eq P]
    exact lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight (fun i : tP P => gP P i))
  have hlog := Real.log_le_log hposQ hmain
  rw [Real.log_mul hCne hposP.ne'] at hlog
  simp only [Height.logHeight_eq_log_mulHeight]
  rw [hCdef, Real.log_pow] at hlog
  linarith [hlog]

end Commons.NumberTheory.Height.MvPolynomial
