import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

namespace Commons.NumberTheory.Height.MvPolynomial

open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ]

/-- Left-only two-fold height bound: the correction term only needs a bound on the number of
monomials of the *left* factor. This is `polyHeight_mul_le` with the (unused) hypothesis on `Q`
removed. -/
theorem polyHeight_mul_le_left (P Q : MvPolynomial σ ℚ) (N : ℕ)
    (hN : 1 ≤ N) (hP : P.support.card ≤ N) :
    Height.logHeight (gP (P * Q)) ≤
      Height.logHeight (gP P) + Height.logHeight (gP Q) + Real.log N := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- archimedean place
  have hcard : (Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).card = 1 := by
    rw [← Height.totalWeight, NumberField.totalWeight_eq_finrank]
    simp [Module.finrank_self]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  have harch : ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
        (fun v => max 1 (coeffSup v (P * Q)))).prod
      ≤ (N : ℝ) * ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
            (fun v => max 1 (coeffSup v P))).prod
          * ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
            (fun v => max 1 (coeffSup v Q))).prod := by
    rw [ha]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    exact max_one_le_of_mul_le_arch hN (coeffSup_nonneg a P) (coeffSup_nonneg a Q)
      (coeffSup_mul_le a P Q N hP)
  -- nonarchimedean places
  have hneP : (fun i : tP P => gP P i) ≠ 0 := gP_restrict_ne_zero P
  have hneQ : (fun i : tP Q => gP Q i) ≠ 0 := gP_restrict_ne_zero Q
  have hnePQ : (fun i : tP (P * Q) => gP (P * Q) i) ≠ 0 := gP_restrict_ne_zero (P * Q)
  have hfP : Function.HasFiniteMulSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ) =>
        (⨆ i : tP P, v.val (gP P i))) := by fun_prop
  have hfQ : Function.HasFiniteMulSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ) =>
        (⨆ i : tP Q, v.val (gP Q i))) := by fun_prop
  have hfPQ : Function.HasFiniteMulSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ) =>
        (⨆ i : tP (P * Q), v.val (gP (P * Q) i))) := by fun_prop
  have hnonarch : (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
        (⨆ i : tP (P * Q), v.val (gP (P * Q) i)))
      ≤ (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
            (⨆ i : tP P, v.val (gP P i)))
          * (∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
            (⨆ i : tP Q, v.val (gP Q i))) := by
    rw [← finprod_mul_distrib hfP hfQ]
    refine finprod_le_finprod hfPQ
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val (fun i : tP (P * Q) => gP (P * Q) i))
      (hfP.mul hfQ) (fun v => ?_)
    rw [iSup_gP_eq v.val (P * Q), iSup_gP_eq v.val P, iSup_gP_eq v.val Q]
    exact max_one_le_of_mul_le (coeffSup_nonneg v.val P) (coeffSup_nonneg v.val Q)
      (coeffSup_mul_le_of_nonarch v.val
        (Height.AdmissibleAbsValues.isNonarchimedean v.val v.prop) P Q)
  -- assemble the multiplicative inequality
  have hmain : Height.mulHeight (gP (P * Q))
      ≤ (N : ℝ) * Height.mulHeight (gP P) * Height.mulHeight (gP Q) := by
    set AQp : ℝ := ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
      (fun v => max 1 (coeffSup v (P * Q)))).prod with hAQp
    set AP : ℝ := ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
      (fun v => max 1 (coeffSup v P))).prod with hAP
    set AQ : ℝ := ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
      (fun v => max 1 (coeffSup v Q))).prod with hAQ
    set BQp : ℝ := ∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
      (⨆ i : tP (P * Q), v.val (gP (P * Q) i)) with hBQp
    set BP : ℝ := ∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
      (⨆ i : tP P, v.val (gP P i)) with hBP
    set BQ : ℝ := ∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
      (⨆ i : tP Q, v.val (gP Q i)) with hBQ
    have h1 : AQp ≤ (N : ℝ) * AP * AQ := by simpa only [hAQp, hAP, hAQ] using harch
    have h2 : BQp ≤ BP * BQ := by simpa only [hBQp, hBP, hBQ] using hnonarch
    have hAPnn : 0 ≤ AP := by
      rw [hAP]
      exact Multiset.prod_nonneg (fun b hb => by
        obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hb
        exact le_trans zero_le_one (le_max_left _ _))
    have hAQnn : 0 ≤ AQ := by
      rw [hAQ]
      exact Multiset.prod_nonneg (fun b hb => by
        obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hb
        exact le_trans zero_le_one (le_max_left _ _))
    have hBQpnn : 0 ≤ BQp := by
      rw [hBQp]
      exact finprod_nonneg (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
    calc Height.mulHeight (gP (P * Q))
        = AQp * BQp := by rw [mulHeight_gP_eq_prod (P * Q), hAQp, hBQp]
      _ ≤ ((N : ℝ) * AP * AQ) * (BP * BQ) :=
          mul_le_mul h1 h2 hBQpnn (mul_nonneg (mul_nonneg (le_of_lt hNpos) hAPnn) hAQnn)
      _ = (N : ℝ) * (AP * BP) * (AQ * BQ) := by ring
      _ = (N : ℝ) * Height.mulHeight (gP P) * Height.mulHeight (gP Q) := by
          rw [mulHeight_gP_eq_prod P, mulHeight_gP_eq_prod Q, hAP, hBP, hAQ, hBQ]
  -- take logarithms
  have hposPQ : 0 < Height.mulHeight (gP (P * Q)) := by
    rw [mulHeight_gP_eq (P * Q)]
    exact lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight (fun i : tP (P * Q) => gP (P * Q) i))
  have hposP : 0 < Height.mulHeight (gP P) := by
    rw [mulHeight_gP_eq P]
    exact lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight (fun i : tP P => gP P i))
  have hposQ : 0 < Height.mulHeight (gP Q) := by
    rw [mulHeight_gP_eq Q]
    exact lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight (fun i : tP Q => gP Q i))
  have hlog := Real.log_le_log hposPQ hmain
  rw [Real.log_mul (mul_ne_zero hNne hposP.ne') hposQ.ne',
    Real.log_mul hNne hposP.ne'] at hlog
  simp only [Height.logHeight_eq_log_mulHeight]
  linarith [hlog]

/-- The number of nonzero coefficients of a polynomial all of whose monomials are coordinatewise
bounded by `d` is at most `∏ j, (d j + 1)`. -/
lemma support_card_le_prod_succ {K : Type*} [CommSemiring K] (P : MvPolynomial σ K) (d : σ → ℕ)
    (hd : ∀ t ∈ P.support, ∀ j, t j ≤ d j) :
    P.support.card ≤ ∏ j, (d j + 1) := by
  classical
  have hinj : Function.Injective (fun t : ↥P.support =>
      fun j : σ => (⟨t.val j, Nat.lt_succ_of_le (hd t.val t.property j)⟩ : Fin (d j + 1))) := by
    intro t1 t2 h
    have h' : ∀ j, (t1.val : σ →₀ ℕ) j = t2.val j := by
      intro j
      have := congrFun h j
      exact Fin.ext_iff.mp this
    exact Subtype.ext (Finsupp.ext h')
  have hcard := Fintype.card_le_of_injective
    (fun t : ↥P.support =>
      fun j : σ => (⟨t.val j, Nat.lt_succ_of_le (hd t.val t.property j)⟩ : Fin (d j + 1))) hinj
  simpa [Fintype.card_coe] using hcard

lemma prod_succ_le_two_pow_sum (d : σ → ℕ) :
    ∏ j, (d j + 1) ≤ 2 ^ (∑ j, d j) := by
  calc ∏ j, (d j + 1) ≤ ∏ j, 2 ^ (d j) := by
        refine Finset.prod_le_prod (fun j _ => Nat.zero_le _) (fun j _ => ?_)
        exact Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := d j))
    _ = 2 ^ (∑ j, d j) := by rw [Finset.prod_pow_eq_pow_sum]

/-- For a nonzero polynomial whose monomials are coordinatewise bounded by `d`, the logarithm of
the number of its monomials is at most `(∑ j, d j) * log 2`. -/
lemma log_support_card_le (P : MvPolynomial σ ℚ) (d : σ → ℕ)
    (hP : P ≠ 0) (hd : ∀ t ∈ P.support, ∀ j, t j ≤ d j) :
    Real.log (P.support.card : ℝ) ≤ ((∑ j, d j : ℕ) : ℝ) * Real.log 2 := by
  have hpos : 0 < P.support.card := (MvPolynomial.support_nonempty.mpr hP).card_pos
  have hle : P.support.card ≤ 2 ^ (∑ j, d j) :=
    le_trans (support_card_le_prod_succ P d hd) (prod_succ_le_two_pow_sum d)
  have hle' : (P.support.card : ℝ) ≤ (2 : ℝ) ^ (∑ j, d j) := by exact_mod_cast hle
  calc Real.log (P.support.card : ℝ)
      ≤ Real.log ((2 : ℝ) ^ (∑ j, d j)) := Real.log_le_log (by exact_mod_cast hpos) hle'
    _ = ((∑ j, d j : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]

lemma mulHeight_gP_one : Height.mulHeight (gP (1 : MvPolynomial σ ℚ)) = 1 := by
  classical
  rw [mulHeight_gP_eq (1 : MvPolynomial σ ℚ)]
  have hconst : (fun i : tP (1 : MvPolynomial σ ℚ) => gP (1 : MvPolynomial σ ℚ) i)
      = (1 : tP (1 : MvPolynomial σ ℚ) → ℚ) := by
    funext i
    obtain ⟨o, ho⟩ := i
    cases o with
    | none => simp [gP]
    | some m =>
        have hm : m ∈ (1 : MvPolynomial σ ℚ).support := by
          rcases (mem_tP_iff (1 : MvPolynomial σ ℚ) (some m)).mp ho with h | ⟨m', hm', he⟩
          · exact absurd h (by simp)
          · exact (Option.some.inj he) ▸ hm'
        rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
        subst hm
        simp [gP, MvPolynomial.coeff_one]
  rw [hconst, Height.mulHeight_one]

lemma logHeight_gP_zero : Height.logHeight (gP (0 : MvPolynomial σ ℚ)) = 0 := by
  rw [Height.logHeight_eq_log_mulHeight]
  have hsupp : ∀ o : Option (σ →₀ ℕ), o ∉ ({none} : Finset (Option (σ →₀ ℕ))) →
      gP (0 : MvPolynomial σ ℚ) o = 0 := by
    intro o ho
    rw [Finset.mem_singleton] at ho
    obtain ⟨m, rfl⟩ := Option.ne_none_iff_exists'.mp ho
    simp [gP]
  rw [Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset
      ({none} : Finset (Option (σ →₀ ℕ))) hsupp,
    Height.mulHeight_eq_one_of_subsingleton, Real.log_one]

lemma logHeight_gP_nonneg (P : MvPolynomial σ ℚ) : 0 ≤ Height.logHeight (gP P) := by
  rw [Height.logHeight_eq_log_mulHeight, mulHeight_gP_eq P]
  exact Real.log_nonneg (Height.one_le_mulHeight (fun j : tP P => gP P j))

theorem polyHeight_finset_prod_le {σ ι : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (d : σ → ℕ)
    (hd : ∀ i, ∀ t ∈ (P i).support, ∀ j, t j ≤ d j) :
    Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP (∏ i, P i)) ≤
      (∑ i, Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP (P i)))
        + (((Fintype.card ι) * (∑ j, d j) + Fintype.card σ * (Fintype.card ι - 1) : ℕ) : ℝ)
          * Real.log 2 := by
  classical
  set B : ℝ := ((∑ j, d j : ℕ) : ℝ) * Real.log 2 with hB
  by_cases hsome : ∃ i, P i = 0
  · obtain ⟨i0, hi0⟩ := hsome
    have hprod : (∏ i, P i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i0) hi0
    rw [hprod, logHeight_gP_zero]
    have h2 : 0 ≤ (((Fintype.card ι) * (∑ j, d j)
        + Fintype.card σ * (Fintype.card ι - 1) : ℕ) : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => logHeight_gP_nonneg (P i))]
  · push Not at hsome
    have key : ∀ s : Finset ι, (∀ i ∈ s, P i ≠ 0) →
        Height.logHeight (gP (∏ i ∈ s, P i)) ≤
          (∑ i ∈ s, Height.logHeight (gP (P i))) + (s.card : ℝ) * B := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro _
          simp only [Finset.prod_empty, Finset.sum_empty, Finset.card_empty, Nat.cast_zero,
            zero_mul, add_zero]
          rw [Height.logHeight_eq_log_mulHeight, mulHeight_gP_one, Real.log_one]
      | insert a t ha ih =>
          intro hsne
          have ha0 : P a ≠ 0 := hsne a (Finset.mem_insert_self a t)
          have htne : ∀ i ∈ t, P i ≠ 0 := fun i hi => hsne i (Finset.mem_insert_of_mem hi)
          have hprod : (∏ i ∈ insert a t, P i) = P a * ∏ i ∈ t, P i := Finset.prod_insert ha
          rw [hprod]
          have hN : 1 ≤ (P a).support.card := (MvPolynomial.support_nonempty.mpr ha0).card_pos
          have hstep := polyHeight_mul_le_left (P a) (∏ i ∈ t, P i) ((P a).support.card) hN le_rfl
          have iht := ih htne
          have hlogcard := log_support_card_le (P a) d ha0 (hd a)
          calc Height.logHeight (gP (P a * ∏ i ∈ t, P i))
              ≤ Height.logHeight (gP (P a)) + Height.logHeight (gP (∏ i ∈ t, P i))
                  + Real.log ((P a).support.card : ℝ) := hstep
            _ ≤ Height.logHeight (gP (P a))
                  + ((∑ i ∈ t, Height.logHeight (gP (P i))) + (t.card : ℝ) * B)
                  + B := by linarith [iht, hlogcard]
            _ = (∑ i ∈ insert a t, Height.logHeight (gP (P i)))
                  + ((insert a t).card : ℝ) * B := by
                rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
                push_cast
                ring
    have hmain := key Finset.univ (fun i _ => hsome i)
    simp only [Finset.card_univ] at hmain
    have hbound : (Fintype.card ι : ℝ) * B
        ≤ (((Fintype.card ι) * (∑ j, d j)
            + Fintype.card σ * (Fintype.card ι - 1) : ℕ) : ℝ) * Real.log 2 := by
      rw [hB]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hle : (Fintype.card ι : ℝ) * (((∑ j, d j : ℕ) : ℝ))
          ≤ (((Fintype.card ι) * (∑ j, d j)
              + Fintype.card σ * (Fintype.card ι - 1) : ℕ) : ℝ) := by
        push_cast
        have hnn : (0 : ℝ) ≤ (Fintype.card σ : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) := by
          positivity
        linarith
      calc (Fintype.card ι : ℝ) * ((((∑ j, d j : ℕ) : ℝ)) * Real.log 2)
          = ((Fintype.card ι : ℝ) * (((∑ j, d j : ℕ) : ℝ))) * Real.log 2 := by ring
        _ ≤ ((((Fintype.card ι) * (∑ j, d j)
              + Fintype.card σ * (Fintype.card ι - 1) : ℕ) : ℝ)) * Real.log 2 :=
              mul_le_mul_of_nonneg_right hle hlog2
    linarith [hmain, hbound]

end Commons.NumberTheory.Height.MvPolynomial
