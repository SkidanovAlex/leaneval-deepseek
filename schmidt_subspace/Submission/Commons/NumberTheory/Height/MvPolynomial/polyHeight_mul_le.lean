import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.FunLike.Fintype
import Mathlib.NumberTheory.Height.NumberField
import Submission.Commons.Algebra.MvPolynomial.coeff_mul_eq_sum_support
import Submission.Commons.NumberTheory.Height.mulHeight_finsupp_coe_eq

namespace Commons.NumberTheory.Height.MvPolynomial

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {σ : Type*} [Fintype σ]

/-- The supremum of `v` over all coefficients of `P`. -/
noncomputable def coeffSup (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) : ℝ :=
  ⨆ m : σ →₀ ℕ, v (MvPolynomial.coeff m P)

lemma bddAbove_range_coeff (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) :
    BddAbove (Set.range fun m : σ →₀ ℕ => v (MvPolynomial.coeff m P)) := by
  classical
  refine ⟨Finset.sup' (insert 0 P.support) (Finset.insert_nonempty 0 _)
    ((fun p => v (MvPolynomial.coeff p P)) : (σ →₀ ℕ) → ℝ), ?_⟩
  rintro y ⟨m, rfl⟩
  by_cases hm : m ∈ P.support
  · exact Finset.le_sup' (fun p => v (MvPolynomial.coeff p P)) (Finset.mem_insert_of_mem hm)
  · change v (MvPolynomial.coeff m P) ≤ _
    rw [MvPolynomial.notMem_support_iff.mp hm, AbsoluteValue.map_zero]
    exact le_trans (v.nonneg _)
      (Finset.le_sup' (fun p => v (MvPolynomial.coeff p P)) (Finset.mem_insert_self 0 _))

lemma le_coeffSup (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    v (MvPolynomial.coeff m P) ≤ coeffSup v P :=
  le_ciSup (bddAbove_range_coeff v P) m

lemma coeffSup_nonneg (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) : 0 ≤ coeffSup v P :=
  Real.iSup_nonneg_of_nonnegHomClass v (fun m => MvPolynomial.coeff m P)

lemma coeffSup_mul_le (v : AbsoluteValue ℚ ℝ) (P Q : MvPolynomial σ ℚ) (N : ℕ)
    (hP : P.support.card ≤ N) :
    coeffSup v (P * Q) ≤ (N : ℝ) * coeffSup v P * coeffSup v Q := by
  classical
  haveI : Nonempty (σ →₀ ℕ) := ⟨0⟩
  refine ciSup_le (fun m => ?_)
  rw [Commons.Algebra.MvPolynomial.coeff_mul_eq_sum_support P Q m]
  calc v (∑ p ∈ P.support, MvPolynomial.coeff p P *
        (if p ≤ m then MvPolynomial.coeff (m - p) Q else 0))
      ≤ ∑ p ∈ P.support, v (MvPolynomial.coeff p P *
          (if p ≤ m then MvPolynomial.coeff (m - p) Q else 0)) :=
        v.sum_le _ _
    _ ≤ ∑ p ∈ P.support, coeffSup v P * coeffSup v Q := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [AbsoluteValue.map_mul]
        refine mul_le_mul (le_coeffSup v P p) ?_ (v.nonneg _) (coeffSup_nonneg v P)
        by_cases h : p ≤ m
        · rw [if_pos h]; exact le_coeffSup v Q (m - p)
        · rw [if_neg h, AbsoluteValue.map_zero]; exact coeffSup_nonneg v Q
    _ = (P.support.card : ℝ) * (coeffSup v P * coeffSup v Q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (coeffSup v P * coeffSup v Q) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hP)
          (mul_nonneg (coeffSup_nonneg v P) (coeffSup_nonneg v Q))
    _ = (N : ℝ) * coeffSup v P * coeffSup v Q := by ring

lemma coeffSup_mul_le_of_nonarch (v : AbsoluteValue ℚ ℝ) (hv : IsNonarchimedean v)
    (P Q : MvPolynomial σ ℚ) :
    coeffSup v (P * Q) ≤ coeffSup v P * coeffSup v Q := by
  classical
  haveI : Nonempty (σ →₀ ℕ) := ⟨0⟩
  refine ciSup_le (fun m => ?_)
  rw [MvPolynomial.coeff_mul]
  refine le_trans (hv.apply_sum_le (s := Finset.HasAntidiagonal.antidiagonal m)) ?_
  haveI : Nonempty ↑(Finset.HasAntidiagonal.antidiagonal m) :=
    ⟨⟨(m, 0), by rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp⟩⟩
  refine ciSup_le (fun x => ?_)
  rw [AbsoluteValue.map_mul]
  exact mul_le_mul (le_coeffSup v P (x : (σ →₀ ℕ) × (σ →₀ ℕ)).1)
    (le_coeffSup v Q (x : (σ →₀ ℕ) × (σ →₀ ℕ)).2) (v.nonneg _) (coeffSup_nonneg v P)

/-! ### The "projective" coefficient tuple `(1, coeffs P)` -/

/-- The coefficient tuple of `P` with an extra constant `1` (indexed by `Option`). -/
noncomputable def gP (P : MvPolynomial σ ℚ) : Option (σ →₀ ℕ) → ℚ :=
  fun o => o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m P)

/-- A finite index set containing the support of `gP P`. -/
noncomputable def tP (P : MvPolynomial σ ℚ) : Finset (Option (σ →₀ ℕ)) :=
  insert none (P.support.image some)

lemma mem_tP_iff (P : MvPolynomial σ ℚ) (o : Option (σ →₀ ℕ)) :
    o ∈ tP P ↔ o = none ∨ ∃ m ∈ P.support, some m = o := by
  rw [tP, Finset.mem_insert, Finset.mem_image]

lemma mem_tP_none (P : MvPolynomial σ ℚ) : (none : Option (σ →₀ ℕ)) ∈ tP P :=
  (mem_tP_iff P none).mpr (Or.inl rfl)

lemma mem_tP_some (P : MvPolynomial σ ℚ) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    (some m) ∈ tP P :=
  (mem_tP_iff P (some m)).mpr (Or.inr ⟨m, hm, rfl⟩)

lemma gP_notMem (P : MvPolynomial σ ℚ) {o : Option (σ →₀ ℕ)} (ho : o ∉ tP P) :
    gP P o = 0 := by
  cases o with
  | none => exact absurd (mem_tP_none P) ho
  | some m =>
    have hm : m ∉ P.support := fun hm => ho (mem_tP_some P hm)
    exact MvPolynomial.notMem_support_iff.mp hm

lemma gP_restrict_ne_zero (P : MvPolynomial σ ℚ) : (fun i : tP P => gP P i) ≠ 0 := by
  intro h
  have := congrFun h ⟨none, mem_tP_none P⟩
  simp only [gP, Option.elim_none, Pi.zero_apply] at this
  exact one_ne_zero this

lemma iSup_gP_eq (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) :
    (⨆ i : tP P, v (gP P i)) = max 1 (coeffSup v P) := by
  classical
  haveI : Nonempty ↑(tP P) := ⟨⟨none, mem_tP_none P⟩⟩
  apply le_antisymm
  · refine ciSup_le (fun i => ?_)
    rcases (mem_tP_iff P i.val).mp i.2 with h | ⟨m, hm, hmi⟩
    · have : gP P i = 1 := by simp only [gP, h, Option.elim_none]
      rw [this, AbsoluteValue.map_one]
      exact le_max_left _ _
    · have : gP P i = MvPolynomial.coeff m P := by
        simp only [gP]
        rw [← hmi, Option.elim_some]
      rw [this]
      exact le_max_of_le_right (le_coeffSup v P m)
  · refine max_le ?_ ?_
    · have h := Finite.le_ciSup (fun i : tP P => v (gP P i)) ⟨none, mem_tP_none P⟩
      simpa only [gP, Option.elim_none, AbsoluteValue.map_one] using h
    · haveI : Nonempty (σ →₀ ℕ) := ⟨0⟩
      refine ciSup_le (fun m => ?_)
      by_cases hm : m ∈ P.support
      · have h := Finite.le_ciSup (fun i : tP P => v (gP P i))
          (⟨some m, mem_tP_some P hm⟩ : tP P)
        have hgi : gP P (⟨some m, mem_tP_some P hm⟩ : tP P) = MvPolynomial.coeff m P := by
          simp only [gP, Option.elim_some]
        rwa [hgi] at h
      · rw [MvPolynomial.notMem_support_iff.mp hm, AbsoluteValue.map_zero]
        exact Real.iSup_nonneg_of_nonnegHomClass v (fun i : tP P => gP P i)

lemma mulHeight_gP_eq (P : MvPolynomial σ ℚ) :
    Height.mulHeight (gP P) = Height.mulHeight (fun i : tP P => gP P i) :=
  Height.mulHeight_eq_mulHeight_finset (tP P) (fun o ho => gP_notMem P ho)

lemma mulHeight_gP_eq_prod (P : MvPolynomial σ ℚ) :
    Height.mulHeight (gP P)
      = ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
            (fun v => max 1 (coeffSup v P))).prod
        * ∏ᶠ (v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ)),
            (⨆ i : tP P, v.val (gP P i)) := by
  rw [mulHeight_gP_eq P, Height.mulHeight_eq (gP_restrict_ne_zero P)]
  rw [show (fun v : AbsoluteValue ℚ ℝ => ⨆ i : tP P, v (gP P i))
      = (fun v => max 1 (coeffSup v P)) from funext (fun v => iSup_gP_eq v P)]

/-! ### Elementary arithmetic -/

lemma max_one_le_of_mul_le {a x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : a ≤ x * y) :
    max 1 a ≤ max 1 x * max 1 y := by
  have hx1 : 1 ≤ max 1 x := le_max_left _ _
  have hy1 : 1 ≤ max 1 y := le_max_left _ _
  refine max_le ?_ (le_trans h ?_)
  · calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ max 1 x * max 1 y := mul_le_mul hx1 hy1 zero_le_one (le_trans zero_le_one hx1)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hy (le_trans zero_le_one hx1)

lemma max_one_le_of_mul_le_arch {a x y : ℝ} {N : ℕ} (hN : 1 ≤ N) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : a ≤ (N : ℝ) * x * y) : max 1 a ≤ (N : ℝ) * max 1 x * max 1 y := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx1 : 1 ≤ max 1 x := le_max_left _ _
  have hy1 : 1 ≤ max 1 y := le_max_left _ _
  have hmx0 : 0 ≤ max 1 x := le_trans zero_le_one hx1
  have hprod : (N : ℝ) * x * y ≤ (N : ℝ) * max 1 x * max 1 y := by
    have h1 : (N : ℝ) * x ≤ (N : ℝ) * max 1 x :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hN0
    have h2 : (N : ℝ) * x * y ≤ (N : ℝ) * max 1 x * y :=
      mul_le_mul_of_nonneg_right h1 hy
    have h3 : (N : ℝ) * max 1 x * y ≤ (N : ℝ) * max 1 x * max 1 y :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hN0 hmx0)
    exact le_trans h2 h3
  refine max_le ?_ (le_trans h hprod)
  · calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ (N : ℝ) * max 1 x * max 1 y :=
          mul_le_mul (mul_le_mul hN1 hx1 zero_le_one hN0) hy1 zero_le_one
            (mul_nonneg hN0 hmx0)

theorem polyHeight_mul_le {σ : Type*} [Fintype σ] (P Q : MvPolynomial σ ℚ) (N : ℕ)
    (hN : 1 ≤ N) (hP : P.support.card ≤ N) (hQ : Q.support.card ≤ N) :
    Height.logHeight (fun o : Option (σ →₀ ℕ) =>
        o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m (P * Q))) ≤
      Height.logHeight (fun o : Option (σ →₀ ℕ) =>
        o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m P)) +
      Height.logHeight (fun o : Option (σ →₀ ℕ) =>
        o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m Q)) + Real.log N := by
  classical
  change Height.logHeight (gP (P * Q)) ≤
    Height.logHeight (gP P) + Height.logHeight (gP Q) + Real.log N
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

end Commons.NumberTheory.Height.MvPolynomial