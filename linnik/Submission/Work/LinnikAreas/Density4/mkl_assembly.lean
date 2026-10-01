import Mathlib
import Submission.Work.LinnikAreas.Density4.mu_kappa_log_sum
import Submission.Work.LinnikAreas.Density4.ThetaPow.selTheta_asymptotic_pow
import Submission.Work.Commons.NumberTheory.Moebius.log_pow_bookkeeping

namespace Work.LinnikAreas.Density4

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary facts -/

/-- `κW(n) = ∏_{p | n} p/(p+1) = 1/∏_{p | n}(1 + 1/p)`. -/
lemma kappaW_eq_inv_prod (n : ℕ) :
    kappaW n = 1 / ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
  rw [kappaW, one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp2 : (0 : ℝ) < (p : ℝ) := by
    have := (Nat.mem_primeFactors.mp hp).1.two_le
    exact_mod_cast (by omega : 0 < p)
  have h1 : ((p : ℝ) + 1) ≠ 0 := by positivity
  have h0 : (p : ℝ) ≠ 0 := ne_of_gt hp2
  field_simp

/-- `∏_{p | t}(p+1)/p = ∏_{p | t}(1 + 1/p)`. -/
lemma prod_succ_div_eq_prod_one_add (t : ℕ) :
    (∏ p ∈ t.primeFactors, ((p : ℝ) + 1) / (p : ℝ))
      = ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℝ)) := by
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    have := (Nat.mem_primeFactors.mp hp).1.two_le
    have h : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    exact ne_of_gt h
  rw [add_div, div_self hp0]

/-- `1/√⌊Q⌋₊ ≤ √2/√Q` for `Q ≥ 1`. -/
lemma inv_sqrt_floor_le (Q : ℝ) (hQ : 1 ≤ Q) :
    (Real.sqrt (⌊Q⌋₊ : ℝ))⁻¹ ≤ Real.sqrt 2 * (Real.sqrt Q)⁻¹ := by
  have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa using hQ)
  have hQpos : 0 < Q := by linarith
  have hNpos : (0 : ℝ) < (⌊Q⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊Q⌋₊)
  have hlt : Q < ((⌊Q⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one Q
  have h2N : Q < 2 * (⌊Q⌋₊ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hN1
    linarith
  have hsq : Real.sqrt Q < Real.sqrt 2 * Real.sqrt (⌊Q⌋₊ : ℝ) := by
    have h := Real.sqrt_lt_sqrt (by linarith) h2N
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hQspos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have h1 : (Real.sqrt (⌊Q⌋₊ : ℝ))⁻¹ = 1 / Real.sqrt (⌊Q⌋₊ : ℝ) := inv_eq_one_div _
  have h2 : Real.sqrt 2 * (Real.sqrt Q)⁻¹ = Real.sqrt 2 / Real.sqrt Q := by
    rw [div_eq_mul_inv]
  rw [h1, h2, div_le_div_iff₀ (Real.sqrt_pos.mpr hNpos) hQspos]
  linarith [hsq]

/-! ## Assembly -/

/-- Assembly of the target estimate (for `A > 0`) from the real-`Q` reduction and the
weighted `Θ`-error bound. -/
lemma mkl_core (A : ℝ) (hA : 0 < A)
    (hred : ∀ (Q : ℝ) (t : ℕ), 1 ≤ Q →
      (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          (ArithmeticFunction.moebius n : ℝ) * kappaW n * Real.log (Q / (n : ℝ)) / (n : ℝ))
        = ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
            prodKappa d * selTheta (Q / (d : ℝ)) (d * t))
    (herr : ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (t : ℕ), 1 ≤ Q → 1 ≤ t →
      (∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d : ℝ))) ^ (-A))
        ≤ C * sHalf t * (Real.log (2 + Q)) ^ (-A)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
      |(∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
          (ArithmeticFunction.moebius n : ℝ)
            / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))
            * Real.log (Q / (n : ℝ)))
        - (∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ))) * (Real.pi ^ 2 / 6)|
        ≤ (C * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Real.log (2 + Q) ^ (-A) := by
  obtain ⟨Ce, hCe, herr'⟩ := herr
  obtain ⟨Cs, hCs, hsel⟩ := ThetaPow.selTheta_asymptotic_pow A hA
  obtain ⟨Cm, hCm, hmain⟩ := sqfree_coprime_recip_pm1_finite_self
  obtain ⟨⟨K1, hK1pos, hK1⟩, ⟨K2, hK2pos, hK2⟩, ⟨K3, hK3pos, hK3⟩⟩ :=
    Work.Commons.NumberTheory.Moebius.log_pow_bookkeeping A hA
  refine ⟨Cs * Ce + 2 * Real.sqrt 2 * Cm * K1 + 1, by positivity, ?_⟩
  intro Q r hQ hr
  have ht1 : 1 ≤ r := hr
  have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa using hQ)
  have hQpos : 0 < Q := by linarith
  have hlogpos : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
  have hLnn : 0 ≤ Real.log (2 + Q) ^ (-A) := Real.rpow_nonneg hlogpos.le _
  have hsHnn : 0 ≤ sHalf r := sHalf_nonneg r
  have htotpos : 0 < Nat.totient r := Nat.totient_pos.mpr (by omega)
  -- (1) rewrite the summand `μ(n)/(n ∏(1+1/p))` into the `κW` shape
  have hS_eq : (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
          (ArithmeticFunction.moebius n : ℝ)
            / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))
            * Real.log (Q / (n : ℝ)))
      = ∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
          (ArithmeticFunction.moebius n : ℝ) * kappaW n * Real.log (Q / (n : ℝ)) / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_filter] at hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn.1).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hPne : (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have hp2 : (0 : ℝ) < (p : ℝ) := by
        have := (Nat.mem_primeFactors.mp hp).1.two_le
        exact_mod_cast (by omega : 0 < p)
      positivity
    rw [kappaW_eq_inv_prod n, one_div]
    field_simp
  -- (2) set up the reduction and the main/error split
  set E : Finset ℕ := (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d r) with hE
  set Sel : ℝ := ∑ d ∈ E, prodKappa d * selTheta (Q / (d : ℝ)) (d * r) with hSel
  set Ap : ℝ := ∑ d ∈ E, prodKappa d * (((d * r : ℕ)) : ℝ) / (Nat.totient (d * r) : ℝ) with hAp
  set Psum : ℝ := ∑ d ∈ E, ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) ^ 2 - 1) with hPsum
  set mainT : ℝ := (∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ))) * (Real.pi ^ 2 / 6) with hmainT
  set mainA : ℝ := ((r : ℝ) / (Nat.totient r : ℝ))
      * ((Real.pi ^ 2 / 6) * ∏ p ∈ r.primeFactors, (1 - (1 : ℝ) / (p : ℝ) ^ 2)) with hmainA
  have hSel_eq : (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) * kappaW n * Real.log (Q / (n : ℝ)) / (n : ℝ))
      = Sel := by
    rw [hSel, hE]
    exact hred Q r hQ
  rw [hS_eq, hSel_eq]
  -- (3) `mainT` is the closed form of the main term
  have hmainT_eq : mainA = mainT := by
    rw [hmainA, hmainT, main_const r ht1, prod_succ_div_eq_prod_one_add r]
    ring
  -- (4) the termwise main term `Ap` is `(r/φ r)·Psum`
  have hAp_eq : Ap = ((r : ℝ) / (Nat.totient r : ℝ)) * Psum := by
    rw [hAp, hPsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hE, Finset.mem_filter] at hd
    obtain ⟨hdIcc, hdsq, hdcop⟩ := hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    rw [main_term_d d r hd1 ht1 hdcop hdsq]
    ring
  -- (5) error term
  have hSel_Ap : |Sel - Ap| ≤ Cs * Ce * sHalf r * Real.log (2 + Q) ^ (-A) := by
    rw [hSel, hAp, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∀ d ∈ E,
        |prodKappa d * selTheta (Q / (d : ℝ)) (d * r)
            - prodKappa d * (((d * r : ℕ)) : ℝ) / (Nat.totient (d * r) : ℝ)|
        ≤ prodKappa d * (Cs * sHalf (d * r) * Real.log (2 + Q / (d : ℝ)) ^ (-A)) := by
      intro d hd
      rw [hE, Finset.mem_filter] at hd
      obtain ⟨hdIcc, hdsq, hdcop⟩ := hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
      have hdN : d ≤ ⌊Q⌋₊ := (Finset.mem_Icc.mp hdIcc).2
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hdleQ : (d : ℝ) ≤ Q := by
        have h1 : ((d : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hdN
        have h2 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
        linarith
      have hQd : 1 ≤ Q / (d : ℝ) := by
        rw [le_div_iff₀ hdpos]; linarith
      have hdr1 : 1 ≤ d * r := Nat.mul_pos (by omega) (by omega)
      have hb := hsel (Q / (d : ℝ)) hQd (d * r) hdr1
      have hb' : |selTheta (Q / (d : ℝ)) (d * r)
            - ((d * r : ℕ) : ℝ) / (Nat.totient (d * r) : ℝ)|
          ≤ (Cs * sHalf (d * r)) * Real.log (2 + Q / (d : ℝ)) ^ (-A) := by
        simpa [sHalf] using hb
      rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (prodKappa_nonneg d)]
      exact mul_le_mul_of_nonneg_left hb' (prodKappa_nonneg d)
    calc (∑ d ∈ E,
            |prodKappa d * selTheta (Q / (d : ℝ)) (d * r)
              - prodKappa d * (((d * r : ℕ)) : ℝ) / (Nat.totient (d * r) : ℝ)|)
        ≤ ∑ d ∈ E,
            prodKappa d * (Cs * sHalf (d * r) * Real.log (2 + Q / (d : ℝ)) ^ (-A)) :=
          Finset.sum_le_sum hstep
      _ = Cs * ∑ d ∈ E, prodKappa d * sHalf (d * r) * Real.log (2 + Q / (d : ℝ)) ^ (-A) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
      _ ≤ Cs * (Ce * sHalf r * Real.log (2 + Q) ^ (-A)) :=
          mul_le_mul_of_nonneg_left (by simpa [hE] using herr' Q r hQ ht1) hCs.le
      _ = Cs * Ce * sHalf r * Real.log (2 + Q) ^ (-A) := by ring
  -- (6) main term error
  have hAp_main : |Ap - mainA| ≤ (2 * Real.sqrt 2 * Cm * K1) * sHalf r * Real.log (2 + Q) ^ (-A) := by
    have hrφnn : 0 ≤ (r : ℝ) / (Nat.totient r : ℝ) := by positivity
    have hP := hmain ⌊Q⌋₊ r hN1 ht1
    have h1 : |Ap - mainA| ≤ Cm / Real.sqrt (⌊Q⌋₊ : ℝ) * ((r : ℝ) / (Nat.totient r : ℝ)) := by
      rw [hAp_eq, hmainA, ← mul_sub, abs_mul, abs_of_nonneg hrφnn]
      calc ((r : ℝ) / (Nat.totient r : ℝ))
            * |Psum - (Real.pi ^ 2 / 6) * ∏ p ∈ r.primeFactors, (1 - (1 : ℝ) / (p : ℝ) ^ 2)|
          ≤ ((r : ℝ) / (Nat.totient r : ℝ)) * (Cm / Real.sqrt (⌊Q⌋₊ : ℝ)) :=
            mul_le_mul_of_nonneg_left hP hrφnn
        _ = Cm / Real.sqrt (⌊Q⌋₊ : ℝ) * ((r : ℝ) / (Nat.totient r : ℝ)) := by ring
    refine h1.trans ?_
    have hratio := totient_ratio_le_two_sHalf r ht1
    have hinv := inv_sqrt_floor_le Q hQ
    have h2 : Cm / Real.sqrt (⌊Q⌋₊ : ℝ) ≤ Cm * (Real.sqrt 2 * (Real.sqrt Q)⁻¹) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hCm.le
    have hK1' := hK1 Q hQ
    calc Cm / Real.sqrt (⌊Q⌋₊ : ℝ) * ((r : ℝ) / (Nat.totient r : ℝ))
        ≤ (Cm * (Real.sqrt 2 * (Real.sqrt Q)⁻¹)) * (2 * sHalf r) :=
          mul_le_mul h2 hratio (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * Cm * (sHalf r * (Real.sqrt Q)⁻¹) := by ring
      _ ≤ 2 * Real.sqrt 2 * Cm * (sHalf r * (K1 * Real.log (2 + Q) ^ (-A))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK1' hsHnn) (by positivity)
      _ = 2 * Real.sqrt 2 * Cm * K1 * sHalf r * Real.log (2 + Q) ^ (-A) := by ring
  -- (7) combine
  have hsplit : |Sel - mainT| ≤ |Sel - Ap| + |Ap - mainA| := by
    have h1 : Sel - mainT = (Sel - Ap) + (Ap - mainA) := by rw [hmainT_eq]; ring
    rw [h1]
    exact abs_add_le _ _
  have hcomb : |Sel - Ap| + |Ap - mainA|
      ≤ (Cs * Ce + 2 * Real.sqrt 2 * Cm * K1) * sHalf r * Real.log (2 + Q) ^ (-A) := by
    refine (add_le_add hSel_Ap hAp_main).trans ?_
    have h1 : Cs * Ce * sHalf r * Real.log (2 + Q) ^ (-A)
          + (2 * Real.sqrt 2 * Cm * K1) * sHalf r * Real.log (2 + Q) ^ (-A)
        = (Cs * Ce + 2 * Real.sqrt 2 * Cm * K1) * sHalf r * Real.log (2 + Q) ^ (-A) := by ring
    rw [h1]
  refine (hsplit.trans hcomb).trans ?_
  have h2 : (Cs * Ce + 2 * Real.sqrt 2 * Cm * K1) * sHalf r * Real.log (2 + Q) ^ (-A)
      ≤ (Cs * Ce + 2 * Real.sqrt 2 * Cm * K1 + 1) * sHalf r * Real.log (2 + Q) ^ (-A) := by
    have h3 : 0 ≤ sHalf r * Real.log (2 + Q) ^ (-A) := mul_nonneg hsHnn hLnn
    nlinarith
  exact h2

end

end Work.LinnikAreas.Density4
