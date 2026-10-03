import Mathlib

namespace Work.KMTAreas.A8

open scoped BigOperators

/-- **Finite `ℓ^r` duality (norm attainment).**  For every `r ≥ 1` and every finite complex
vector `v`, there is a coefficient vector `c` in the dual unit ball of `ℓ^r` which attains the
norm of `v`:

  `∑ᵢ vᵢ cᵢ = ‖v‖_r`  and  `|∑ᵢ xᵢ cᵢ| ≤ ‖x‖_r` for every `x`.

The witness is the explicit Hölder-dual vector `cᵢ = conj vᵢ · ‖vᵢ‖^{r-2} / ‖v‖_r^{r-1}`. -/
theorem exists_dual_lp {ι : Type*} [Fintype ι] (r : NNReal) (hr : 1 ≤ r) (v : ι → ℂ) :
    ∃ c : ι → ℂ,
      (∑ i, v i * c i = (((∑ i, ‖v i‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)) : ℝ) : ℂ)) ∧
      (∀ x : ι → ℂ, ‖∑ i, x i * c i‖ ≤ ((∑ i, ‖x i‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)) : ℝ)) := by
  set p : ℝ := (r : ℝ) with hpdef
  have hp1 : 1 ≤ p := by rw [hpdef]; exact_mod_cast hr
  have hp0 : p ≠ 0 := by linarith
  set S : ℝ := ∑ i, ‖v i‖ ^ p with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  set N : ℝ := S ^ (1 / p) with hNdef
  have hNnn : 0 ≤ N := by rw [hNdef]; exact Real.rpow_nonneg hSnn _
  have hNp : N ^ p = S := by
    rw [hNdef, ← Real.rpow_mul hSnn (1 / p) p, one_div_mul_cancel hp0, Real.rpow_one]
  have hdiv : S / N ^ (p - 1) = N := by
    by_cases hN : N = 0
    · have hS0 : S = 0 := by rw [← hNp, hN, Real.zero_rpow hp0]
      rw [hS0, hN]; simp
    · have hNpos : 0 < N := lt_of_le_of_ne hNnn (Ne.symm hN)
      have hNm : N ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNpos (p - 1))
      have h1 : N ^ (p - 1) * N = S := by
        rw [← Real.rpow_add_one' hNnn (h := by rw [show p - 1 + 1 = p by ring]; exact hp0)]
        rw [show p - 1 + 1 = p by ring, hNp]
      rw [div_eq_iff hNm, mul_comm, h1]
  refine ⟨fun i => star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) / ((N ^ (p - 1) : ℝ) : ℂ),
    ?_, ?_⟩
  · -- condition (1): the functional `c` attains the norm of `v`
    have hterm : ∀ i,
        v i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ)) = ((‖v i‖ ^ p : ℝ) : ℂ) := by
      intro i
      have hmc : v i * star (v i) = ((Complex.normSq (v i) : ℝ) : ℂ) := by
        simpa using Complex.mul_conj (v i)
      have hreal : Complex.normSq (v i) * (‖v i‖ ^ (p - 2)) = ‖v i‖ ^ p := by
        rw [Complex.normSq_eq_norm_sq, ← Real.rpow_two,
          ← Real.rpow_add' (norm_nonneg (v i))
            (h := by rw [show (2 : ℝ) + (p - 2) = p by ring]; exact hp0)]
        rw [show (2 : ℝ) + (p - 2) = p by ring]
      rw [← mul_assoc, hmc, ← Complex.ofReal_mul, hreal]
    calc ∑ i, v i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) / ((N ^ (p - 1) : ℝ) : ℂ))
        = ∑ i, (v i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ))) /
            ((N ^ (p - 1) : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun i _ => by rw [← mul_div_assoc]
      _ = (∑ i, v i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ))) /
            ((N ^ (p - 1) : ℝ) : ℂ) := by
          rw [Finset.sum_div]
      _ = (∑ i, ((‖v i‖ ^ p : ℝ) : ℂ)) / ((N ^ (p - 1) : ℝ) : ℂ) := by
          rw [Finset.sum_congr rfl fun i _ => hterm i]
      _ = ((S : ℝ) : ℂ) / ((N ^ (p - 1) : ℝ) : ℂ) := by
          rw [hSdef, Complex.ofReal_sum]
      _ = ((S / N ^ (p - 1) : ℝ) : ℂ) := by rw [Complex.ofReal_div]
      _ = (N : ℂ) := by rw [hdiv]
  · -- condition (2): `c` lies in the dual unit ball
    intro x
    have hcs : ‖∑ i, x i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
          ((N ^ (p - 1) : ℝ) : ℂ))‖
        ≤ ∑ i, ‖x i‖ * ‖star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
            ((N ^ (p - 1) : ℝ) : ℂ)‖ :=
      (norm_sum_le Finset.univ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _)
    by_cases hpone : p = 1
    · -- the case `p = 1` (dual exponent `∞`): `‖cᵢ‖ ≤ 1`
      have hle : ∀ i, ‖star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
            ((N ^ (p - 1) : ℝ) : ℂ)‖ ≤ 1 := by
        intro i
        have hX : (‖v i‖ ^ (p - 2) : ℝ) = ‖v i‖⁻¹ := by
          rw [hpone, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
        have hK : (N ^ (p - 1) : ℝ) = 1 := by
          rw [hpone, show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero]
        rw [norm_div, norm_mul, norm_star, hX, hK, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          abs_one, div_one]
        rcases eq_or_lt_of_le (norm_nonneg (v i)) with h | h
        · rw [← h, zero_mul]; norm_num
        · rw [mul_inv_cancel₀ (ne_of_gt h)]
      calc ‖∑ i, x i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
            ((N ^ (p - 1) : ℝ) : ℂ))‖
          ≤ ∑ i, ‖x i‖ * ‖star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
              ((N ^ (p - 1) : ℝ) : ℂ)‖ := hcs
        _ ≤ ∑ i, ‖x i‖ * 1 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (norm_nonneg _)
        _ = ((∑ i, ‖x i‖ ^ p) ^ (1 / p) : ℝ) := by
              rw [hpone]; simp [Real.rpow_one]
    · -- the case `p > 1`: Hölder with the conjugate exponent `p/(p-1)`
      have hplt : 1 < p := lt_of_le_of_ne hp1 (Ne.symm hpone)
      have hpq := Real.HolderConjugate.conjExponent hplt
      have hnc : ∀ i, ‖star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
            ((N ^ (p - 1) : ℝ) : ℂ)‖ = ‖v i‖ ^ (p - 1) / N ^ (p - 1) := by
        intro i
        rw [norm_div, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (v i)) _),
          abs_of_nonneg (Real.rpow_nonneg hNnn _)]
        congr 1
        nth_rewrite 1 [← Real.rpow_one ‖v i‖]
        rw [← Real.rpow_add' (norm_nonneg (v i))
          (h := by rw [show (1 : ℝ) + (p - 2) = p - 1 by ring]; intro hh; linarith)]
        rw [show (1 : ℝ) + (p - 2) = p - 1 by ring]
      have h1 : (∑ i, (‖v i‖ ^ (p - 1)) ^ (p.conjExponent)) = S := by
        rw [hSdef]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Real.rpow_mul (norm_nonneg (v i)) (p - 1) (p.conjExponent),
          hpq.sub_one_mul_conj]
      have h2 : S ^ (1 / p.conjExponent) = N ^ (p - 1) := by
        have hq1 : 1 / p.conjExponent = (p - 1) / p := by
          rw [hpq.conjugate_eq, one_div_div]
        rw [hq1, show (p - 1) / p = (1 / p) * (p - 1) by ring,
          Real.rpow_mul hSnn (1 / p) (p - 1), ← hNdef]
      have hHolder : ∑ i, ‖x i‖ * ‖v i‖ ^ (p - 1)
          ≤ (∑ i, ‖x i‖ ^ p) ^ (1 / p) * N ^ (p - 1) := by
        refine (Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq
          (fun i _ => norm_nonneg (x i))
          (fun i _ => Real.rpow_nonneg (norm_nonneg (v i)) _)).trans ?_
        rw [h1, h2]
      calc ‖∑ i, x i * (star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
            ((N ^ (p - 1) : ℝ) : ℂ))‖
          ≤ ∑ i, ‖x i‖ * ‖star (v i) * ((‖v i‖ ^ (p - 2) : ℝ) : ℂ) /
              ((N ^ (p - 1) : ℝ) : ℂ)‖ := hcs
        _ = ∑ i, ‖x i‖ * (‖v i‖ ^ (p - 1) / N ^ (p - 1)) :=
              Finset.sum_congr rfl fun i _ => by rw [hnc i]
        _ = (∑ i, ‖x i‖ * ‖v i‖ ^ (p - 1)) / N ^ (p - 1) := by
              simp only [← mul_div_assoc, Finset.sum_div]
        _ ≤ (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
              by_cases hN1 : N ^ (p - 1) = 0
              · rw [hN1, div_zero]
                exact Real.rpow_nonneg
                  (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
              · rw [div_le_iff₀ (lt_of_le_of_ne (Real.rpow_nonneg hNnn _) (Ne.symm hN1))]
                exact hHolder

end Work.KMTAreas.A8
