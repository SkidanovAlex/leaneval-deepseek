import Mathlib

namespace Work.FIArea5.S16Hecke

/-- Key algebraic inequality: for `T ≥ 3` and `0 ≤ α ≤ 3/2` one has
`α (2a + α) / (T² + a²) ≤ 2α/T` for every real `a`. -/
lemma alphaSq_div_le (T a α : ℝ) (hT : 3 ≤ T) (hα0 : 0 ≤ α) (hα2 : α ≤ 3 / 2) :
    α * (2 * a + α) / (T ^ 2 + a ^ 2) ≤ 2 * (α / T) := by
  have hden : 0 < T ^ 2 + a ^ 2 := by positivity
  have hTpos : 0 < T := by linarith
  have hh : 2 * (α / T) = 2 * α / T := by ring
  rw [hh, div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hTpos]
  nlinarith [sq_nonneg (a - T / 2), mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ 3 * T / 2 - α)]

/-- Logarithmic bound for a single ratio: for `T ≥ 3` and `0 ≤ α ≤ 3/2`,
`-(α/T) ≤ (1/2)·(log (T²+a²) - log (T²+(a+α)²))`. -/
lemma half_log_sub_le (T a α : ℝ) (hT : 3 ≤ T) (hα0 : 0 ≤ α) (hα2 : α ≤ 3 / 2) :
    -(α / T) ≤ (1 / 2) * (Real.log (T ^ 2 + a ^ 2) - Real.log (T ^ 2 + (a + α) ^ 2)) := by
  have hApos : 0 < T ^ 2 + a ^ 2 := by positivity
  have hBpos : 0 < T ^ 2 + (a + α) ^ 2 := by positivity
  have hTpos : 0 < T := by linarith
  have hlog : Real.log ((T ^ 2 + (a + α) ^ 2) / (T ^ 2 + a ^ 2)) ≤
      (T ^ 2 + (a + α) ^ 2) / (T ^ 2 + a ^ 2) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hdiv : Real.log ((T ^ 2 + (a + α) ^ 2) / (T ^ 2 + a ^ 2)) =
      Real.log (T ^ 2 + (a + α) ^ 2) - Real.log (T ^ 2 + a ^ 2) :=
    Real.log_div (ne_of_gt hBpos) (ne_of_gt hApos)
  have hkey := alphaSq_div_le T a α hT hα0 hα2
  have hfrac : (T ^ 2 + (a + α) ^ 2) / (T ^ 2 + a ^ 2) - 1 =
      α * (2 * a + α) / (T ^ 2 + a ^ 2) := by
    field_simp
    ring
  rw [hfrac] at hlog
  have hlogB : Real.log ((T ^ 2 + (a + α) ^ 2) / (T ^ 2 + a ^ 2)) ≤ 2 * (α / T) :=
    le_trans hlog hkey
  have hrewrite : (1 / 2) * (Real.log (T ^ 2 + a ^ 2) - Real.log (T ^ 2 + (a + α) ^ 2)) =
      -(1 / 2) * Real.log ((T ^ 2 + (a + α) ^ 2) / (T ^ 2 + a ^ 2)) := by
    rw [hdiv]; ring
  rw [hrewrite]
  linarith

/-- Each factor of the product is bounded below by `(j+1/2)/(j+2)`
(valid for `0 ≤ T` and `1/2 ≤ α ≤ 3/2`). -/
lemma term_ge_linear (α T : ℝ) (hα1 : 1 / 2 ≤ α) (hα2 : α ≤ 3 / 2) (j : ℕ) :
    ((j : ℝ) + 1 / 2) / ((j : ℝ) + 2) ≤
      Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) := by
  have ha0 : 0 < (j : ℝ) + 1 / 2 := by positivity
  have hb0 : 0 < (j : ℝ) + α + 1 / 2 := by linarith [hα1]
  have hb2 : 0 < ((j : ℝ) + α + 1 / 2) ^ 2 := by positivity
  have hB : 0 < T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2 := by positivity
  have hcross : ((j : ℝ) + 1 / 2) ^ 2 * (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2) ≤
      (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) * ((j : ℝ) + α + 1 / 2) ^ 2 := by
    have ha2b2 : ((j : ℝ) + 1 / 2) ^ 2 ≤ ((j : ℝ) + α + 1 / 2) ^ 2 := by nlinarith [ha0, hα1]
    nlinarith [sq_nonneg T, ha2b2, mul_nonneg (sq_nonneg T) (sub_nonneg.mpr ha2b2)]
  have hsq : (((j : ℝ) + 1 / 2) / ((j : ℝ) + α + 1 / 2)) ^ 2 ≤
      (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2) := by
    rw [div_pow, div_le_iff₀ hb2, div_mul_eq_mul_div, le_div_iff₀ hB]
    exact hcross
  have step1 : ((j : ℝ) + 1 / 2) / ((j : ℝ) + α + 1 / 2) ≤
      Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) := by
    calc ((j : ℝ) + 1 / 2) / ((j : ℝ) + α + 1 / 2)
        = Real.sqrt ((((j : ℝ) + 1 / 2) / ((j : ℝ) + α + 1 / 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) :=
          Real.sqrt_le_sqrt hsq
  have step2 : ((j : ℝ) + 1 / 2) / ((j : ℝ) + 2) ≤ ((j : ℝ) + 1 / 2) / ((j : ℝ) + α + 1 / 2) := by
    rw [div_le_div_iff_of_pos_left ha0 (by positivity : (0 : ℝ) < (j : ℝ) + 2) hb0]
    linarith [hα2]
  linarith [step1, step2]

/-- For `T ≤ 3` the product is at least `1/500`. -/
lemma prod_lower_small (α T : ℝ) (hα1 : 1 / 2 ≤ α) (hα2 : α ≤ 3 / 2) (hT : 0 ≤ T)
    (hT3 : T ≤ 3) :
    (1 / 500 : ℝ) ≤ Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
      (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := by
  have hN : max 3 (Nat.ceil T) + 1 = 4 := by
    have : Nat.ceil T ≤ 3 := Nat.ceil_le.mpr hT3
    omega
  rw [hN]
  have hterm : ∀ j ∈ Finset.range 4, ((j : ℝ) + 1 / 2) / ((j : ℝ) + 2) ≤
      Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) :=
    fun j _ => term_ge_linear α T hα1 hα2 j
  have hprod := Finset.prod_le_prod₀
    (f := fun j : ℕ => ((j : ℝ) + 1 / 2) / ((j : ℝ) + 2))
    (g := fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))
    (fun j hj => by positivity) hterm
  have hval : Finset.prod (Finset.range 4) (fun j : ℕ => ((j : ℝ) + 1 / 2) / ((j : ℝ) + 2)) = 7 / 128 := by
    norm_num [Finset.prod_range_succ]
  calc (1 / 500 : ℝ) ≤ 7 / 128 := by norm_num
    _ = Finset.prod (Finset.range 4) (fun j : ℕ => ((j : ℝ) + 1 / 2) / ((j : ℝ) + 2)) := hval.symm
    _ ≤ Finset.prod (Finset.range 4)
          (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := hprod

/-- For `T ≥ 3` the product is at least `1/500`. -/
lemma prod_lower_big (α T : ℝ) (hα1 : 1 / 2 ≤ α) (hα2 : α ≤ 3 / 2) (hT : 3 ≤ T) :
    (1 / 500 : ℝ) ≤ Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
      (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := by
  have hα0 : 0 ≤ α := by linarith
  have hTpos : 0 < T := by linarith
  have hFpos : ∀ j : ℕ, 0 < Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) := by
    intro j; rw [Real.sqrt_pos]; apply div_pos <;> positivity
  have hlogF : ∀ j : ℕ, -(α / T) ≤
      Real.log (Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := by
    intro j
    have h1 : Real.log (Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))
        = (1 / 2) * (Real.log (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) - Real.log (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) := by
      rw [Real.log_sqrt (by positivity),
          Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2))
                       (ne_of_gt (by positivity : (0 : ℝ) < T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))]
      ring
    rw [h1]
    have hlin := half_log_sub_le T ((j : ℝ) + 1 / 2) α hT hα0 hα2
    have h2 : (((j : ℝ) + 1 / 2) + α) = ((j : ℝ) + α + 1 / 2) := by ring
    rw [h2] at hlin
    exact hlin
  have hlogPsum : Real.log (Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))))
      = Finset.sum (Finset.range (max 3 (Nat.ceil T) + 1))
        (fun j : ℕ => Real.log (Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))) :=
    Real.log_prod (fun j hj => ne_of_gt (hFpos j))
  have hsumlb : -(((max 3 (Nat.ceil T) : ℕ) : ℝ) + 1) * (α / T) ≤
      Real.log (Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))) := by
    rw [hlogPsum]
    have h := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range (max 3 (Nat.ceil T) + 1)) => hlogF j)
    have hc : Finset.sum (Finset.range (max 3 (Nat.ceil T) + 1)) (fun _ : ℕ => -(α / T))
        = -(((max 3 (Nat.ceil T) : ℕ) : ℝ) + 1) * (α / T) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast; ring
    rw [hc] at h
    exact h
  have hcoef : (((max 3 (Nat.ceil T) : ℕ) : ℝ) + 1) * (α / T) ≤ 5 / 2 := by
    have hle : ((max 3 (Nat.ceil T) : ℕ) : ℝ) + 1 ≤ T + 2 := by
      have h3 : (3 : ℝ) ≤ T + 1 := by linarith
      have hceil : (Nat.ceil T : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      have hmax : ((max 3 (Nat.ceil T) : ℕ) : ℝ) ≤ T + 1 := by
        rw [Nat.cast_max]; simp only [Nat.cast_ofNat]
        exact max_le h3 (le_of_lt hceil)
      linarith
    have hnonneg : 0 ≤ α / T := by positivity
    have step1 : (((max 3 (Nat.ceil T) : ℕ) : ℝ) + 1) * (α / T) ≤ (T + 2) * (α / T) :=
      mul_le_mul_of_nonneg_right hle hnonneg
    have step2 : (T + 2) * (α / T) ≤ 5 / 2 := by
      have : (T + 2) * (α / T) = α * (T + 2) / T := by ring
      rw [this, div_le_iff₀ hTpos]
      nlinarith [hα2, hT]
    linarith
  have hlogPlow : -(5 / 2) ≤ Real.log (Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))) := by
    linarith
  have hPpos : 0 < Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) :=
    Finset.prod_pos (fun j hj => hFpos j)
  have hPge : Real.exp (-(5 / 2)) ≤ Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := by
    rw [← Real.exp_log hPpos]
    exact Real.exp_le_exp.mpr hlogPlow
  have hexp : (1 : ℝ) / 500 < Real.exp (-(5 / 2)) := by
    have he : Real.exp (5 / 2) < 500 := by
      have h1 : Real.exp (5 / 2) < Real.exp 3 := Real.exp_lt_exp.mpr (by norm_num)
      have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by
        have := Real.exp_nat_mul 1 3; simpa using this
      rw [h2] at h1
      have h3 : Real.exp 1 ^ 3 < (3 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      norm_num at h3
      linarith
    rw [Real.exp_neg]
    have heq : (1 : ℝ) / 500 = (500 : ℝ)⁻¹ := by norm_num
    rw [heq, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 500) (Real.exp_pos (5 / 2))]
    linarith
  linarith [hexp, hPge]

theorem gammaRatioSeqLower (α T : ℝ) (hα1 : 1 / 2 ≤ α) (hα2 : α ≤ 3 / 2) (hT : 0 ≤ T) :
    (1 / 1000) * (1 + T) ^ α ≤
      ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α *
        Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
          (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := by
  have hα0 : 0 ≤ α := by linarith
  set P : ℝ := Finset.prod (Finset.range (max 3 (Nat.ceil T) + 1))
      (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) with hPdef
  have hNnn : (0 : ℝ) ≤ ((max 3 (Nat.ceil T) : ℕ) : ℝ) := by positivity
  have hNpow : (0 : ℝ) ≤ ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α := Real.rpow_nonneg hNnn α
  have hP : (1 / 500 : ℝ) ≤ P := by
    rw [hPdef]
    rcases le_or_gt T 3 with hT3 | hT3
    · exact prod_lower_small α T hα1 hα2 hT hT3
    · exact prod_lower_big α T hα1 hα2 (le_of_lt hT3)
  have h1T : 1 + T ≤ (4 / 3) * ((max 3 (Nat.ceil T) : ℕ) : ℝ) := by
    rcases le_or_gt T 3 with hT3 | hT3
    · have hN : (max 3 (Nat.ceil T) : ℕ) = 3 := by
        have : Nat.ceil T ≤ 3 := Nat.ceil_le.mpr hT3
        omega
      rw [hN]; norm_num; linarith
    · have hT3' : (3 : ℝ) ≤ T := le_of_lt hT3
      have hceil3 : (3 : ℕ) ≤ Nat.ceil T := by
        have := Nat.ceil_mono hT3'
        simpa using this
      have hN : (max 3 (Nat.ceil T) : ℕ) = Nat.ceil T := max_eq_right hceil3
      rw [hN]
      have hle : (Nat.ceil T : ℝ) ≥ T := Nat.le_ceil T
      nlinarith [hle, hT3']
  have hstep1 : (1 + T) ^ α ≤ ((4 / 3) * ((max 3 (Nat.ceil T) : ℕ) : ℝ)) ^ α :=
    Real.rpow_le_rpow (by linarith) h1T hα0
  have hstep2 : ((4 / 3) * ((max 3 (Nat.ceil T) : ℕ) : ℝ)) ^ α =
      (4 / 3 : ℝ) ^ α * ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α :=
    Real.mul_rpow (by norm_num) hNnn
  have hstep3 : (4 / 3 : ℝ) ^ α ≤ (4 / 3 : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hα2
  have h43 : (4 / 3 : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 := by
    have hadd := Real.rpow_add (show (0 : ℝ) < 4 / 3 by norm_num) ((1 : ℝ) / 2) 1
    rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num, hadd, Real.rpow_one]
    have hs : (4 / 3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 3 / 2 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
      exact ⟨by norm_num, by norm_num⟩
    nlinarith [mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hconst : (1 / 1000) * (4 / 3 : ℝ) ^ ((3 : ℝ) / 2) ≤ 1 / 500 := by nlinarith [h43]
  calc
    (1 / 1000) * (1 + T) ^ α
        ≤ (1 / 1000) * ((4 / 3 : ℝ) ^ α * ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [← hstep2]; exact hstep1
      _ ≤ (1 / 1000) * ((4 / 3 : ℝ) ^ ((3 : ℝ) / 2) * ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hstep3 hNpow
      _ = ((1 / 1000) * (4 / 3 : ℝ) ^ ((3 : ℝ) / 2)) * ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α := by
          ring
      _ ≤ (1 / 500) * ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hconst hNpow
      _ ≤ P * ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hP hNpow
      _ = ((max 3 (Nat.ceil T) : ℕ) : ℝ) ^ α * P := by ring

end Work.FIArea5.S16Hecke
