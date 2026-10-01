import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs
import Submission.Work.ZeroDensity.Ingham.perronIntDeps
import Submission.Work.ZeroDensity.Ingham.mkStripBound
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_strip_region_bound

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- Pointwise strip bound for the entire factor `perronM` of the patched Perron integrand. -/
lemma perronMStripBoundOne (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ)
    (hβ0 : (1 : ℝ) / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ w : ℂ,
      (1 / 2 : ℝ) - ρ.re ≤ w.re → w.re ≤ 2 → |ρ.im| + 1 ≤ |w.im| →
      ‖perronM K Y ρ w‖ ≤ C * Real.exp (-(Real.pi / 2) * |w.im|) * (1 + |w.im|) ^ A := by
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.LinnikAreas.Zeta1Aux.zeta1_strip_region_bound
  have hCYpos : 0 < max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2) :=
    lt_max_of_lt_left (Real.rpow_pos_of_pos hY _)
  have hSKnonneg : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3 :=
    Finset.sum_nonneg (fun n _ => pow_nonneg (Nat.cast_nonneg n) 3)
  refine ⟨Commons.Analysis.Complex.K6 * ((Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13)
      * max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2) * ((∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3) + 1), 19,
      ?_, by norm_num, ?_⟩
  · have h1 : 0 < (Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13 :=
      mul_pos (by linarith [norm_nonneg (riemannZeta₁ ρ)]) (by norm_num)
    exact mul_pos (mul_pos (mul_pos Commons.Analysis.Complex.K6_pos h1) hCYpos)
      (by linarith)
  · intro w hwl hwr hwim
    have hwim1 : (1 : ℝ) ≤ |w.im| := by linarith [abs_nonneg ρ.im]
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hwim1
      norm_num at hwim1
    -- ## the `Γ(w+1)` factor
    have hG : ‖Complex.Gamma (w + 1)‖ ≤
        Commons.Analysis.Complex.K6 * (1 + |w.im|) ^ 6 *
          Real.exp (-(Real.pi / 2) * |w.im|) := by
      have h := Commons.Analysis.Complex.gamma_strip_upper (w.re + 1) w.im
        (by linarith) (by linarith) hwim1
      have hre : w + 1 = (((w.re + 1 : ℝ)) : ℂ) + Complex.I * ((w.im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hre]
      calc ‖Complex.Gamma (↑(w.re + 1) + Complex.I * ↑w.im)‖
          ≤ Commons.Analysis.Complex.K6 * (1 + |w.im|) ^ (6 : ℝ) *
              Real.exp (-(Real.pi / 2) * |w.im|) := h
        _ = Commons.Analysis.Complex.K6 * (1 + |w.im|) ^ 6 *
              Real.exp (-(Real.pi / 2) * |w.im|) := by norm_num
    -- ## the `ζ₁` factor and the divided difference
    have hζ1re : -2 ≤ (ρ + w).re := by simp only [Complex.add_re]; linarith
    have hζ1hi : (ρ + w).re ≤ 3 := by simp only [Complex.add_re]; linarith
    have hζ1im : 1 ≤ |(ρ + w).im| := by
      have h2 : |w.im| - |ρ.im| ≤ |w.im + ρ.im| := by
        have h := abs_abs_sub_abs_le_abs_sub w.im (-ρ.im)
        rw [abs_neg, sub_neg_eq_add] at h
        have h3 : |w.im| - |ρ.im| ≤ abs (|w.im| - |ρ.im|) := le_abs_self _
        linarith
      have h4 : (ρ + w).im = ρ.im + w.im := Complex.add_im ρ w
      rw [h4, add_comm ρ.im w.im]
      linarith
    have hζ1b : ‖riemannZeta₁ (ρ + w)‖ ≤ Cz * (|(ρ + w).im| + 3) ^ 13 :=
      hCz (ρ + w) hζ1re hζ1hi hζ1im
    have hds : ‖dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 w‖ ≤
        (Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13 * (1 + |w.im|) ^ 13 := by
      rw [dslope_of_ne (fun t : ℂ => riemannZeta₁ (ρ + t)) hw0, slope_def_field,
        add_zero, sub_zero]
      rw [norm_div]
      have hnum : ‖riemannZeta₁ (ρ + w) - riemannZeta₁ ρ‖ ≤
          (Cz + ‖riemannZeta₁ ρ‖) * (|(ρ + w).im| + 3) ^ 13 := by
        have hX1 : (1 : ℝ) ≤ (|(ρ + w).im| + 3) ^ 13 := by
          have h3 : (1 : ℝ) ≤ |(ρ + w).im| + 3 := by linarith [abs_nonneg (ρ + w).im]
          calc (1 : ℝ) = 1 ^ 13 := by norm_num
            _ ≤ (|(ρ + w).im| + 3) ^ 13 := pow_le_pow_left₀ (by norm_num) h3 13
        have hMnn : (0 : ℝ) ≤ ‖riemannZeta₁ ρ‖ := norm_nonneg _
        refine le_trans (norm_sub_le _ _) ?_
        have h4 : ‖riemannZeta₁ ρ‖ ≤ ‖riemannZeta₁ ρ‖ * (|(ρ + w).im| + 3) ^ 13 := by
          calc ‖riemannZeta₁ ρ‖ = ‖riemannZeta₁ ρ‖ * 1 := (mul_one _).symm
            _ ≤ ‖riemannZeta₁ ρ‖ * (|(ρ + w).im| + 3) ^ 13 :=
                mul_le_mul_of_nonneg_left hX1 hMnn
        linarith [hζ1b, h4, norm_nonneg (riemannZeta₁ ρ)]
      have hX : (|(ρ + w).im| + 3) ≤ 2 * (1 + |w.im|) := by
        have h1 : |ρ.im| ≤ |w.im| := by linarith
        have h2 : (ρ + w).im = ρ.im + w.im := Complex.add_im ρ w
        rw [h2]
        have h3 := abs_add_le ρ.im w.im
        linarith
      have hX13 : (|(ρ + w).im| + 3) ^ 13 ≤ (2 * (1 + |w.im|)) ^ 13 :=
        pow_le_pow_left₀ (by positivity) hX 13
      have hnum_nn : (0 : ℝ) ≤ (Cz + ‖riemannZeta₁ ρ‖) * (|(ρ + w).im| + 3) ^ 13 :=
        mul_nonneg (by linarith [norm_nonneg (riemannZeta₁ ρ)]) (by positivity)
      have hden1 : (1 : ℝ) ≤ ‖w‖ := by
        have := Complex.abs_im_le_norm w
        linarith [abs_nonneg w.im]
      calc ‖riemannZeta₁ (ρ + w) - riemannZeta₁ ρ‖ / ‖w‖
          ≤ ((Cz + ‖riemannZeta₁ ρ‖) * (|(ρ + w).im| + 3) ^ 13) / ‖w‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg _)
        _ ≤ ((Cz + ‖riemannZeta₁ ρ‖) * (|(ρ + w).im| + 3) ^ 13) / 1 :=
            div_le_div_of_nonneg_left hnum_nn one_pos hden1
        _ = (Cz + ‖riemannZeta₁ ρ‖) * (|(ρ + w).im| + 3) ^ 13 := div_one _
        _ ≤ (Cz + ‖riemannZeta₁ ρ‖) * (2 * (1 + |w.im|)) ^ 13 :=
            mul_le_mul_of_nonneg_left hX13 (by linarith [norm_nonneg (riemannZeta₁ ρ)])
        _ = (Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13 * (1 + |w.im|) ^ 13 := by
            rw [mul_pow]; ring
    -- ## the `Y^w` factor
    have hYw : ‖(Y : ℂ) ^ w‖ ≤ max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      rcases le_total Y 1 with h1 | h1
      · have h2 : Y ^ w.re ≤ Y ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hY h1 (by linarith)
        exact le_trans h2 (le_max_left _ _)
      · have h2 : Y ^ w.re ≤ Y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hwr
        have h3 : Y ^ (2 : ℝ) = Y ^ 2 := by norm_num
        rw [h3] at h2
        exact le_trans h2 (le_max_right _ _)
    -- ## the `M_K` factor
    have hMK : ‖MK K (ρ + w)‖ ≤ (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3) + 1 := by
      have hs : (-3 : ℝ) ≤ (ρ + w).re := by simp only [Complex.add_re]; linarith
      have := mkStripBound K hs
      linarith [hSKnonneg]
    -- ## combine
    have hGnn : 0 ≤ Commons.Analysis.Complex.K6 * (1 + |w.im|) ^ 6 *
        Real.exp (-(Real.pi / 2) * |w.im|) :=
      mul_nonneg (mul_nonneg Commons.Analysis.Complex.K6_pos.le
        (pow_nonneg (by positivity) 6)) (Real.exp_nonneg _)
    have hdsnn : 0 ≤ (Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13 * (1 + |w.im|) ^ 13 := by
      have h1 : (0 : ℝ) < Cz + ‖riemannZeta₁ ρ‖ := by linarith [norm_nonneg (riemannZeta₁ ρ)]
      positivity
    have hYwnn : 0 ≤ max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2) := le_of_lt hCYpos
    have hMKnn : 0 ≤ (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3) + 1 := by linarith
    have hprod : ‖perronM K Y ρ w‖ ≤
        (Commons.Analysis.Complex.K6 * (1 + |w.im|) ^ 6 * Real.exp (-(Real.pi / 2) * |w.im|))
        * ((Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13 * (1 + |w.im|) ^ 13)
        * max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2)
        * ((∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3) + 1) := by
      rw [perronM, norm_mul, norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (mul_le_mul hG hds (norm_nonneg _) hGnn) hYw (norm_nonneg _)
        (mul_nonneg hGnn hdsnn)) hMK (norm_nonneg _)
        (mul_nonneg (mul_nonneg hGnn hdsnn) hYwnn)
    have heq : (Commons.Analysis.Complex.K6 * (1 + |w.im|) ^ 6 * Real.exp (-(Real.pi / 2) * |w.im|))
        * ((Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13 * (1 + |w.im|) ^ 13)
        * max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2)
        * ((∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3) + 1)
        = Commons.Analysis.Complex.K6 * ((Cz + ‖riemannZeta₁ ρ‖) * 2 ^ 13)
          * max (Y ^ (-(1 / 2) : ℝ)) (Y ^ 2)
          * ((∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3) + 1)
          * Real.exp (-(Real.pi / 2) * |w.im|) * (1 + |w.im|) ^ (19 : ℝ) := by
      have h19 : (1 + |w.im|) ^ (19 : ℝ) = (1 + |w.im|) ^ 19 := by norm_num
      rw [h19]; ring_nf
    exact le_trans hprod (le_of_eq heq)

/-- Decay of the horizontal edge integrals of the patched Perron integrand on the segment
`1/2 - Re ρ ≤ x ≤ 2`. -/
theorem perronHHorizontalOne (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ)
    (hβ0 : (1 : ℝ) / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) :
    Filter.Tendsto (fun R : ℝ => ∫ x in ((1 / 2 : ℝ) - ρ.re)..2,
        perronH K Y ρ ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun R : ℝ => ∫ x in ((1 / 2 : ℝ) - ρ.re)..2,
        perronH K Y ρ ((x : ℂ) - (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
  obtain ⟨C, A, hCpos, hAnn, hbound⟩ := perronMStripBoundOne K Y hY ρ hβ0 hβ1
  set a : ℝ := (1 / 2 : ℝ) - ρ.re with ha
  set c₀ : ℝ := ‖perronM K Y ρ (1 - ρ)‖ with hc₀
  have ha2 : a ≤ 2 := by rw [ha]; linarith
  have hc₀nn : (0 : ℝ) ≤ c₀ := by rw [hc₀]; positivity
  -- ## decay of the dominating sequence
  have hdec1 : Filter.Tendsto (fun R : ℝ => (1 + R) ^ A * Real.exp (-(Real.pi / 2) * R))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun R : ℝ => R ^ A * Real.exp (-(Real.pi / 2) * R))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A (Real.pi / 2) (by positivity)
    have hmul : Filter.Tendsto
        (fun R : ℝ => (2 : ℝ) ^ A * (R ^ A * Real.exp (-(Real.pi / 2) * R)))
        Filter.atTop (nhds 0) := by
      simpa using hbase.const_mul ((2 : ℝ) ^ A)
    refine squeeze_zero' ?_ ?_ hmul
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
      exact mul_nonneg (Real.rpow_nonneg (by linarith) A) (Real.exp_nonneg _)
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
      have hb : (1 + R) ^ A ≤ (2 * R) ^ A := Real.rpow_le_rpow (by linarith) (by linarith) hAnn
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ R)] at hb
      calc (1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)
          ≤ (2 ^ A * R ^ A) * Real.exp (-(Real.pi / 2) * R) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = (2 : ℝ) ^ A * (R ^ A * Real.exp (-(Real.pi / 2) * R)) := by ring
  have hdec2 : Filter.Tendsto (fun R : ℝ => 2 * c₀ / R) Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 * c₀)
    rw [mul_zero] at h
    simpa [div_eq_mul_inv] using h
  have hlim : Filter.Tendsto (fun R : ℝ =>
      (2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R) * (2 - a))
      Filter.atTop (nhds 0) := by
    have h := ((hdec1.const_mul (2 * C)).add hdec2).mul_const (2 - a)
    simpa using h
  -- ## pointwise bound at height `R`
  have hkey : ∀ (R : ℝ) (w : ℂ), a ≤ w.re → w.re ≤ 2 → |w.im| = R → 2 * |ρ.im| + 2 ≤ R →
      ‖perronH K Y ρ w‖ ≤
        2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R := by
    intro R w h1 h2 hwim hR
    have hRpos : 0 < R := by linarith [abs_nonneg ρ.im]
    have hR1 : (1 : ℝ) ≤ R := by linarith [abs_nonneg ρ.im]
    have hM : ‖perronM K Y ρ w‖ ≤ C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A := by
      have h := hbound w h1 h2 (by rw [hwim]; linarith [abs_nonneg ρ.im])
      rwa [hwim] at h
    have hden : R / 2 ≤ ‖w - (1 - ρ)‖ := by
      have him2 : (w - (1 - ρ)).im = w.im + ρ.im := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub, sub_neg_eq_add]
      have hlow : |w.im| - |ρ.im| ≤ |w.im + ρ.im| := by
        have h := abs_abs_sub_abs_le_abs_sub w.im (-ρ.im)
        rw [abs_neg, sub_neg_eq_add] at h
        have h3 : |w.im| - |ρ.im| ≤ abs (|w.im| - |ρ.im|) := le_abs_self _
        linarith
      calc R / 2 ≤ |w.im + ρ.im| := by rw [hwim] at hlow; linarith [abs_nonneg ρ.im]
        _ = |(w - (1 - ρ)).im| := by rw [him2]
        _ ≤ ‖w - (1 - ρ)‖ := Complex.abs_im_le_norm _
    have hne : w ≠ 1 - ρ := by
      intro h
      have h3 := hden
      rw [h] at h3
      simp at h3
      linarith
    have hnum : ‖perronM K Y ρ w - perronM K Y ρ (1 - ρ)‖
        ≤ C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A + c₀ := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hc₀]
      exact add_le_add hM le_rfl
    have hX0 : (0 : ℝ) ≤ C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A + c₀ := by
      have h : (0 : ℝ) ≤ C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A :=
        mul_nonneg (mul_nonneg hCpos.le (Real.exp_nonneg _)) (Real.rpow_nonneg (by linarith) A)
      linarith
    have hAnnn : (0 : ℝ) ≤ C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A :=
      mul_nonneg (mul_nonneg hCpos.le (Real.exp_nonneg _)) (Real.rpow_nonneg (by linarith) A)
    have hslope : perronH K Y ρ w
        = (perronM K Y ρ w - perronM K Y ρ (1 - ρ)) / (w - (1 - ρ)) := by
      rw [perronH, dslope_of_ne (perronM K Y ρ) hne, slope_def_field]
    calc ‖perronH K Y ρ w‖
        = ‖perronM K Y ρ w - perronM K Y ρ (1 - ρ)‖ / ‖w - (1 - ρ)‖ := by
          rw [hslope, norm_div]
      _ ≤ (C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A + c₀) / ‖w - (1 - ρ)‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A + c₀) / (R / 2) :=
          div_le_div_of_nonneg_left hX0 (by linarith) hden
      _ = 2 * (C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A) / R + 2 * c₀ / R := by ring
      _ ≤ 2 * (C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A) + 2 * c₀ / R := by
          have h1 : 2 * (C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A) / R
              ≤ 2 * (C * Real.exp (-(Real.pi / 2) * R) * (1 + R) ^ A) := by
            rw [div_le_iff₀ hRpos]
            nlinarith [hAnnn]
          linarith
      _ = 2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R := by ring
  -- ## the two edges
  have hbdp : ∀ᶠ R : ℝ in Filter.atTop,
      ‖∫ x in a..2, perronH K Y ρ ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤
        (2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R) * (2 - a) := by
    filter_upwards [Filter.eventually_ge_atTop (2 * |ρ.im| + 2)] with R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := 2)
      (C := 2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R)
      (f := fun x : ℝ => perronH K Y ρ ((x : ℂ) + (R : ℂ) * Complex.I)) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - a)] at h
    · intro x hx
      rw [Set.uIoc_of_le ha2] at hx
      have him : (((x : ℂ) + (R : ℂ) * Complex.I)).im = R := by simp
      have hre : (((x : ℂ) + (R : ℂ) * Complex.I)).re = x := by simp
      exact hkey R _ (by rw [hre]; exact le_of_lt hx.1)
        (by rw [hre]; exact hx.2)
        (by rw [him, abs_of_nonneg (by linarith [abs_nonneg ρ.im])]) hR
  have hbdm : ∀ᶠ R : ℝ in Filter.atTop,
      ‖∫ x in a..2, perronH K Y ρ ((x : ℂ) - (R : ℂ) * Complex.I)‖ ≤
        (2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R) * (2 - a) := by
    filter_upwards [Filter.eventually_ge_atTop (2 * |ρ.im| + 2)] with R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := 2)
      (C := 2 * C * ((1 + R) ^ A * Real.exp (-(Real.pi / 2) * R)) + 2 * c₀ / R)
      (f := fun x : ℝ => perronH K Y ρ ((x : ℂ) - (R : ℂ) * Complex.I)) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - a)] at h
    · intro x hx
      rw [Set.uIoc_of_le ha2] at hx
      have him : (((x : ℂ) - (R : ℂ) * Complex.I)).im = -R := by simp
      have hre : (((x : ℂ) - (R : ℂ) * Complex.I)).re = x := by simp
      exact hkey R _ (by rw [hre]; exact le_of_lt hx.1)
        (by rw [hre]; exact hx.2)
        (by rw [him, abs_neg, abs_of_nonneg (by linarith [abs_nonneg ρ.im])]) hR
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) hbdp hlim
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) hbdm hlim

end Work.ZeroDensity.Ingham
