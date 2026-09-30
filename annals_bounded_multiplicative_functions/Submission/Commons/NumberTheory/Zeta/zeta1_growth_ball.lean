import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Metric Set
open scoped Topology BigOperators
noncomputable section
namespace Commons.NumberTheory.Zeta

private lemma zeta1_norm_eq_mul (w : ℂ) (hw : w ≠ 1) :
    ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
  have h1 : (w - 1) * riemannZeta w = riemannZeta₁ w := by
    calc
      (w - 1) * riemannZeta w = (w - 1) * ((w - 1)⁻¹ * riemannZeta₁ w) := by
        rw [riemannZeta_eq_inv_sub_mul hw]
      _ = riemannZeta₁ w := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hw)]
        simp
  calc
    ‖riemannZeta₁ w‖ = ‖(w - 1) * riemannZeta w‖ := by rw [← h1]
    _ = ‖w - 1‖ * ‖riemannZeta w‖ := by rw [norm_mul]

/-- A uniform bound for `riemannZeta₁` on the fixed rectangle
`1/2 ≤ re w ≤ 7/2`, `|im w| ≤ 1`. -/
private lemma box_zeta1_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ w : ℂ, (1/2 : ℝ) ≤ w.re → w.re ≤ 7/2 → |w.im| ≤ 1 → ‖riemannZeta₁ w‖ ≤ C := by
  let K : Set ℂ := ((fun p : ℝ × ℝ ↦ (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
    (Set.Icc (1 / 2 : ℝ) (7 / 2) ×ˢ Set.Icc (-1 : ℝ) (1 : ℝ)))
  have hφcont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) := by
    fun_prop
  have hI1 : IsCompact (Set.Icc (1 / 2 : ℝ) (7 / 2)) := isCompact_Icc
  have hI2 : IsCompact (Set.Icc (-1 : ℝ) (1 : ℝ)) := isCompact_Icc
  have hK : IsCompact K := by
    dsimp [K]
    exact (IsCompact.prod hI1 hI2).image hφcont
  have hKne : K.Nonempty := by
    refine ⟨(2 : ℂ), ?_⟩
    refine ⟨((2 : ℝ), (0 : ℝ)), ⟨by norm_num, by norm_num⟩, ?_⟩
    apply Complex.ext <;> simp
  have hcontOn : ContinuousOn (fun w : ℂ => ‖riemannZeta₁ w‖) K :=
    (differentiable_riemannZeta₁.continuous.norm).continuousOn
  rcases hK.exists_isMaxOn hKne hcontOn with ⟨x, hxK, hxmax⟩
  refine ⟨‖riemannZeta₁ x‖ + 1, by positivity, ?_⟩
  intro w hσlo hσhi hτ
  have hwK : w ∈ K := by
    refine ⟨(w.re, w.im), ⟨⟨hσlo, hσhi⟩, ?_⟩, ?_⟩
    · exact (abs_le.mp hτ)
    · apply Complex.ext <;> simp
  exact le_trans (hxmax hwK) (by linarith)

/-- Pass from a polynomial bound with coefficient `A` to the requested shape. -/
private lemma growth_glue {A C δ t : ℝ} (hC : 0 ≤ C) (hAC : A ≤ C) (hδ0 : 0 < δ) :
    A * (|t| + 6) ^ 5 ≤ C * (1 + 1 / δ) * (|t| + 6) ^ 5 := by
  have hX0 : 0 ≤ (|t| + 6) ^ 5 := by positivity
  have hδge : (1 : ℝ) ≤ 1 + 1 / δ := by
    have h : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδ0)
    linarith
  calc
    A * (|t| + 6) ^ 5 ≤ C * (|t| + 6) ^ 5 := mul_le_mul_of_nonneg_right hAC hX0
    _ = (C * 1) * (|t| + 6) ^ 5 := by ring
    _ ≤ (C * (1 + 1 / δ)) * (|t| + 6) ^ 5 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδge hC) hX0
    _ = C * (1 + 1 / δ) * (|t| + 6) ^ 5 := by ring

theorem zeta1_growth_ball :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t : ℝ, 0 < δ → δ ≤ 1 →
      ∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ < 3 / 2 - δ / 2 →
        ‖riemannZeta₁ w‖ ≤ C * (1 + 1 / δ) * (|t| + 6) ^ 5 := by
  rcases zeta_strip_polyGrowth with ⟨Cpg, hCpg0, hCpgSpec⟩
  rcases zeta_norm_le_const_of_three_le_re with ⟨C3, hC3_0, hC3Spec⟩
  rcases box_zeta1_bound with ⟨Cb, hCb0, hCbSpec⟩
  let C : ℝ := max Cpg (max C3 Cb)
  have hC0 : 0 < C := lt_max_of_lt_left hCpg0
  have hC0le : 0 ≤ C := le_of_lt hC0
  refine ⟨C, hC0, ?_⟩
  intro δ t hδ0 hδ1 w hball
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let R : ℝ := 3 / 2 - δ / 2
  have hσdist : |w.re - 2| ≤ ‖w - c‖ := by
    simpa [c] using (Complex.abs_re_le_norm (w - c))
  have hτdist : |w.im - t| ≤ ‖w - c‖ := by
    simpa [c] using (Complex.abs_im_le_norm (w - c))
  have hσabs : |w.re - 2| < R := lt_of_le_of_lt hσdist hball
  have hτabs : |w.im - t| < R := lt_of_le_of_lt hτdist hball
  have hR : R ≤ 3 / 2 := by
    dsimp [R]
    linarith
  have hσlo : (1 / 2 : ℝ) ≤ w.re := by
    have h1 : -R < w.re - 2 := (abs_lt.mp hσabs).1
    have h2 : 2 - R ≥ (1 / 2 : ℝ) := by dsimp [R]; linarith
    linarith
  have hσhi : w.re ≤ 7 / 2 := by
    have h1 : w.re - 2 < R := (abs_lt.mp hσabs).2
    have h2 : R + 2 ≤ (7 / 2 : ℝ) := by dsimp [R]; linarith
    linarith
  have hτtb : |w.im| ≤ |t| + 3 / 2 := by
    have htri : |w.im| ≤ |w.im - t| + |t| := by
      calc |w.im| = |(w.im - t) + t| := by congr 1; ring
        _ ≤ |w.im - t| + |t| := abs_add_le (w.im - t) t
    have hle32 : |w.im - t| ≤ 3 / 2 := le_trans (le_of_lt hτabs) hR
    linarith
  have hc1 : ‖c - 1‖ ≤ 1 + |t| := by
    dsimp [c]
    have hrew : ((2 : ℂ) + Complex.I * (t : ℂ)) - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by ring
    rw [hrew]
    calc
      ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
      _ = 1 + |t| := by
        rw [norm_one]
        rw [norm_mul]
        rw [Complex.norm_I]
        rw [Complex.norm_real]
        rw [Real.norm_eq_abs]
        ring
  have hw1le : ‖w - 1‖ ≤ |t| + 6 := by
    have hsum : (w - c) + (c - 1) = w - 1 := by ring
    calc
      ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by rw [← hsum]
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 3 / 2 + (1 + |t|) := by
        have h1 : ‖w - c‖ ≤ 3 / 2 := le_trans (le_of_lt hball) hR
        exact add_le_add h1 hc1
      _ ≤ |t| + 6 := by linarith
  have hX1 : (1 : ℝ) ≤ (|t| + 6) ^ 5 := by
    exact one_le_pow₀ (by linarith [abs_nonneg t] : (1 : ℝ) ≤ |t| + 6)
  by_cases hτbig : 1 ≤ |w.im|
  · have hwne1 : w ≠ 1 := by
      intro h
      have hz : |w.im| = 0 := by simp [h]
      linarith
    by_cases hσ3 : w.re ≤ 3
    · have hζle : ‖riemannZeta w‖ ≤ Cpg * (|w.im| + 3) ^ 4 := by
        have hform : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
          apply Complex.ext <;> simp
        have hEqZeta : riemannZeta w = riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
          exact congrArg riemannZeta hform
        rw [hEqZeta]
        exact hCpgSpec w.re w.im (by linarith) hσ3 hτbig
      have hτ36 : |w.im| + 3 ≤ |t| + 6 := by
        linarith
      have hpow46 : (|w.im| + 3) ^ 4 ≤ (|t| + 6) ^ 4 := by
        exact pow_le_pow_left₀ (by positivity : 0 ≤ |w.im| + 3) hτ36 4
      have hmain : ‖riemannZeta₁ w‖ ≤ Cpg * (|t| + 6) ^ 5 := by
        calc
          ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := zeta1_norm_eq_mul w hwne1
          _ ≤ (|t| + 6) * ‖riemannZeta w‖ := by
            exact mul_le_mul_of_nonneg_right hw1le (norm_nonneg _)
          _ ≤ (|t| + 6) * (Cpg * (|w.im| + 3) ^ 4) := by
            exact mul_le_mul_of_nonneg_left hζle (by positivity : 0 ≤ |t| + 6)
          _ ≤ (|t| + 6) * (Cpg * (|t| + 6) ^ 4) := by
            have hmult : Cpg * (|w.im| + 3) ^ 4 ≤ Cpg * (|t| + 6) ^ 4 :=
              mul_le_mul_of_nonneg_left hpow46 (le_of_lt hCpg0)
            exact mul_le_mul_of_nonneg_left hmult (by positivity : 0 ≤ |t| + 6)
          _ = Cpg * (|t| + 6) ^ 5 := by ring_nf
      have hAC : Cpg ≤ C := le_max_left Cpg (max C3 Cb)
      exact le_trans hmain (growth_glue hC0le hAC hδ0)
    · have hσ3re : 3 ≤ w.re := by linarith
      have hζle : ‖riemannZeta w‖ ≤ C3 := hC3Spec w hσ3re
      have hmain : ‖riemannZeta₁ w‖ ≤ C3 * (|t| + 6) ^ 5 := by
        calc
          ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := zeta1_norm_eq_mul w hwne1
          _ ≤ (|t| + 6) * ‖riemannZeta w‖ := by
            exact mul_le_mul_of_nonneg_right hw1le (norm_nonneg _)
          _ ≤ (|t| + 6) * C3 := by
            exact mul_le_mul_of_nonneg_left hζle (by positivity : 0 ≤ |t| + 6)
          _ = C3 * (|t| + 6) := by ring
          _ ≤ C3 * (|t| + 6) ^ 5 := by
            have hx : (|t| + 6 : ℝ) ≤ (|t| + 6) ^ 5 := by
              have hp := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ |t| + 6) (by norm_num : (1 : ℕ) ≤ 5)
              simpa using hp
            exact mul_le_mul_of_nonneg_left hx (le_of_lt hC3_0)
      have hAC : C3 ≤ C := by
        have h1 : C3 ≤ max C3 Cb := le_max_left C3 Cb
        exact le_trans h1 (le_max_right Cpg (max C3 Cb))
      exact le_trans hmain (growth_glue hC0le hAC hδ0)
  · have hτlt1 : |w.im| < 1 := lt_of_not_ge hτbig
    have hbCb := hCbSpec w hσlo hσhi (le_of_lt hτlt1)
    have hmain : ‖riemannZeta₁ w‖ ≤ Cb * (|t| + 6) ^ 5 := by
      calc
        ‖riemannZeta₁ w‖ ≤ Cb := hbCb
        _ ≤ Cb * (|t| + 6) ^ 5 := by
          have h := mul_le_mul_of_nonneg_left hX1 (le_of_lt hCb0)
          simpa using h
    have hAC : Cb ≤ C := by
      have h1 : Cb ≤ max C3 Cb := le_max_right C3 Cb
      exact le_trans h1 (le_max_right Cpg (max C3 Cb))
    exact le_trans hmain (growth_glue hC0le hAC hδ0)

end Commons.NumberTheory.Zeta
