import Mathlib
import Submission.Work.Pert.Basic

/-!
# PERT · `Work.Pert.liftF_sub_translation_le_cont`

The "translation by `1`" error of the lift `F_f = liftF u σ α` at the upper end, in the
*continuous* form: only `ContinuousAt u 0` and `u 0 ≠ 0` are assumed about the germ `u`.  If
`1 - σ u 0 = exp (2πi α)` holds with `0 < ‖α‖ ≤ 1/64`, then for `‖τ_f z‖` small enough there is
`K > 0` with

    ‖liftF u σ α z - (z + 1)‖ ≤ K (‖u (τ_f z) - u 0‖ + ‖τ_f z‖) .

The proof is the exact algebraic computation of (A.1.7)/(4.2.x) with the Lipschitz bound
`‖u 0 - u τ‖ ≤ C ‖τ‖` of the sibling file `liftF_sub_translation_le` replaced by the plain
continuity of `u` at `0` (which gives both `‖u τ - u 0‖ → 0` and the local bound
`‖u τ‖ ≤ ‖u 0‖ + 1`).  Writing `A = exp (2πiα) = 1 - σ u 0`, `τ = τ_f z` and

    E = σ (u 0 - u τ + u 0 (τ u τ)) / (A (1 + τ u τ))

one has `1 - s = A (1 + E)` with `s = sfun u σ α z`, and `log A = 2πiα` for the principal branch,
so that `liftF u σ α z - (z + 1) = (2πiα)⁻¹ log (1 + E)`; everything is then bounded with
`‖u 0 - u τ‖` and `‖τ‖`.
-/

open Complex

namespace Work.Pert

noncomputable section

/-- `1 + w ≠ 0` as soon as `‖w‖ < 1`. -/
private lemma one_add_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) + w ≠ 0 := by
  intro h
  have h1 : w = -1 := by linear_combination h
  rw [h1, norm_neg, norm_one] at hw
  exact lt_irrefl 1 hw

/-- Principal logarithm of a product of two numbers with positive real part. -/
private lemma log_mul_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
  refine Complex.log_mul hx0 hy0 ?_
  have hxa : |x.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hya : |y.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  rw [abs_lt] at hxa hya
  have hpi : (Real.pi : ℝ) / 2 + Real.pi / 2 = Real.pi := by ring
  constructor <;> linarith [hxa.1, hxa.2, hya.1, hya.2, hpi]

/-- The algebraic identity `1 - s = A (1 + E)` behind the near-translation estimate, where
`s = σ u τ / (1 + τ u τ)` and `E = σ (u 0 - u τ + u 0 (τ u τ)) / (A (1 + τ u τ))`; the
normalisation enters as `A + σ u 0 = 1`. -/
private lemma sfun_factor {u : ℂ → ℂ} {σ τ A : ℂ} (hA : A ≠ 0)
    (h1 : 1 + τ * u τ ≠ 0) (hσu : A + σ * u 0 = 1) :
    1 - σ * u τ / (1 + τ * u τ)
      = A * (1 + σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ))) := by
  have hnum : 1 - σ * u τ / (1 + τ * u τ)
      = (A + τ * u τ + σ * (u 0 - u τ)) / (1 + τ * u τ) := by
    rw [eq_div_iff h1, sub_mul, div_mul_cancel₀ _ h1]
    linear_combination -hσu
  have hA' : A * (σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ)))
      = σ * (u 0 - u τ + u 0 * (τ * u τ)) / (1 + τ * u τ) := by
    field_simp
  have hnum2 : A * (1 + σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ)))
      = (A + τ * u τ + σ * (u 0 - u τ)) / (1 + τ * u τ) := by
    rw [mul_add, mul_one, hA', eq_div_iff h1, add_mul, div_mul_cancel₀ _ h1]
    linear_combination (τ * u τ) * hσu
  rw [hnum, hnum2]

theorem liftF_sub_translation_le_cont {u : ℂ → ℂ} {σ α : ℂ}
    (hu : ContinuousAt u 0) (hu0 : u 0 ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hαne : α ≠ 0) (hαsmall : ‖α‖ ≤ 1 / 64) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ z : ℂ,
      ‖Work.Pert.tauC σ α z‖ ≤ ε →
        ‖Work.Pert.liftF u σ α z - (z + 1)‖
          ≤ K * (‖u (Work.Pert.tauC σ α z) - u 0‖ + ‖Work.Pert.tauC σ α z‖) := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hαre_le : α.re ≤ 1 / 64 :=
    le_trans (le_abs_self α.re) (le_trans (Complex.abs_re_le_norm α) hαsmall)
  have hαre_ge : -(1 / 64 : ℝ) ≤ α.re :=
    le_trans (neg_le_neg (le_trans (Complex.abs_re_le_norm α) hαsmall)) (neg_abs_le α.re)
  have hw_norm : ‖(2 * Real.pi * I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hw_im : ((2 * Real.pi * I * α : ℂ)).im = 2 * Real.pi * α.re := by
    simp [Complex.mul_im, Complex.mul_re]
  have htwopi : 2 * Real.pi * ‖α‖ ≤ 1 := by
    have h1 : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * (1 / 64) :=
      mul_le_mul_of_nonneg_left hαsmall (by positivity)
    nlinarith [Real.pi_le_four]
  have hfourpi : 4 * Real.pi * ‖α‖ ≤ 1 / 2 := by
    have h1 : 4 * Real.pi * ‖α‖ ≤ 4 * Real.pi * (1 / 64) :=
      mul_le_mul_of_nonneg_left hαsmall (by positivity)
    nlinarith [Real.pi_le_four]
  -- the exponential `A = exp (2πiα) = 1 - σ u 0`
  set A : ℂ := Complex.exp (2 * Real.pi * I * α) with hA
  have hnormA : 1 - σ * u 0 = A := by rw [hA]; exact hnorm
  have hA_ne : A ≠ 0 := by rw [hA]; exact Complex.exp_ne_zero _
  have hlog_exp : Complex.log A = 2 * Real.pi * I * α := by
    rw [hA]
    refine Complex.log_exp ?_ ?_
    · rw [hw_im]; nlinarith [Real.pi_pos, hαre_ge]
    · rw [hw_im]; nlinarith [Real.pi_pos, hαre_le]
  have hAnorm_sub : ‖A - 1‖ ≤ 4 * Real.pi * ‖α‖ := by
    have h := Complex.norm_exp_sub_one_le (x := (2 * Real.pi * I * α : ℂ))
      (by rw [hw_norm]; exact htwopi)
    rw [hw_norm] at h
    rw [hA]
    linarith
  have hA_re : (1 : ℝ) / 2 ≤ A.re := by
    have h := Complex.abs_re_le_norm (A - 1)
    rw [abs_le] at h
    have h2 : (A - 1).re = A.re - 1 := by simp
    linarith [h.1, hAnorm_sub, hfourpi, h2]
  have hA_norm : (1 : ℝ) / 2 ≤ ‖A‖ := by
    have h := abs_norm_sub_norm_le A (1 : ℂ)
    rw [norm_one, abs_le] at h
    linarith [h.1, hAnorm_sub, hfourpi]
  have hσu : σ * u 0 = 1 - A := by linear_combination -hnormA
  have hσuA : A + σ * u 0 = 1 := by linear_combination hσu
  -- the constant `L` dominating both `1` and `‖u 0‖ (‖u 0‖ + 1)`
  set L : ℝ := max 1 (‖u 0‖ * (‖u 0‖ + 1)) with hLdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hLge : ‖u 0‖ * (‖u 0‖ + 1) ≤ L := le_max_right _ _
  -- the threshold coming from the continuity of `u` at `0`
  set P : ℝ := 16 * (‖σ‖ * L + 1) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  set η : ℝ := min 1 (1 / P) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min one_pos (div_pos one_pos hPpos)
  have hη1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
  have hηP : η ≤ 1 / P := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hu) η hηpos
  set ε : ℝ := min (δ / 2) (min (1 / (8 * (‖u 0‖ + 1))) (1 / P)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (lt_min (div_pos one_pos (by positivity))
      (div_pos one_pos hPpos))
  have hεδ : ε ≤ δ / 2 := by rw [hεdef]; exact min_le_left _ _
  have hεM : ε ≤ 1 / (8 * (‖u 0‖ + 1)) := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεP : ε ≤ 1 / P := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set K : ℝ := 2 * ‖σ‖ * L / (Real.pi * ‖α‖) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : 0 ≤ 2 * ‖σ‖ * L / (Real.pi * ‖α‖) := by positivity
    linarith
  refine ⟨ε, K, hεpos, hKpos, ?_⟩
  intro z hz
  set τ : ℂ := tauC σ α z with hτdef
  have hτ_le : ‖τ‖ ≤ ε := by rw [hτdef]; exact hz
  have hτδ : ‖τ‖ < δ := by linarith [hτ_le, hεδ, hδpos]
  have huclose : ‖u τ - u 0‖ < η := by
    have h := hδ (x := τ) (by rw [dist_eq_norm, sub_zero]; exact hτδ)
    rwa [dist_eq_norm] at h
  have huclose1 : ‖u τ - u 0‖ < 1 := lt_of_lt_of_le huclose hη1
  have hucloseP : ‖u τ - u 0‖ < 1 / P := lt_of_lt_of_le huclose hηP
  have huτ_le : ‖u τ‖ ≤ ‖u 0‖ + 1 := by
    have h2 : ‖u τ‖ ≤ ‖u 0‖ + ‖u τ - u 0‖ := by
      simpa using norm_add_le (u 0) (u τ - u 0)
    linarith
  have hτu_bound : ‖τ * u τ‖ ≤ (‖u 0‖ + 1) * ‖τ‖ := by
    rw [norm_mul]
    calc ‖τ‖ * ‖u τ‖ ≤ ‖τ‖ * (‖u 0‖ + 1) :=
          mul_le_mul_of_nonneg_left huτ_le (norm_nonneg τ)
      _ = (‖u 0‖ + 1) * ‖τ‖ := by ring
  have hτu_le : ‖τ * u τ‖ ≤ 1 / 8 := by
    have hpos : 0 < ‖u 0‖ + 1 := by positivity
    have h8 : ε * (‖u 0‖ + 1) ≤ 1 / 8 := by
      have h := mul_le_mul_of_nonneg_right hεM (le_of_lt hpos)
      have he : 1 / (8 * (‖u 0‖ + 1)) * (‖u 0‖ + 1) = 1 / 8 := by
        field_simp
      linarith [h, he.ge, he.le]
    calc ‖τ * u τ‖ ≤ (‖u 0‖ + 1) * ‖τ‖ := hτu_bound
      _ ≤ (‖u 0‖ + 1) * ε := mul_le_mul_of_nonneg_left hτ_le (le_of_lt hpos)
      _ = ε * (‖u 0‖ + 1) := by ring
      _ ≤ 1 / 8 := h8
  have h1τu_ne : 1 + τ * u τ ≠ 0 := one_add_ne_zero_of_norm_lt_one (by linarith)
  have h1τu_norm : 3 / 4 ≤ ‖1 + τ * u τ‖ := by
    have h := norm_add_le ((1 : ℂ) + τ * u τ) (-(τ * u τ))
    have h' : (1 : ℝ) ≤ ‖(1 : ℂ) + τ * u τ‖ + ‖-(τ * u τ)‖ := by simpa using h
    rw [norm_neg] at h'
    linarith
  -- the error term `E`
  set E : ℂ := σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ)) with hEdef
  have hsfun : sfun u σ α z = σ * u τ / (1 + τ * u τ) := by
    simp only [sfun]
    rw [← hτdef]
  have hident : 1 - sfun u σ α z = A * (1 + E) := by
    rw [hsfun, hEdef]
    exact sfun_factor hA_ne h1τu_ne hσuA
  have hnum_le : ‖u 0 - u τ + u 0 * (τ * u τ)‖ ≤ L * (‖u τ - u 0‖ + ‖τ‖) := by
    have h1 : ‖u 0 * (τ * u τ)‖ ≤ ‖u 0‖ * ((‖u 0‖ + 1) * ‖τ‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hτu_bound (norm_nonneg (u 0))
    have h4 : (‖u 0‖ * (‖u 0‖ + 1)) * ‖τ‖ ≤ L * ‖τ‖ :=
      mul_le_mul_of_nonneg_right hLge (norm_nonneg τ)
    have h6 : ‖u τ - u 0‖ ≤ L * ‖u τ - u 0‖ := by
      have h := mul_le_mul_of_nonneg_right hL1 (norm_nonneg (u τ - u 0))
      rwa [one_mul] at h
    calc ‖u 0 - u τ + u 0 * (τ * u τ)‖
        ≤ ‖u 0 - u τ‖ + ‖u 0 * (τ * u τ)‖ := norm_add_le _ _
      _ ≤ ‖u τ - u 0‖ + ‖u 0‖ * ((‖u 0‖ + 1) * ‖τ‖) :=
            add_le_add (le_of_eq (norm_sub_rev (u 0) (u τ))) h1
      _ = ‖u τ - u 0‖ + (‖u 0‖ * (‖u 0‖ + 1)) * ‖τ‖ := by ring
      _ ≤ L * ‖u τ - u 0‖ + L * ‖τ‖ := add_le_add h6 h4
      _ = L * (‖u τ - u 0‖ + ‖τ‖) := by ring
  have hnum_sigma : ‖σ * (u 0 - u τ + u 0 * (τ * u τ))‖
      ≤ ‖σ‖ * (L * (‖u τ - u 0‖ + ‖τ‖)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hnum_le (norm_nonneg σ)
  have hE_den : (3 / 8 : ℝ) ≤ ‖A * (1 + τ * u τ)‖ := by
    rw [norm_mul]
    have h := mul_le_mul hA_norm h1τu_norm (by norm_num : (0 : ℝ) ≤ 3 / 4) (norm_nonneg A)
    linarith
  have hE_bound : ‖E‖ ≤ (8 / 3) * ‖σ‖ * L * (‖u τ - u 0‖ + ‖τ‖) := by
    rw [hEdef, norm_div]
    have hN : 0 ≤ ‖σ‖ * (L * (‖u τ - u 0‖ + ‖τ‖)) := by positivity
    have h := div_le_div₀ hN hnum_sigma (by norm_num : (0 : ℝ) < 3 / 8) hE_den
    have hq : ‖σ‖ * (L * (‖u τ - u 0‖ + ‖τ‖)) / (3 / 8)
        = (8 / 3) * ‖σ‖ * L * (‖u τ - u 0‖ + ‖τ‖) := by ring
    rwa [hq] at h
  have hAB : ‖u τ - u 0‖ + ‖τ‖ ≤ 2 * (1 / P) := by
    have h2 : ‖τ‖ ≤ 1 / P := le_trans hτ_le hεP
    linarith [le_of_lt hucloseP]
  have hE_half : ‖E‖ ≤ 1 / 2 := by
    have hcoef : (8 / 3 : ℝ) * ‖σ‖ * L * (2 * (1 / P)) = ‖σ‖ * L / (3 * (‖σ‖ * L + 1)) := by
      rw [hPdef]; field_simp; ring
    calc ‖E‖ ≤ (8 / 3) * ‖σ‖ * L * (‖u τ - u 0‖ + ‖τ‖) := hE_bound
      _ ≤ (8 / 3) * ‖σ‖ * L * (2 * (1 / P)) := mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = ‖σ‖ * L / (3 * (‖σ‖ * L + 1)) := hcoef
      _ ≤ 1 / 2 := by
            rw [div_le_iff₀ (by positivity)]
            linarith [mul_nonneg (norm_nonneg σ) (le_of_lt hLpos)]
  have hE_re : 0 < (1 + E).re := by
    have h := Complex.abs_re_le_norm E
    rw [abs_le] at h
    simp only [Complex.add_re, Complex.one_re]
    linarith [h.1, hE_half]
  have hA_re_pos : 0 < A.re := lt_of_lt_of_le (by norm_num) hA_re
  have hlog1 : Complex.log (1 - sfun u σ α z) = Complex.log A + Complex.log (1 + E) := by
    rw [hident]
    exact log_mul_of_re_pos hA_re_pos hE_re
  have hne : (2 * Real.pi * I * α : ℂ) ≠ 0 := by
    have h : 0 < ‖(2 * Real.pi * I * α : ℂ)‖ := by
      rw [hw_norm]
      exact mul_pos (by linarith [Real.pi_pos]) hαpos
    exact norm_pos_iff.mp h
  have hmain : liftF u σ α z - (z + 1)
      = (1 / (2 * Real.pi * I * α : ℂ)) * Complex.log (1 + E) := by
    simp only [liftF]
    rw [hlog1, hlog_exp, mul_add, div_mul_cancel₀ 1 hne]
    ring
  have hlogbound : ‖Complex.log (1 + E)‖ ≤ (3 / 2) * ‖E‖ :=
    Complex.norm_log_one_add_half_le_self hE_half
  have h2pn : 0 < 2 * Real.pi * ‖α‖ := mul_pos (by linarith [Real.pi_pos]) hαpos
  have hfinal : ‖liftF u σ α z - (z + 1)‖ ≤ K * (‖u τ - u 0‖ + ‖τ‖) := by
    calc ‖liftF u σ α z - (z + 1)‖
        = ‖(1 / (2 * Real.pi * I * α : ℂ)) * Complex.log (1 + E)‖ := by rw [hmain]
      _ = ‖1 / (2 * Real.pi * I * α : ℂ)‖ * ‖Complex.log (1 + E)‖ := norm_mul _ _
      _ = (1 / (2 * Real.pi * ‖α‖)) * ‖Complex.log (1 + E)‖ := by
            rw [norm_div, norm_one, hw_norm]
      _ ≤ (1 / (2 * Real.pi * ‖α‖)) * ((3 / 2) * ‖E‖) :=
            mul_le_mul_of_nonneg_left hlogbound (by positivity)
      _ ≤ (1 / (2 * Real.pi * ‖α‖)) * ((3 / 2) * ((8 / 3) * ‖σ‖ * L
              * (‖u τ - u 0‖ + ‖τ‖))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE_bound (by norm_num))
              (by positivity)
      _ = (2 * ‖σ‖ * L / (Real.pi * ‖α‖)) * (‖u τ - u 0‖ + ‖τ‖) := by
            field_simp
            ring
      _ ≤ K * (‖u τ - u 0‖ + ‖τ‖) := by
            have hc : 2 * ‖σ‖ * L / (Real.pi * ‖α‖) ≤ K := by
              rw [hKdef]; linarith
            exact mul_le_mul_of_nonneg_right hc (by positivity)
  exact hfinal

end

end Work.Pert
