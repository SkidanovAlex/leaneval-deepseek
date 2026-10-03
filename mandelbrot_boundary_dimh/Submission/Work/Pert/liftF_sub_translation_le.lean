import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.liftF_sub_translation_le`

The "translation by `1`" error of the lift `F_f = liftF u σ α` at the **upper end**, in the
*Lipschitz* form of `NOTES_liftF_upper.md` §2 ("Piece B"): if `u` is bounded by `1/2` below and
by `2` above and is `C`-Lipschitz on `ball 0 r`, and if the normalisation
`1 - σ u 0 = exp (2πiα)` holds with `0 < ‖α‖ ≤ 1/64`, then for `‖τ_f z‖` small enough
there is `K > 0` with

    ‖liftF u σ α z - (z + 1)‖ ≤ K ‖τ_f z‖ ,

namely `K = 16 (C + 4)`.

The proof is the exact algebraic computation behind (A.1.7)/(4.2.x).  Writing
`A = exp (2πiα) = 1 - σ u 0`, `τ = τ_f z` and

    E = σ (u 0 - u τ + u 0 (τ u τ)) / (A (1 + τ u τ)) ,

one has the identity `1 - s = A (1 + E)` with `s = σ u τ / (1 + τ u τ) = sfun u σ α z`, and
`log A = 2πiα` for the principal branch (because `‖α‖ ≤ 1/64`), so that

    liftF u σ α z - (z + 1) = (2πiα)⁻¹ log (1 + E) .

Everything is then bounded using `‖u 0 - u τ‖ ≤ C ‖τ‖`, `1/2 ≤ ‖u‖ ≤ 2` and the crude
`‖σ‖ ≤ 8π ‖α‖` that follows from the normalisation.

Note: the statement (unchanged, verbatim from the interface) writes the imaginary unit as the
bare `I`; the `open Complex` below is what makes it resolve to `Complex.I` under
`autoImplicit = false` (as used by `lake build`).  No hypothesis or conclusion is altered.
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

theorem liftF_sub_translation_le {u : ℂ → ℂ} {σ α : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hu2 : ∀ z ∈ Metric.ball 0 r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huL : ∀ z ∈ Metric.ball 0 r, ∀ w ∈ Metric.ball 0 r, ‖u z - u w‖ ≤ C * ‖z - w‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hαne : α ≠ 0) (hαsmall : ‖α‖ ≤ 1 / 64) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ z : ℂ,
      ‖Work.Pert.tauC σ α z‖ ≤ ε →
        ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ K * ‖Work.Pert.tauC σ α z‖ := by
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
  have hσ_norm : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
    have h0mem : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
    have hu0 : 1 / 2 ≤ ‖u 0‖ := (hu2 0 h0mem).1
    have h1 : ‖σ‖ * (1 / 2) ≤ ‖σ * u 0‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
    rw [hσu, norm_sub_rev] at h1
    linarith [h1, hAnorm_sub]
  -- the smallness threshold `ε` and the constant `K`
  have hσ1pos : 0 < ‖σ‖ + 1 := by positivity
  have hC4pos : 0 < C + 4 := by linarith
  have hDpos : 0 < 16 * (‖σ‖ + 1) * (C + 4) :=
    mul_pos (mul_pos (by norm_num) hσ1pos) hC4pos
  set ε : ℝ := min (r / 2) (min (1 / 8) (1 / (16 * (‖σ‖ + 1) * (C + 4)))) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (lt_min (by norm_num) (div_pos one_pos hDpos))
  have hεr : ε ≤ r / 2 := by rw [hεdef]; exact min_le_left _ _
  have hε8 : ε ≤ 1 / 8 := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεD : ε ≤ 1 / (16 * (‖σ‖ + 1) * (C + 4)) := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hKpos : 0 < 16 * (C + 4) := mul_pos (by norm_num) hC4pos
  refine ⟨ε, 16 * (C + 4), hεpos, hKpos, ?_⟩
  intro z hz
  set τ : ℂ := tauC σ α z with hτdef
  have hτ_le : ‖τ‖ ≤ ε := by rw [hτdef]; exact hz
  have hτ_lt : ‖τ‖ < r := by linarith [hτ_le, hεr, hr]
  have hτmem : τ ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hτ_lt
  have h0mem : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hu0hi : ‖u 0‖ ≤ 2 := (hu2 0 h0mem).2
  have huτhi : ‖u τ‖ ≤ 2 := (hu2 τ hτmem).2
  have huLip : ‖u 0 - u τ‖ ≤ C * ‖τ‖ := by
    have h := huL 0 h0mem τ hτmem
    simpa using h
  have hτu_le : ‖τ * u τ‖ ≤ 2 * ε := by
    rw [norm_mul]
    have h := mul_le_mul hτ_le huτhi (norm_nonneg (u τ)) (le_of_lt hεpos)
    linarith
  have h2ε : 2 * ε ≤ 1 / 4 := by linarith [hε8]
  have h1τu_ne : 1 + τ * u τ ≠ 0 := by
    refine one_add_ne_zero_of_norm_lt_one ?_
    linarith
  have h1τu_norm : 3 / 4 ≤ ‖1 + τ * u τ‖ := by
    have h := norm_add_le ((1 : ℂ) + τ * u τ) (-(τ * u τ))
    have h' : (1 : ℝ) ≤ ‖(1 : ℂ) + τ * u τ‖ + ‖-(τ * u τ)‖ := by simpa using h
    rw [norm_neg] at h'
    linarith [h', hτu_le, h2ε]
  -- the error term `E`
  set E : ℂ := σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ)) with hEdef
  have hsfun : sfun u σ α z = σ * u τ / (1 + τ * u τ) := by
    simp only [sfun]
    rw [← hτdef]
  have hident : 1 - sfun u σ α z = A * (1 + E) := by
    rw [hsfun, hEdef]
    exact sfun_factor hA_ne h1τu_ne hσuA
  have hu0τu : ‖u 0 * (τ * u τ)‖ ≤ 2 * (2 * ‖τ‖) := by
    have hτu : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
      rw [norm_mul]
      calc ‖τ‖ * ‖u τ‖ = ‖u τ‖ * ‖τ‖ := by ring
        _ ≤ 2 * ‖τ‖ := mul_le_mul_of_nonneg_right huτhi (norm_nonneg τ)
    rw [norm_mul]
    exact mul_le_mul hu0hi hτu (norm_nonneg _) (by norm_num)
  have hE_num : ‖σ * (u 0 - u τ + u 0 * (τ * u τ))‖ ≤ ‖σ‖ * ((C + 4) * ‖τ‖) := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg σ)
    calc ‖u 0 - u τ + u 0 * (τ * u τ)‖
        ≤ ‖u 0 - u τ‖ + ‖u 0 * (τ * u τ)‖ := norm_add_le _ _
      _ ≤ C * ‖τ‖ + 2 * (2 * ‖τ‖) := add_le_add huLip hu0τu
      _ = (C + 4) * ‖τ‖ := by ring
  have hE_den : (3 / 8 : ℝ) ≤ ‖A * (1 + τ * u τ)‖ := by
    rw [norm_mul]
    have h := mul_le_mul hA_norm h1τu_norm (by norm_num : (0 : ℝ) ≤ 3 / 4) (norm_nonneg A)
    linarith
  have hE_bound : ‖E‖ ≤ (8 / 3) * ‖σ‖ * (C + 4) * ‖τ‖ := by
    rw [hEdef, norm_div]
    have hN : 0 ≤ ‖σ‖ * ((C + 4) * ‖τ‖) :=
      mul_nonneg (norm_nonneg σ) (mul_nonneg (by linarith) (norm_nonneg τ))
    have h := div_le_div₀ hN hE_num (by norm_num : (0 : ℝ) < 3 / 8) hE_den
    refine le_trans h (le_of_eq ?_)
    field_simp
  have hE_half : ‖E‖ ≤ 1 / 2 := by
    have hkey : (8 / 3 : ℝ) * ‖σ‖ * (C + 4) * (1 / (16 * (‖σ‖ + 1) * (C + 4)))
        = ‖σ‖ / (6 * (‖σ‖ + 1)) := by
      field_simp
      ring
    have hmono : (8 / 3) * ‖σ‖ * (C + 4) * ε
        ≤ (8 / 3) * ‖σ‖ * (C + 4) * (1 / (16 * (‖σ‖ + 1) * (C + 4))) :=
      mul_le_mul_of_nonneg_left hεD (by positivity)
    have hle : ‖σ‖ / (6 * (‖σ‖ + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [norm_nonneg σ]
    calc ‖E‖ ≤ (8 / 3) * ‖σ‖ * (C + 4) * ‖τ‖ := hE_bound
      _ ≤ (8 / 3) * ‖σ‖ * (C + 4) * ε :=
            mul_le_mul_of_nonneg_left hτ_le (by positivity)
      _ ≤ (8 / 3) * ‖σ‖ * (C + 4) * (1 / (16 * (‖σ‖ + 1) * (C + 4))) := hmono
      _ = ‖σ‖ / (6 * (‖σ‖ + 1)) := hkey
      _ ≤ 1 / 2 := hle
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
  have hpn : 0 < Real.pi * ‖α‖ := mul_pos Real.pi_pos hαpos
  have h2pn : 0 < 2 * Real.pi * ‖α‖ := mul_pos (by linarith [Real.pi_pos]) hαpos
  have hnn : 0 ≤ (C + 4) * ‖τ‖ := mul_nonneg (by linarith) (norm_nonneg τ)
  have hfinal : ‖liftF u σ α z - (z + 1)‖ ≤ 16 * (C + 4) * ‖τ‖ := by
    calc ‖liftF u σ α z - (z + 1)‖
        = ‖(1 / (2 * Real.pi * I * α : ℂ)) * Complex.log (1 + E)‖ := by rw [hmain]
      _ = ‖1 / (2 * Real.pi * I * α : ℂ)‖ * ‖Complex.log (1 + E)‖ := norm_mul _ _
      _ = (1 / (2 * Real.pi * ‖α‖)) * ‖Complex.log (1 + E)‖ := by
            rw [norm_div, norm_one, hw_norm]
      _ ≤ (1 / (2 * Real.pi * ‖α‖)) * ((3 / 2) * ‖E‖) :=
            mul_le_mul_of_nonneg_left hlogbound (le_of_lt (div_pos one_pos h2pn))
      _ ≤ (1 / (2 * Real.pi * ‖α‖)) * ((3 / 2) * ((8 / 3) * ‖σ‖ * (C + 4) * ‖τ‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE_bound (by norm_num))
              (le_of_lt (div_pos one_pos h2pn))
      _ = ((2 * ‖σ‖) / (Real.pi * ‖α‖)) * ((C + 4) * ‖τ‖) := by
            field_simp
            ring
      _ ≤ 16 * ((C + 4) * ‖τ‖) := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            rw [div_le_iff₀ hpn]
            linarith [hσ_norm]
      _ = 16 * (C + 4) * ‖τ‖ := by ring
  simpa only [← hτdef] using hfinal

end

end Work.Pert
