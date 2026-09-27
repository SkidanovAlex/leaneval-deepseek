import Mathlib
import Submission.Work.Drive.polarParam

noncomputable section

namespace Work.Drive

/-- `arg (r · e^{iθ}) = θ` for `r > 0` and `θ ∈ (-π, π]`. -/
lemma arg_ofReal_mul_exp_mul_I {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg ((r : ℂ) * Complex.exp (θ * Complex.I)) = θ := by
  rw [Complex.exp_ofReal_mul_I, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_mul_cos_add_sin_mul_I hr hθ]

/-- `‖r · e^{iθ}‖ = r` for `r > 0`. -/
lemma norm_ofReal_mul_exp_mul_I {r θ : ℝ} (hr : 0 < r) :
    ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
    abs_of_pos hr]

/-- `im (r · e^{iθ}) = r sin θ`. -/
lemma im_ofReal_mul_exp_mul_I {r θ : ℝ} :
    ((r : ℂ) * Complex.exp (θ * Complex.I)).im = r * Real.sin θ := by
  have h : (r : ℂ) * Complex.exp (θ * Complex.I)
      = ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]; push_cast; ring
  rw [h]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

/-- **Uniqueness of the polar parametrisation of the closed disk**: the pair `(t, σ) ∈ [0,1) × [0,1]`
with `z = (1 - 2σ) · e^{iπt}` is `(dirParam z, radParam z)`. -/
theorem polarParam_unique {z : ℂ} (hz : z ≠ 0) {t σ : ℝ} (ht : t ∈ Set.Ico 0 1)
    (hσ : σ ∈ Set.Icc 0 1)
    (h : ((1 - 2 * σ : ℝ) : ℂ) * Complex.exp (Real.pi * ((t : ℝ) : ℂ) * Complex.I) = z) :
    t = Work.Drive.dirParam z ∧ σ = Work.Drive.radParam z := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t < 1 := ht.2
  set θ : ℝ := Real.pi * t with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθπ : θ < Real.pi := by rw [hθdef]; nlinarith [Real.pi_pos]
  have hθmem : θ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, hθπ.le⟩
  set w : ℝ := 1 - 2 * σ with hwdef
  have hσeq : σ = (1 - w) / 2 := by rw [hwdef]; ring
  have hw : (w : ℂ) * Complex.exp (θ * Complex.I) = z := by
    have h1 : Complex.exp (θ * Complex.I) = Complex.exp (Real.pi * ((t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      rw [show θ = Real.pi * t from hθdef]
      push_cast
      ring
    rw [h1, h]
  rcases lt_trichotomy w 0 with hwneg | hwzero | hwpos
  · -- the signed radius exceeds `1/2`: `arg z` is `θ - π` (or `π` when `θ = 0`)
    have hnorm : ‖z‖ = -w := by
      rw [← hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
        mul_one, abs_of_neg hwneg]
    rcases eq_or_lt_of_le ht0 with ht_eq | ht_pos
    · -- `t = 0`: then `z` is a negative real number
      have hθz : θ = 0 := by rw [hθdef, ← ht_eq, mul_zero]
      have hzy : z = (w : ℂ) := by
        rw [← hw, hθz]; simp
      have hargz : Complex.arg z = Real.pi := by
        rw [hzy]; exact Complex.arg_ofReal_of_neg hwneg
      have hdir : t = dirParam z := by
        rw [← ht_eq, dirParam, if_pos hargz]
      have hrad : σ = radParam z := by
        rw [radParam, if_pos hargz, hnorm]
        exact hσeq
      exact ⟨hdir, hrad⟩
    · -- `0 < t`: `arg z = θ - π`
      have hθpos : 0 < θ := by rw [hθdef]; exact mul_pos Real.pi_pos ht_pos
      have hvpos : (0 : ℝ) < -w := neg_pos.mpr hwneg
      have hzy : z = -(((-w : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) := by
        rw [← hw]; push_cast; ring
      have hargy : Complex.arg (((-w : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) = θ :=
        arg_ofReal_mul_exp_mul_I hvpos hθmem
      have hyim : 0 < (((-w : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im := by
        rw [im_ofReal_mul_exp_mul_I]
        exact mul_pos hvpos (Real.sin_pos_of_pos_of_lt_pi hθpos hθπ)
      have hargz : Complex.arg z = θ - Real.pi := by
        rw [hzy, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hyim, hargy]
      have hne : Complex.arg z ≠ Real.pi := by
        rw [hargz]; intro hc; linarith
      have hnn : ¬ (0 ≤ Complex.arg z) := by
        rw [hargz]; intro hc; linarith
      have hdir : t = dirParam z := by
        rw [dirParam, if_neg hne, if_neg hnn, hargz, hθdef]
        field_simp
        ring
      have hrad : σ = radParam z := by
        rw [radParam, if_neg hne, if_neg hnn, hnorm]
        exact hσeq
      exact ⟨hdir, hrad⟩
  · -- `σ = 1/2` is impossible since `z ≠ 0`
    rw [hwzero, Complex.ofReal_zero, zero_mul] at hw
    exact absurd hw.symm hz
  · -- the signed radius is less than `1/2`: `arg z = θ ∈ [0, π)`
    have hnorm : ‖z‖ = w := by
      rw [← hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
        mul_one, abs_of_pos hwpos]
    have hargz : Complex.arg z = θ := by
      rw [← hw]
      exact arg_ofReal_mul_exp_mul_I hwpos hθmem
    have hne : Complex.arg z ≠ Real.pi := by
      rw [hargz]; exact ne_of_lt hθπ
    have hnn : 0 ≤ Complex.arg z := by
      rw [hargz]; exact hθ0
    have hdir : t = dirParam z := by
      rw [dirParam, if_neg hne, if_pos hnn, hargz, hθdef]
      exact (mul_div_cancel_left₀ t Real.pi_ne_zero).symm
    have hrad : σ = radParam z := by
      rw [radParam, if_neg hne, if_pos hnn, hnorm]
      exact hσeq
    exact ⟨hdir, hrad⟩

end Work.Drive
