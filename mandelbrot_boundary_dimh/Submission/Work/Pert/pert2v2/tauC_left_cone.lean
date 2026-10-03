import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# `Work.Pert.pert2v2.tauC_left_cone`

`τ_f(w) = σ / (1 - e^{-2πiαw})` (`Work.Pert.tauC`) satisfies the *left–cone* condition

  `Re τ ≤ 0`  and  `‖τ‖ ≤ -2 Re τ`

for every `w` with `1 ≤ Re w`, `|Im w| ≤ Re w / 2` and `2π‖α‖(‖w‖+1) ≤ 1/32`, as long as the
normal–form data satisfy `1 - σ u(0) = exp(2πi α)` with `‖u(0) - 1‖ ≤ 1/16`.

The mechanism is the classical expansion `τ ≈ -1/w`: with `a = 2πi α`,

  `τ = ((1 - e^a)/(1 - e^{-aw}))/u(0)`  and  `‖w·τ + 1‖ ≤ 2/15`,

so `τ` is an `O(1/‖w‖)`–perturbation of `-1/w`, which lies strictly inside the cone
`‖τ‖ ≤ -2 Re τ` because `|Im w| ≤ Re w/2` (the cone boundary has slope `√3`, and `√3 > 1/2`
with room to spare).

`model_close` is the analytic step (the quadratic Taylor residual `e^x - 1 - x = O(x²)` of the
exponential), `cone_of_close` is the geometric step.
-/

namespace Work.Pert.pert2v2

open Complex

noncomputable section

/-- **Model step (analytic).**  For `a = 2πiα`, the model coordinate `(1 - e^a)/(1 - e^{-aw})`
differs from `-1/w` by at most `1/16` *relative*: `‖(1 - e^a)/(1 - e^{-aw})·w + 1‖ ≤ 1/16`.

Writing `g(z) = e^z - 1 - z` (`‖g z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1`), the numerator
`w(1 - e^a) + (1 - e^{-aw}) = -(w·g a + g(-aw))` is bounded by
`‖a‖²‖w‖(1+‖w‖) ≤ ‖a‖(‖w‖+1)·‖a‖‖w‖ ≤ (1/32)‖a‖‖w‖`, while the denominator satisfies
`‖1 - e^{-aw}‖ ≥ ‖aw‖ - ‖aw‖² ≥ ‖aw‖/2`; the quotient is `≤ 1/16`. -/
private theorem model_close {a w : ℂ} (ha : ‖a‖ * (‖w‖ + 1) ≤ 1 / 32)
    (hQ : Complex.exp (-(a * w)) ≠ 1) :
    ‖(1 - Complex.exp a) / (1 - Complex.exp (-(a * w))) * w + 1‖ ≤ 1 / 16 := by
  have haw : ‖a‖ * ‖w‖ ≤ 1 / 32 := by nlinarith [ha, norm_nonneg a, norm_nonneg w]
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [ha, norm_nonneg a, norm_nonneg w]
  have hga : ‖Complex.exp a - 1 - a‖ ≤ ‖a‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le ha1
  have hgb : ‖Complex.exp (-(a * w)) - 1 - (-(a * w))‖ ≤ ‖a‖ ^ 2 * ‖w‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -(a * w))
      (by rw [norm_neg, norm_mul]; linarith [haw, norm_nonneg a, norm_nonneg w])
    rwa [norm_neg, norm_mul, mul_pow] at h
  have hnum : w * (1 - Complex.exp a) + (1 - Complex.exp (-(a * w)))
      = -(w * (Complex.exp a - 1 - a)
          + (Complex.exp (-(a * w)) - 1 - (-(a * w)))) := by ring
  have hN : ‖w * (1 - Complex.exp a) + (1 - Complex.exp (-(a * w)))‖
      ≤ (1 / 32) * (‖a‖ * ‖w‖) := by
    rw [hnum, norm_neg]
    calc ‖w * (Complex.exp a - 1 - a)
            + (Complex.exp (-(a * w)) - 1 - (-(a * w)))‖
        ≤ ‖w * (Complex.exp a - 1 - a)‖
            + ‖Complex.exp (-(a * w)) - 1 - (-(a * w))‖ := norm_add_le _ _
      _ ≤ ‖w‖ * ‖a‖ ^ 2 + ‖a‖ ^ 2 * ‖w‖ ^ 2 := by
          apply add_le_add
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_left hga (norm_nonneg w)
          · exact hgb
      _ = (‖a‖ * (‖w‖ + 1)) * (‖a‖ * ‖w‖) := by ring
      _ ≤ (1 / 32) * (‖a‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_right ha (by positivity)
  have hD : (1 / 2) * (‖a‖ * ‖w‖) ≤ ‖1 - Complex.exp (-(a * w))‖ := by
    have hX : 0 ≤ ‖a‖ * ‖w‖ := mul_nonneg (norm_nonneg a) (norm_nonneg w)
    have h4 : ‖a‖ ^ 2 * ‖w‖ ^ 2 ≤ (1 / 32) * (‖a‖ * ‖w‖) := by
      rw [← mul_pow]
      nlinarith [haw, hX]
    have h1 : ‖a * w‖ ≤ ‖Complex.exp (-(a * w)) - 1‖
        + ‖Complex.exp (-(a * w)) - 1 - (-(a * w))‖ := by
      calc ‖a * w‖ = ‖-(a * w)‖ := (norm_neg _).symm
        _ = ‖(Complex.exp (-(a * w)) - 1)
              - (Complex.exp (-(a * w)) - 1 - (-(a * w)))‖ := by
              congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖a * w‖ - ‖a‖ ^ 2 * ‖w‖ ^ 2 ≤ ‖Complex.exp (-(a * w)) - 1‖ := by
      linarith [h1, hgb]
    rw [norm_mul] at h2
    rw [norm_sub_rev]
    nlinarith [h2, h4, hX]
  have hDne : (1 : ℂ) - Complex.exp (-(a * w)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hQ)
  have hDpos : 0 < ‖1 - Complex.exp (-(a * w))‖ := by
    rw [norm_pos_iff]; exact hDne
  have hid : (1 - Complex.exp a) / (1 - Complex.exp (-(a * w))) * w + 1
      = (w * (1 - Complex.exp a) + (1 - Complex.exp (-(a * w))))
        / (1 - Complex.exp (-(a * w))) := by
    field_simp
  rw [hid, norm_div, div_le_iff₀ hDpos]
  calc ‖w * (1 - Complex.exp a) + (1 - Complex.exp (-(a * w)))‖
      ≤ (1 / 32) * (‖a‖ * ‖w‖) := hN
    _ = (1 / 16) * ((1 / 2) * (‖a‖ * ‖w‖)) := by ring
    _ ≤ (1 / 16) * ‖1 - Complex.exp (-(a * w))‖ :=
        mul_le_mul_of_nonneg_left hD (by norm_num)

/-- **Cone step (geometric).**  If `w` lies in the sector `Re w ≥ 1`, `|Im w| ≤ Re w/2` and
`‖w τ + 1‖ ≤ 2/15`, then `τ` lies in the left cone `Re τ ≤ 0`, `‖τ‖ ≤ -2 Re τ`.

With `θ = wτ + 1` (`‖θ‖ ≤ 2/15`) and `x = Re w`, `y = Im w`, `n = ‖w‖²` one has
`τ.re·n = (θ.re-1)x + θ.im·y` and `τ.im·n = θ.im·x - (θ.re-1)y`; since `13/15 ≤ 1 - θ.re`,
`|θ.re-1| ≤ 17/15`, `|θ.im| ≤ 2/15` and `|y| ≤ x/2`, this gives `(-τ.re)·n ≥ (4/5)x` and
`|τ.im|·n ≤ (7/10)x`, hence `|τ.im| ≤ (7/8)(-τ.re) ≤ √3(-τ.re)` and `τ.re < 0`; the cone
inequality `‖τ‖ ≤ -2 Re τ` follows. -/
private theorem cone_of_close {τ w : ℂ} (hre : 1 ≤ w.re) (him : |w.im| ≤ w.re / 2)
    (h : ‖w * τ + 1‖ ≤ 2 / 15) : τ.re ≤ 0 ∧ ‖τ‖ ≤ -2 * τ.re := by
  have hwne : w ≠ 0 := by
    intro hh
    rw [hh] at hre
    norm_num at hre
  have hnpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hwne
  set θ : ℂ := w * τ + 1 with hθ
  have hθn : ‖θ‖ ≤ 2 / 15 := h
  have hθre_abs : |θ.re| ≤ 2 / 15 := le_trans (Complex.abs_re_le_norm θ) hθn
  have hθim_abs : |θ.im| ≤ 2 / 15 := le_trans (Complex.abs_im_le_norm θ) hθn
  have hθre := abs_le.mp hθre_abs
  have hθim := abs_le.mp hθim_abs
  have hx : 0 < w.re := by linarith
  have hτeq : τ = (θ - 1) / w := by
    rw [hθ]; field_simp; ring
  have hTre : τ.re * Complex.normSq w = (θ.re - 1) * w.re + θ.im * w.im := by
    rw [hτeq, Complex.div_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    field_simp
  have hTim : τ.im * Complex.normSq w = θ.im * w.re - (θ.re - 1) * w.im := by
    rw [hτeq, Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    field_simp
  have hlow : (4 / 5) * w.re ≤ (-τ.re) * Complex.normSq w := by
    have h1 : (13 : ℝ) / 15 ≤ -(θ.re - 1) := by linarith [hθre.2]
    have h2 : θ.im * w.im ≤ w.re / 15 := by
      have h3 : θ.im * w.im ≤ |θ.im| * |w.im| := by
        rw [← abs_mul]; exact le_abs_self _
      have h4 : |θ.im| * |w.im| ≤ (2 / 15) * (w.re / 2) :=
        mul_le_mul hθim_abs him (abs_nonneg _) (by norm_num)
      linarith
    nlinarith [hTre, h1, h2, hx]
  have hhi : |τ.im| * Complex.normSq w ≤ (7 / 10) * w.re := by
    have hA : |θ.re - 1| ≤ 17 / 15 := by
      rw [abs_le]; constructor <;> linarith [hθre.1, hθre.2]
    calc |τ.im| * Complex.normSq w = |τ.im * Complex.normSq w| := by
          rw [abs_mul, abs_of_pos hnpos]
      _ = |θ.im * w.re - (θ.re - 1) * w.im| := by rw [hTim]
      _ ≤ |θ.im * w.re| + |(θ.re - 1) * w.im| := abs_sub _ _
      _ = |θ.im| * w.re + |θ.re - 1| * |w.im| := by
          rw [abs_mul, abs_mul, abs_of_pos hx]
      _ ≤ (2 / 15) * w.re + (17 / 15) * (w.re / 2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hθim_abs (le_of_lt hx)
          · exact mul_le_mul hA him (abs_nonneg _) (by norm_num)
      _ = (7 / 10) * w.re := by ring
  have hratio : |τ.im| ≤ (7 / 8) * (-τ.re) := by
    have h1 : Complex.normSq w * |τ.im| ≤ Complex.normSq w * ((7 / 8) * (-τ.re)) := by
      nlinarith [hlow, hhi]
    exact le_of_mul_le_mul_left h1 hnpos
  have hτre : τ.re ≤ 0 := by
    have hpos : 0 < (-τ.re) * Complex.normSq w := by nlinarith [hlow, hre]
    nlinarith [hpos, hnpos]
  refine ⟨hτre, ?_⟩
  have him2 : τ.im ^ 2 ≤ (49 / 64) * τ.re ^ 2 := by
    have h2 : |τ.im| ^ 2 ≤ ((7 / 8) * (-τ.re)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hratio 2
    rwa [sq_abs, mul_pow, show ((7 : ℝ) / 8) ^ 2 = 49 / 64 by norm_num, neg_sq] at h2
  have hsq : ‖τ‖ ^ 2 ≤ (-2 * τ.re) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [show (-2 * τ.re) ^ 2 = 4 * τ.re ^ 2 by ring]
    nlinarith [him2, sq_nonneg τ.re]
  have hfin := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg τ), abs_of_nonneg (by linarith : (0 : ℝ) ≤ -2 * τ.re)] at hfin

theorem tauC_left_cone {u : ℂ → ℂ} {σ α w : ℂ}
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu0 : ‖u 0 - 1‖ ≤ 1 / 16)
    (hα : 2 * Real.pi * ‖α‖ * (‖w‖ + 1) ≤ 1 / 32)
    (hre : 1 ≤ w.re) (him : |w.im| ≤ w.re / 2) :
    (Work.Pert.tauC σ α w).re ≤ 0 ∧
      ‖Work.Pert.tauC σ α w‖ ≤ -2 * (Work.Pert.tauC σ α w).re := by
  -- ### elementary facts about `u 0`
  have hu0ne : u 0 ≠ 0 := by
    intro h
    rw [h] at hu0
    norm_num at hu0
  have hu0norm : (15 : ℝ) / 16 ≤ ‖u 0‖ := by
    have h := abs_norm_sub_norm_le (u 0) (1 : ℂ)
    rw [norm_one] at h
    have h2 := (abs_le.mp h).1
    linarith
  -- ### the auxiliary `a = 2πi α` and its size
  set a : ℂ := 2 * Real.pi * Complex.I * α with ha
  have ha_norm : ‖a‖ = 2 * Real.pi * ‖α‖ := by
    rw [ha]
    simp only [norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hαa : ‖a‖ * (‖w‖ + 1) ≤ 1 / 32 := by rw [ha_norm]; exact hα
  rcases eq_or_ne (Complex.exp (-(a * w))) 1 with hQ1 | hQ1
  · -- degenerate case: the denominator of `τ_f` vanishes, so `τ_f = 0`
    have hτ0 : Work.Pert.tauC σ α w = 0 := by
      unfold Work.Pert.tauC
      have harg : -(2 * Real.pi * I * α * w) = -(a * w) := by rw [ha]
      rw [harg, hQ1]
      simp
    rw [hτ0]
    constructor <;> simp
  · -- main case: `τ_f = ((1 - e^a)/(1 - e^{-aw}))/u 0`
    have hnorm' : 1 - σ * u 0 = Complex.exp a := hnorm
    have hσ : σ = (1 - Complex.exp a) / u 0 := by
      rw [eq_div_iff hu0ne]
      rw [← hnorm']
      ring
    have hτ1 : Work.Pert.tauC σ α w
        = ((1 - Complex.exp a) / (1 - Complex.exp (-(a * w)))) / u 0 := by
      unfold Work.Pert.tauC
      have harg : -(2 * Real.pi * I * α * w) = -(a * w) := by rw [ha]
      rw [harg, hσ, div_div, div_div]
      congr 1
      ring
    have hu0inv : ‖(1 : ℂ) / u 0‖ ≤ 16 / 15 := by
      rw [norm_div, norm_one]
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15 / 16) hu0norm
      linarith
    have hu0diff : ‖1 - 1 / u 0‖ ≤ 1 / 15 := by
      have hrw : 1 - 1 / u 0 = (u 0 - 1) / u 0 := by field_simp
      rw [hrw, norm_div, div_le_iff₀ (by linarith : (0 : ℝ) < ‖u 0‖)]
      nlinarith [hu0, hu0norm]
    have hsplit : Work.Pert.tauC σ α w * w + 1
        = ((1 - Complex.exp a) / (1 - Complex.exp (-(a * w))) * w + 1) / u 0
          + (1 - 1 / u 0) := by
      rw [hτ1]
      field_simp
      ring
    have hmodel := model_close (a := a) (w := w) hαa hQ1
    have hbdry : ‖Work.Pert.tauC σ α w * w + 1‖ ≤ 2 / 15 := by
      rw [hsplit]
      calc ‖((1 - Complex.exp a) / (1 - Complex.exp (-(a * w))) * w + 1) / u 0
              + (1 - 1 / u 0)‖
          ≤ ‖((1 - Complex.exp a) / (1 - Complex.exp (-(a * w))) * w + 1) / u 0‖
              + ‖1 - 1 / u 0‖ := norm_add_le _ _
        _ ≤ 1 / 16 * (16 / 15) + 1 / 15 := by
            apply add_le_add
            · rw [div_eq_mul_one_div, norm_mul]
              exact mul_le_mul hmodel hu0inv (norm_nonneg _) (by norm_num)
            · exact hu0diff
        _ = 2 / 15 := by norm_num
    have hbdry' : ‖w * Work.Pert.tauC σ α w + 1‖ ≤ 2 / 15 := by
      rw [mul_comm]; exact hbdry
    exact cone_of_close hre him hbdry'

end

end Work.Pert.pert2v2
