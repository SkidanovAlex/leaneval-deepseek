import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.horiz_dev_le_clear
import Submission.Work.Pert.V5.horiz_dev_le_split
import Submission.Work.Pert.V5.corridor_piece_bound
import Submission.Work.Pert.V5.ceil_cover_norm_le
import Submission.Work.Pert.V5.walk_data
import Submission.Work.Pert.V5.vert_dev_le_of_margin
import Submission.Work.Pert.V5.horiz_dev_le_of_margin
import Submission.Work.Pert.V5.corridor_dev_affine
import Submission.Work.Pert.V5.clear_lattice_band
import Submission.Work.Pert.V5.clear_lattice_gate
import Submission.Work.Pert.V5.Assembly2
import Submission.Work.Pert.V5.corridor_left_cover
import Submission.Work.Pert.V5.corridor_left_long
import Submission.Work.Pert.V5.P_le_B_pin
import Submission.Work.Pert.V5.corridor_dev_linear
import Submission.Work.Pert.V5.crude_of_caseB
import Submission.Work.Pert.V5.fallback_clear_geom

/-!
# `Work.Pert.V5.corridor_left_wk` — the left corridor, weak form

The horizontal comparison between the band point `q = x + i y₀` (`x = z.re`, `y₀ = z₀.im`) and the
pin `z₀`, in the case `x ≤ x₀ = z₀.re`.  The file provides

* the elementary corridor data (`mgA_shift`, `mgB_shift`, `len_le`, `pin_le`; `pin_le` is the
  constraint `Ξ + 2 Rde ≤ M + 2 Kp (1+log(2+M))` forced by `z₀ ∈ Qm` with margin `> 2Rde+2`);
* the **lattice clearance of the gate** (`lattice_clear_gate_scaled`): every point of the gate is at
  distance `≥ (min (mgA) (mgB) + Ξ)/√2` from the lattice `(1/α)ℤ`, because `mgA`, `mgB` are
  `√2`-Lipschitz while each lattice point violates one of the two inequalities by `Ξ`.  Hence the
  cleared-piece lemmas apply as soon as the gate margin is `≥ 2^10 √2 - Ξ` (e.g. whenever `Ξ ≥ 2^10 √2`,
  or when the margin is `≥ 2^10` and `Ξ ≥ 0`);
* the **affine corridor bound** (`corridor_left_affine`): if the `b₁`-margin at the band end is
  `≥ √2 Rde` then the whole corridor has margin `≥ √2 Rde` and `corridor_dev_affine` yields
  `‖D q - D z₀‖ ≤ C₂ √2 (log (1 + ℓ/(√2 Rde)) + log (1 + ℓ/(2 Rde + 2))) + ℓ/31`,  `ℓ = x₀ - x`.
-/

namespace Work.Pert.V5

open Set Metric Filter
open scoped Topology

noncomputable section

/-! ## 0. Two elementary inequalities for `ℂ` -/

/-- `|re z| + |im z| ≤ √2 ‖z‖`. -/
lemma abs_re_add_abs_im_le_sqrt2_mul (z : ℂ) :
    |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hz : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg z), Complex.sq_norm, Complex.normSq_apply]
    ring_nf
  rw [hz]
  have h1 : (0:ℝ) ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  have hsq1 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq2 : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = z.re ^ 2 + z.im ^ 2 := Real.sq_sqrt h1
  have h2 : (0:ℝ) ≤ Real.sqrt 2 * Real.sqrt (z.re ^ 2 + z.im ^ 2) := by positivity
  refine le_of_sq_le_sq ?_ h2
  nlinarith [sq_nonneg (|z.re| - |z.im|), sq_abs z.re, sq_abs z.im, hsq1, hsq2]

/-- The `b₂`-marginal is `√2`-Lipschitz. -/
lemma abs_mgB_sub_le {Ξ : ℝ} (a b : ℂ) :
    |mgB Ξ a - mgB Ξ b| ≤ Real.sqrt 2 * ‖a - b‖ := by
  have h0 : mgB Ξ a - mgB Ξ b = (|a.im| - |b.im|) - (a.re - b.re) := by
    simp only [mgB]; ring
  have h1 : |a.im| - |b.im| ≤ |a.im - b.im| := abs_sub_abs_le_abs_sub a.im b.im
  have h2 : |b.im| - |a.im| ≤ |a.im - b.im| := by
    have h := abs_sub_abs_le_abs_sub b.im a.im
    rwa [abs_sub_comm] at h
  have h3 : |a.im - b.im| + |a.re - b.re| ≤ Real.sqrt 2 * ‖a - b‖ := by
    have := abs_re_add_abs_im_le_sqrt2_mul (a - b)
    simp only [Complex.sub_re, Complex.sub_im] at this
    linarith
  have hmid : |(|a.im| - |b.im|) - (a.re - b.re)| ≤ |a.im - b.im| + |a.re - b.re| := by
    have h4 : -|a.im - b.im| ≤ |a.im| - |b.im| := by linarith
    have h5 : -|a.re - b.re| ≤ -(a.re - b.re) := by
      rw [← abs_neg (a.re - b.re)]; exact neg_abs_le _
    have h6 : -(a.re - b.re) ≤ |a.re - b.re| := neg_le_abs _
    rw [abs_le]
    exact ⟨by linarith [h4, h5], by linarith [h1, h6]⟩
  rw [h0]
  exact le_trans hmid h3

/-- The `b₁`-marginal is `√2`-Lipschitz. -/
lemma abs_mgA_sub_le {Ξ : ℝ} {α : ℂ} (a b : ℂ) :
    |mgA Ξ α a - mgA Ξ α b| ≤ Real.sqrt 2 * ‖a - b‖ := by
  have h0 : mgA Ξ α a - mgA Ξ α b
      = (|a.im + (1/α).im| - |b.im + (1/α).im|) + (a.re - b.re) := by
    simp only [mgA]; ring
  have h1 : |a.im + (1/α).im| - |b.im + (1/α).im| ≤ |a.im - b.im| := by
    have h := abs_sub_abs_le_abs_sub (a.im + (1/α).im) (b.im + (1/α).im)
    have he : (a.im + (1/α).im) - (b.im + (1/α).im) = a.im - b.im := by ring
    rwa [he] at h
  have h3 : |a.im - b.im| + |a.re - b.re| ≤ Real.sqrt 2 * ‖a - b‖ := by
    have := abs_re_add_abs_im_le_sqrt2_mul (a - b)
    simp only [Complex.sub_re, Complex.sub_im] at this
    linarith
  have hmid : |(|a.im + (1/α).im| - |b.im + (1/α).im|) + (a.re - b.re)|
      ≤ |a.im - b.im| + |a.re - b.re| := by
    have h4 : -|a.im - b.im| ≤ |a.im + (1/α).im| - |b.im + (1/α).im| := by
      have h2 : |b.im + (1/α).im| - |a.im + (1/α).im| ≤ |a.im - b.im| := by
        have h := abs_sub_abs_le_abs_sub (b.im + (1/α).im) (a.im + (1/α).im)
        have he : (b.im + (1/α).im) - (a.im + (1/α).im) = b.im - a.im := by ring
        rw [he, abs_sub_comm] at h
        exact h
      linarith
    have h5 : -|a.re - b.re| ≤ a.re - b.re := neg_abs_le _
    have h6 : a.re - b.re ≤ |a.re - b.re| := le_abs_self _
    rw [abs_le]
    exact ⟨by linarith [h4, h5], by linarith [h1, h6]⟩
  rw [h0]
  exact le_trans hmid h3

/-- For `α ∈ 𝓕₁`: `|Im (1/α)| ≤ Re (1/α)`. -/
theorem im_inv_le_re_inv {α : ℂ} (h : MandelDim.InF1 α) : |(1 / α).im| ≤ (1 / α).re := by
  have hre : 0 < α.re := by have := abs_nonneg α.im; linarith [show |α.im| < α.re from h]
  have hne : α ≠ 0 := by intro h0; rw [h0] at hre; simp at hre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  have h1 : (1 / α).im = -α.im / Complex.normSq α := by rw [one_div, Complex.inv_im]
  have h2 : (1 / α).re = α.re / Complex.normSq α := by rw [one_div, Complex.inv_re]
  rw [h1, h2, abs_div, abs_neg, abs_of_nonneg hns.le]
  rw [div_le_div_iff_of_pos_right hns]
  exact le_of_lt h

theorem alpha_ne_zero_of_inf1 {α : ℂ} (h : MandelDim.InF1 α) : α ≠ 0 := by
  intro h0
  have hre : 0 < α.re := by have := abs_nonneg α.im; linarith [show |α.im| < α.re from h]
  rw [h0] at hre; simp at hre

/-! ## 1. Lattice clearance of the gate -/

/-- Every lattice point `k/α` with `k ≥ 0` has `b₂`-marginal `≤ -Ξ`. -/
theorem mgB_div_alpha_nonpos {Ξ : ℝ} {α : ℂ} (h : |(1/α).im| ≤ (1/α).re) (k : ℤ)
    (hk : 0 ≤ k) : mgB Ξ ((k : ℂ) / α) ≤ -Ξ := by
  have hre : ((k : ℂ) / α).re = (k : ℝ) * (1/α).re := by
    rw [div_eq_mul_inv, one_div, Complex.mul_re]; simp
  have him : ((k : ℂ) / α).im = (k : ℝ) * (1/α).im := by
    rw [div_eq_mul_inv, one_div, Complex.mul_im]; simp
  have hk0 : (0:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : |(k:ℝ) * (1/α).im| ≤ (k:ℝ) * (1/α).re := by
    rw [abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_left h hk0
  simp only [mgB, hre, him]
  linarith

/-- Every lattice point `k/α` with `k ≤ -1` has `b₁`-marginal `≤ -Ξ`. -/
theorem mgA_div_alpha_nonpos {Ξ : ℝ} {α : ℂ} (h : |(1/α).im| ≤ (1/α).re) (k : ℤ)
    (hk : k ≤ -1) : mgA Ξ α ((k : ℂ) / α) ≤ -Ξ := by
  have hre : ((k : ℂ) / α).re = (k : ℝ) * (1/α).re := by
    rw [div_eq_mul_inv, one_div, Complex.mul_re]; simp
  have him : ((k : ℂ) / α).im = (k : ℝ) * (1/α).im := by
    rw [div_eq_mul_inv, one_div, Complex.mul_im]; simp
  have hk1 : (k : ℝ) + 1 ≤ 0 := by
    have : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    linarith
  have hia : (0:ℝ) ≤ (1/α).re := le_trans (abs_nonneg _) h
  have hb : |(k:ℝ) * (1/α).im + (1/α).im| = |(k:ℝ) + 1| * |(1/α).im| := by
    rw [show (k:ℝ) * (1/α).im + (1/α).im = ((k:ℝ)+1) * (1/α).im by ring, abs_mul]
  have hkabs : |(k:ℝ) + 1| = -((k:ℝ)+1) := abs_of_nonpos hk1
  have h4 : (-((k:ℝ)+1)) * |(1/α).im| ≤ (-((k:ℝ)+1)) * (1/α).re :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h5 : ((k:ℝ) + 1) * (1/α).re + (-((k:ℝ)+1)) * (1/α).re = 0 := by ring
  simp only [mgA, hre, him]
  rw [hb, hkabs]
  linarith

/-- **Lattice clearance of the gate.**  For `w` with positive gate marginals, the lattice
`(1/α)ℤ` is at distance at least `(min (mgA) (mgB) (w) + Ξ)/√2`. -/
theorem lattice_clear_gate_scaled {Ξ : ℝ} {α : ℂ}
    (h : |(1/α).im| ≤ (1/α).re) {w : ℂ} (hA : 0 < mgA Ξ α w) (hB : 0 < mgB Ξ w) (k : ℤ) :
    (min (mgA Ξ α w) (mgB Ξ w) + Ξ) / Real.sqrt 2 ≤ ‖w - (k : ℂ) / α‖ := by
  have hsqrtpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rcases lt_or_ge k 0 with hk | hk
  · have hk' : k ≤ -1 := by omega
    have h1 : mgA Ξ α ((k:ℂ)/α) ≤ -Ξ := mgA_div_alpha_nonpos h k hk'
    have h2 : mgA Ξ α w - mgA Ξ α ((k:ℂ)/α) ≤ Real.sqrt 2 * ‖w - (k:ℂ)/α‖ :=
      le_trans (le_abs_self (mgA Ξ α w - mgA Ξ α ((k:ℂ)/α)))
        (abs_mgA_sub_le (Ξ := Ξ) (α := α) w ((k:ℂ)/α))
    have h3 : min (mgA Ξ α w) (mgB Ξ w) + Ξ ≤ Real.sqrt 2 * ‖w - (k:ℂ)/α‖ := by
      have := min_le_left (mgA Ξ α w) (mgB Ξ w); linarith
    rw [div_le_iff₀ hsqrtpos]; linarith
  · have h1 : mgB Ξ ((k:ℂ)/α) ≤ -Ξ := mgB_div_alpha_nonpos h k hk
    have h2 : mgB Ξ w - mgB Ξ ((k:ℂ)/α) ≤ Real.sqrt 2 * ‖w - (k:ℂ)/α‖ :=
      le_trans (le_abs_self (mgB Ξ w - mgB Ξ ((k:ℂ)/α)))
        (abs_mgB_sub_le w ((k:ℂ)/α))
    have h3 : min (mgA Ξ α w) (mgB Ξ w) + Ξ ≤ Real.sqrt 2 * ‖w - (k:ℂ)/α‖ := by
      have := min_le_right (mgA Ξ α w) (mgB Ξ w); linarith
    rw [div_le_iff₀ hsqrtpos]; linarith

/-- **Lattice clearance of the gate**, in the form required by the cleared-piece lemmas: if the
margin at `w` is at least `2^10 √2 - Ξ`, then `‖α‖ 2^10 ≤ ‖α w - k‖` for every integer `k`. -/
theorem lattice_clear_alpha_of_margin {Ξ : ℝ} {α : ℂ} (hInF1 : MandelDim.InF1 α) {w : ℂ}
    (hA : 0 < mgA Ξ α w) (hB : 0 < mgB Ξ w)
    (hm : 2 ^ 10 * Real.sqrt 2 ≤ min (mgA Ξ α w) (mgB Ξ w) + Ξ) (k : ℤ) :
    ‖α‖ * 2 ^ 10 ≤ ‖α * w - (k : ℂ)‖ := by
  have hsqrtpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcl := lattice_clear_gate_scaled (im_inv_le_re_inv hInF1) hA hB k
  have hαne : α ≠ 0 := alpha_ne_zero_of_inf1 hInF1
  have hfac : α * w - (k:ℂ) = α * (w - (k:ℂ)/α) := by
    have h1 : α * ((k:ℂ) / α) = (k:ℂ) := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm α (k:ℂ), mul_assoc,
        mul_inv_cancel₀ hαne, mul_one]
    rw [mul_sub, h1]
  have hnorm : ‖α‖ * 2 ^ 10 ≤ ‖α‖ * ((min (mgA Ξ α w) (mgB Ξ w) + Ξ) / Real.sqrt 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg α)
    rw [le_div_iff₀ hsqrtpos]; linarith
  rw [hfac, norm_mul]
  exact le_trans hnorm (mul_le_mul_of_nonneg_left hcl (norm_nonneg α))

/-! ## 2. The corridor's elementary data -/

/-- `mgA` shifts by the change of abscissa along a horizontal line. -/
lemma mgA_shift {Ξ : ℝ} {α : ℂ} {x x' y : ℝ} :
    mgA Ξ α ((x' : ℂ) + (y : ℂ) * Complex.I)
      = mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I) + (x' - x) := by
  rw [mgA_re_im, mgA_re_im]; ring

/-- `mgB` shifts by minus the change of abscissa along a horizontal line. -/
lemma mgB_shift {Ξ : ℝ} {x x' y : ℝ} :
    mgB Ξ ((x' : ℂ) + (y : ℂ) * Complex.I)
      = mgB Ξ ((x : ℂ) + (y : ℂ) * Complex.I) - (x' - x) := by
  rw [mgB_re_im, mgB_re_im]; ring

/-- **The pin bounds.** -/
theorem pin_re_im' {M Kp : ℝ} {z₀ : ℂ}
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    |z₀.re + M| ≤ Kp * (1 + Real.log (2 + M)) ∧
      |z₀.im| ≤ Kp * (1 + Real.log (2 + M)) := by
  have h1 : |(z₀ + (((M : ℝ)) : ℂ)).re| ≤ ‖z₀ + (((M : ℝ)) : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have h2 : |(z₀ + (((M : ℝ)) : ℂ)).im| ≤ ‖z₀ + (((M : ℝ)) : ℂ)‖ :=
    Complex.abs_im_le_norm _
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
    add_zero] at h1 h2
  exact ⟨le_trans h1 hpinbd, le_trans h2 hpinbd⟩

/-- **The corridor is no longer than the pin's displacement plus the band's width.** -/
private lemma len_le {Ξ M Kp Rde : ℝ} {z₀ : ℂ} {x : ℝ}
    (hM : 2 ^ 10 ≤ M) (hRde : 0 < Rde)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ x)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    (hmB : 2 * Rde + 2 < mgB Ξ z₀) :
    z₀.re - x ≤ Kp * (1 + Real.log (2 + M)) + M + Ξ + 2 ^ 10 := by
  obtain ⟨hx₀, hy₀⟩ := pin_re_im' hpinbd
  have hx₀' : z₀.re ≤ -(M) + Kp * (1 + Real.log (2 + M)) := by
    have := (abs_le.mp hx₀).2
    linarith
  have hy₀le : -z₀.im ≤ Kp * (1 + Real.log (2 + M)) := by
    have h := (abs_le.mp hy₀).1
    linarith
  have hmB' : |z₀.im| - Ξ - z₀.re > 2 * Rde + 2 := by simpa [mgB] using hmB
  have hx : -x ≤ Ξ + 2 ^ 10 + 2 * M := by linarith
  have h1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
  nlinarith [abs_nonneg z₀.im, hx₀', hx, hy₀le, neg_abs_le z₀.im, hRde]

/-- **The pin constraint.**  `z₀ ∈ Qm` with margin `> 2 Rde + 2` at the pin, together with
`‖z₀ + M‖ ≤ Kp (1 + log (2+M))`, forces `Ξ + 2 Rde ≤ M + 2 Kp (1 + log (2+M))`. -/
lemma pin_le {Ξ M Kp Rde : ℝ} {z₀ : ℂ}
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    (hmB : 2 * Rde + 2 < mgB Ξ z₀) :
    Ξ + 2 * Rde ≤ M + 2 * Kp * (1 + Real.log (2 + M)) := by
  obtain ⟨hx₀, hy₀⟩ := pin_re_im' hpinbd
  have hx₀' : -(M) - Kp * (1 + Real.log (2 + M)) ≤ z₀.re := by
    have := (abs_le.mp hx₀).1
    linarith
  have hmB' : |z₀.im| - Ξ - z₀.re > 2 * Rde + 2 := by simpa [mgB] using hmB
  nlinarith [abs_nonneg z₀.im, le_abs_self z₀.im, neg_abs_le z₀.im]

/-! ## 2b. The height trick: lifting a horizontal corridor

Lifting the height from `y` to `s` with `|s| - |y| ≥ T` increases **both** marginals by at least
`T`, provided `s` is at least as far from `0` as `y` and (for the vertical legs) `s` and `y` do not
have opposite signs.  These are the geometric inputs of the case `mgA (x + i y₀) < √2 Rde` of the
corridor comparison, where one lifts to `|s| = |y₀| + 2|Im (1/α)| + √2 Rde + 2^10` so that all
four end-margins of the lifted corridor become `≥ √2 Rde`. -/

/-- Lifting the height by `T` raises `mgA` by at least `T` when `T ≤ |s| - |y| - 2|Im (1/α)|`. -/
theorem mgA_lift_height {Ξ : ℝ} {α : ℂ} {x y s T : ℝ}
    (h : |y| + 2 * |(1/α).im| + T ≤ |s|) :
    mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I) + T ≤ mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I) := by
  have h1 : |s + (1/α).im| ≥ |s| - |(1/α).im| := by
    have := abs_sub_abs_le_abs_sub s (-((1/α).im))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have h2 : |y + (1/α).im| ≤ |y| + |(1/α).im| := abs_add_le _ _
  rw [mgA_re_im, mgA_re_im]
  linarith

/-- Lifting the height by `T` raises `mgB` by at least `T` when `T ≤ |s| - |y|`. -/
theorem mgB_lift_height {Ξ : ℝ} {x y s T : ℝ} (h : |y| + T ≤ |s|) :
    mgB Ξ ((x : ℂ) + (y : ℂ) * Complex.I) + T ≤ mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgB_re_im, mgB_re_im]
  linarith

/-- **The margins along a vertical line.**  Both marginals along the whole vertical line
`Re = a` dominate the two *dip* values: `mgA` at `Im = -Im (1/α)` and `mgB` at `Im = 0`.  This is
what replaces a margin computation on the vertical legs (which are *not* horizontal corridors). -/
theorem vert_margin_of_dips {Ξ : ℝ} {α : ℂ} {a u κ : ℝ}
    (hdipA : κ ≤ a - Ξ + (1/α).re) (hdipB : κ ≤ -Ξ - a) :
    κ ≤ min (mgA Ξ α ((a : ℂ) + (u : ℂ) * Complex.I))
            (mgB Ξ ((a : ℂ) + (u : ℂ) * Complex.I)) := by
  refine le_min ?_ ?_
  · rw [mgA_re_im]
    have := abs_nonneg (u + (1/α).im)
    linarith
  · rw [mgB_re_im]
    have := abs_nonneg u
    linarith

/-! NOTE (for the case `mgA (x + i y₀) < √2 Rde`).  The two `lift` lemmas above give the four
*end* margins of the lifted corridor `[x, x₀] × {s}` (with `|s| = |y₀| + 2|Im(1/α)| + √2 Rde + 2^10`)
as soon as the end margins at height `y₀` satisfy `mgA (x + i y₀) ≥ 16M`, `mgB (x + i y₀) ≥ 2^10`,
`mgA z₀ > 2Rde+2`, `mgB z₀ > 2Rde+2`.  The two *vertical legs* then need their own margin bounds:
the leg at the band abscissa `x` is free (`dev_vert_band`, band, any heights); for the leg at `x₀`
one must avoid the dip of `|u + Im(1/α)|` at `u = -Im(1/α)` (the margin `mgA` along that leg is
`x₀ - Ξ + Re(1/α) + |u + Im(1/α)|`, whose minimum over `u ∈ [y₀, s]` is
`min (mgA z₀) (mgA (x₀ + i s))` *when `-Im(1/α)` is outside the interval*, and
`x₀ - Ξ + Re(1/α)` otherwise). -/

/-! ## 2c. The vertical leg at the band abscissa: its cost fits the `|t|/8` slot -/

/-- **The price of the vertical leg at the band abscissa.**  With `|y₀| ≤ Kp L` (the pin bound) the
vertical transport `c₀ |t - y₀|` from `z = x + i t` to the corridor's height `y₀` fits into the
`|t|/8` slot of the target, leaving `Kp 2^36 K L` untouched. -/
theorem leg_cost_le_slot {Ξ rr M Kp t y₀ : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr)
    (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hy : |y₀| ≤ Kp * (1 + Real.log (2 + M))) :
    (1 / 150 + 1 / 31) * |t - y₀|
      ≤ |t| / 8 - (1 / 150 + 1 / 31) * |t|
        + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
  have hc0 : (0:ℝ) ≤ 1 / 150 + 1 / 31 := by norm_num
  have hc0' : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 8 := by norm_num
  have hL : (0:ℝ) ≤ 1 + Real.log (2 + M) := by
    have h : (1:ℝ) ≤ 2 + M := by
      have h1024 : (1024:ℝ) = 2 ^ 10 := by norm_num
      linarith
    have := Real.log_nonneg h
    linarith
  have h1 : |t - y₀| ≤ |t| + |y₀| := by
    have h1a : t - y₀ ≤ |t| + |y₀| := by linarith [le_abs_self t, neg_le_abs y₀]
    have h1b : y₀ - t ≤ |t| + |y₀| := by linarith [le_abs_self y₀, neg_le_abs t]
    exact abs_sub_le_iff.mpr ⟨h1a, h1b⟩
  have h2 : (1 / 150 + 1 / 31) * |y₀|
      ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
    have hK1 : (1:ℝ) ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
      have hK' : (1:ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
        have h1 : 0 < 1 / Ξ := by positivity
        have h2 : 0 < 1 / rr := by positivity
        linarith
      nlinarith [show (1:ℝ) ≤ 2 ^ 36 by norm_num, hK']
    have h3 : (1 / 150 + 1 / 31 : ℝ) ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
      linarith [hK1, show (1 / 150 + 1 / 31 : ℝ) ≤ 1 by norm_num]
    calc (1 / 150 + 1 / 31) * |y₀| ≤ (1 / 150 + 1 / 31) * (Kp * (1 + Real.log (2 + M))) :=
          mul_le_mul_of_nonneg_left hy hc0
      _ ≤ (2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr)) * (Kp * (1 + Real.log (2 + M))) :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg hKp hL)
      _ = Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by ring
  have h5 : (1 / 150 + 1 / 31) * |t| ≤ |t| / 8 := by nlinarith [abs_nonneg t]
  have h6 : (1 / 150 + 1 / 31) * |t - y₀| ≤ (1 / 150 + 1 / 31) * (|t| + |y₀|) :=
    mul_le_mul_of_nonneg_left h1 hc0
  linarith [h6, h5, h2]

/-! ## 3. The affine corridor bound in the good case -/

/-- **The corridor deviation of `corridor_dev_affine`, with the margin ratios bounded by the
explicit `√2 Rde` (band end) and `2 Rde + 2` (pin end).**  If the `b₁`-margin at the band end is
`≥ √2 Rde`, then the whole corridor has margin `≥ √2 Rde` and

`‖D q - D z₀‖ ≤ C₂ √2 (log (1 + ℓ/(√2 Rde)) + log (1 + ℓ/(2 Rde + 2))) + ℓ/31`. -/
theorem corridor_left_affine {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hcase : z.re ≤ z₀.re)
    (hgood : Real.sqrt 2 * Rde
      ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) :
    ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖
      ≤ C₂ * Real.sqrt 2 *
          (Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
            + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)))
        + (z₀.re - z.re) / 31 := by
  have hq : ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
    (band_margins hΞ hM hInF1 hα hQAdm z.re z₀.im hzlo hzhi).1
  have hz₀' : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = z₀ := Complex.re_add_im z₀
  have hseg : ∀ ξ ∈ Set.Icc z.re z₀.re,
      ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro ξ hξ
    exact slice_interval (s := z₀.im) (a := z.re) (b := z₀.re) hq (by rw [hz₀']; exact hz₀)
      (by rw [min_eq_left hcase, max_eq_right hcase]; exact hξ)
  have hB : Real.sqrt 2 * Rde ≤ mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    have h := (zo_margins hRde hcl).2
    rw [hz₀']
    have hs2 : Real.sqrt 2 * Rde ≤ 2 * Rde + 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, hRde]
    linarith
  have hdev := corridor_dev_affine (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (x := z.re) (x₀ := z₀.re) (y := z₀.im)
    hF hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE hNT hΦm hcase hseg hgood hB
  have hmgApos : 0 < mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < Real.sqrt 2 * Rde) hgood
  have hmgBpos : 0 < mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    have h := (zo_margins hRde hcl).2
    rw [hz₀']
    linarith
  have hshiftA : mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      = mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) + (z₀.re - z.re) := mgA_shift
  have hshiftB : mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      = mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) + (z₀.re - z.re) := by
    have := mgB_shift (Ξ := Ξ) (x := z₀.re) (x' := z.re) (y := z₀.im)
    linarith
  have hsqrtpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hratioA : mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      / mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      ≤ 1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde) := by
    have h1 : 0 < Real.sqrt 2 * Rde := by positivity
    rw [hshiftA, div_le_iff₀ hmgApos]
    have h3 : (z₀.re - z.re) ≤ (z₀.re - z.re) / (Real.sqrt 2 * Rde)
        * mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1]
      have h4 : Real.sqrt 2 * Rde * (z₀.re - z.re)
          ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) * (z₀.re - z.re) :=
        mul_le_mul_of_nonneg_right hgood (by linarith)
      linarith
    calc mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) + (z₀.re - z.re)
        ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
            + (z₀.re - z.re) / (Real.sqrt 2 * Rde)
              * mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by linarith
      _ = (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
            * mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by ring
  have hratioB : mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      / mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      ≤ 1 + (z₀.re - z.re) / (2 * Rde + 2) := by
    have h1 : 0 < 2 * Rde + 2 := by linarith
    rw [hshiftB, div_le_iff₀ hmgBpos]
    have h4 : 2 * Rde + 2 < mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      have h := (zo_margins hRde hcl).2
      rw [hz₀']
      exact h
    have h3 : (z₀.re - z.re) ≤ (z₀.re - z.re) / (2 * Rde + 2)
        * mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1]
      nlinarith
    calc mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) + (z₀.re - z.re)
        ≤ mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
            + (z₀.re - z.re) / (2 * Rde + 2)
              * mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by linarith
      _ = (1 + (z₀.re - z.re) / (2 * Rde + 2))
            * mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by ring
  have hlogA : Real.log (mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
        / mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
      ≤ Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde)) :=
    Real.log_le_log (div_pos (by linarith) hmgApos) hratioA
  have hlogB : Real.log (mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
        / mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I))
      ≤ Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)) :=
    Real.log_le_log (div_pos (by linarith) hmgBpos) hratioB
  have hcomb : Real.log (mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
        / mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
      + Real.log (mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
        / mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I))
      ≤ Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
        + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)) := add_le_add hlogA hlogB
  have hfac : (0:ℝ) ≤ C₂ * Real.sqrt 2 := by positivity
  have hkey : C₂ * Real.sqrt 2
        * (Real.log (mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
              / mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          + Real.log (mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
              / mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)))
      ≤ C₂ * Real.sqrt 2
        * (Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
          + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2))) :=
    mul_le_mul_of_nonneg_left hcomb hfac
  have hz₀'' : (Φm z₀ - z₀) = (Φm ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      - ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I)) := by rw [hz₀']
  rw [hz₀'']
  rw [norm_sub_rev] at hdev
  exact le_trans hdev (add_le_add hkey le_rfl)

end

/-- `⌈X/P⌉ · P ≤ X + P` for `X ≥ 0`, `P > 0`. -/
lemma ceil_mul_le_add {X P : ℝ} (hX : 0 ≤ X) (hP : 0 < P) :
    ((Nat.ceil (X / P) : ℕ) : ℝ) * P ≤ X + P := by
  have hz : 0 ≤ X / P := div_nonneg hX (le_of_lt hP)
  have hlt := Nat.ceil_lt_add_one hz
  have hmul := mul_lt_mul_of_pos_right hlt hP
  rw [add_mul, one_mul, div_mul_cancel₀ X (ne_of_gt hP)] at hmul
  linarith [le_of_lt hmul]

/-- `X ≤ ⌈X/P⌉ · P` for `P > 0`. -/
lemma le_ceil_mul {X P : ℝ} (hP : 0 < P) :
    X ≤ ((Nat.ceil (X / P) : ℕ) : ℝ) * P := by
  have h2 : X / P ≤ ((Nat.ceil (X / P) : ℕ) : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hP] at h2
  linarith [h2]

/-- **The route-A step of `corridor_left_wk`.**  Assume the case-A margin at the band abscissa and
the two arithmetic inputs: the linear `ℓ/31` term fits the `|t|/8` slot (`hlin`) and the `C₂`-log
term plus one piece price fits the `N·P` budget (`harith`).  Then the target's conclusion holds with
`W = ℓ/31` and `N = ⌈C₂√2(logs)/P⌉`. -/
theorem corridor_left_wk_route_A {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hcase : z.re ≤ z₀.re)
    (hgood : Real.sqrt 2 * Rde
      ≤ Work.Pert.V5.mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
    (hlin : (z₀.re - z.re) / 31
      ≤ |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
        + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)))
    (harith : C₂ * Real.sqrt 2 *
          (Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
            + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)))
        + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
      ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))) :
    ∃ (N : ℕ) (W : ℝ),
      W + (1 / 150 + 1 / 31) * |z.im|
        ≤ |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
        ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          - (Φm z₀ - z₀)‖
        ≤ W + (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  have hdev := corridor_left_affine (Ξ := Ξ) (rr := rr) (M := M) (Kp := Kp) (Rde := Rde) (C₂ := C₂)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (z₀ := z₀) hF hΞ hrr hM hKp hRde hC₂ hInF1 hα hQAdm
    hσ hnorm hu hu2 hτQ hDE hNT hΦm hz₀ hcl hz hzlo hzhi hcase hgood
  have hPpos : 0 < C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
      + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
    have hL : 0 < 1 + Real.log (2 + M) := by
      have h : (1:ℝ) < 2 + M := by linarith
      have := Real.log_pos h
      linarith
    have h1 : 0 < C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) := by positivity
    have h2 : 0 ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
      have hLg : 0 ≤ Real.log (2 + 16 * (M + 2 + Ξ)) := by
        apply Real.log_nonneg
        have h1024 : (1024:ℝ) = 2 ^ 10 := by norm_num
        linarith
      positivity
    linarith
  have hX0 : 0 ≤ C₂ * Real.sqrt 2 *
      (Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
        + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2))) := by
    have h1 : 0 ≤ Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde)) :=
      Real.log_nonneg (by
        have h : 0 ≤ (z₀.re - z.re) / (Real.sqrt 2 * Rde) :=
          div_nonneg (by linarith) (by positivity)
        linarith)
    have h2 : 0 ≤ Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)) :=
      Real.log_nonneg (by
        have h : 0 ≤ (z₀.re - z.re) / (2 * Rde + 2) :=
          div_nonneg (by linarith) (by linarith)
        linarith)
    positivity
  refine ⟨Nat.ceil (C₂ * Real.sqrt 2 *
        (Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
          + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)))
      / (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
          + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))),
    (z₀.re - z.re) / 31, ?_, ?_, ?_⟩
  · linarith [hlin]
  · have h1 := ceil_mul_le_add hX0 hPpos
    linarith [h1, harith]
  · have h1 := le_ceil_mul (X := C₂ * Real.sqrt 2 *
        (Real.log (1 + (z₀.re - z.re) / (Real.sqrt 2 * Rde))
          + Real.log (1 + (z₀.re - z.re) / (2 * Rde + 2)))) hPpos
    linarith [hdev, h1]

/-- **The route-P step of `corridor_left_wk`.**  Assume the case-A margin at the band abscissa, the
lattice clearance on the corridor and the arithmetic `N·P ≤ B` for the *number* `N` of cleared
pieces; then the target's conclusion holds with `N` pieces and `W = 0`.  What is left for
`corridor_left_wk` is exactly the case analysis producing `hgood`, `hclear` and `harith` (or
switching to the height-trick / affine route, where `W` must also pay the linear `c₀`- and `1/31`
costs). -/
theorem corridor_left_wk_route_P {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hcase : z.re ≤ z₀.re)
    (hgood : Real.sqrt 2 * Rde
      ≤ Work.Pert.V5.mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
    (hclear : ∀ ξ ∈ Set.Icc z.re z₀.re, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) - (k : ℂ)‖)
    (harith : ((Nat.ceil ((z₀.re - z.re) / (16 * (M + 2 + Ξ))) : ℝ))
        * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
      ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))) :
    ∃ (N : ℕ) (W : ℝ),
      W + (1 / 150 + 1 / 31) * |z.im|
        ≤ |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
        ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          - (Φm z₀ - z₀)‖
        ≤ W + (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  have hcorr := corridor_left_cover (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (z₀ := z₀) hΞ hrr hM hRde hC₂ hInF1 hα hQAdm hσ hnorm
    hu hu2 hτQ hDE hNT hΦm hz₀ hcl hz hzlo hzhi hcase hgood hclear
  refine ⟨Nat.ceil ((z₀.re - z.re) / (16 * (M + 2 + Ξ))), 0, ?_, harith, by simpa using hcorr⟩
  have hc0 : (0:ℝ) ≤ 1 / 150 + 1 / 31 := by norm_num
  have hc0' : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 8 := by norm_num
  have h1 : (0:ℝ) ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
    have hL : (0:ℝ) ≤ 1 + Real.log (2 + M) := by
      have h : (1:ℝ) ≤ 2 + M := by linarith
      have := Real.log_nonneg h
      linarith
    have hK : (0:ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
      have h1 : 0 ≤ 1 / Ξ := by positivity
      have h2 : 0 ≤ 1 / rr := by positivity
      linarith
    positivity
  have h2 : (1 / 150 + 1 / 31) * |z.im| ≤ |z.im| / 8 := by nlinarith [abs_nonneg z.im]
  linarith

theorem corridor_left_wk {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (ht : 4 * Rde ≤ |z.im|) (hcase : z.re ≤ z₀.re) :
    ∃ (N : ℕ) (W : ℝ),
      W + (1 / 150 + 1 / 31) * |z.im|
        ≤ |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
        ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          - (Φm z₀ - z₀)‖
        ≤ W + (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  -- ## 0. the pin data
  have hmB : 2 * Rde + 2 < mgB Ξ z₀ := (zo_margins hRde hcl).2
  have hpin : Ξ + 2 * Rde ≤ M + 2 * Kp * (1 + Real.log (2 + M)) := pin_le hpinbd hmB
  have hlen : z₀.re - z.re ≤ Kp * (1 + Real.log (2 + M)) + M + Ξ + 2 ^ 10 :=
    len_le hM hRde hzlo hpinbd hmB
  have hLpos : 0 < 1 + Real.log (2 + M) := by
    have h : (1 : ℝ) ≤ 2 + M := by linarith
    have := Real.log_nonneg h
    linarith
  have hLg0 : 0 ≤ 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by
    have h : (1 : ℝ) ≤ 2 + 16 * (M + 2 + Ξ) := by linarith
    have := Real.log_nonneg h
    linarith
  have hc0nn : 0 ≤ (1 / 8 - (1 / 150 + 1 / 31)) * |z.im| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  have hKpslot_nn :
      0 ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
    have h1 : (0 : ℝ) < 1 / Ξ := one_div_pos.mpr hΞ
    have h2 : (0 : ℝ) < 1 / rr := one_div_pos.mpr hrr
    exact mul_nonneg (mul_nonneg (mul_nonneg hKp (by norm_num)) (by linarith)) hLpos.le
  have hPnn : 0 ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
      + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
    have h1 : 0 ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₂.le (by norm_num))
        (by linarith [hΞ.le])) hLpos.le
    have h2 : 0 ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith [one_div_pos.mpr hrr])) hLg0
    linarith
  have hPpos : 0 < C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
      + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
    have h1 : 0 < C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) :=
      mul_pos (mul_pos (mul_pos hC₂ (by norm_num)) (by linarith)) hLpos
    have h2 : 0 ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith [one_div_pos.mpr hrr])) hLg0
    linarith
  have hB := P_le_B_pin hΞ hrr hM hKp hRde hC₂ hpin
  -- ## 1. the long corridor
  by_cases hlong : 14 * (M + Ξ) < z₀.re - z.re
  · refine ⟨1, |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
        + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)), ?_, ?_, ?_⟩
    · have e : (|z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
            + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)))
            + (1 / 150 + 1 / 31) * |z.im|
          = |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
        ring
      exact le_of_eq e
    · simpa using hB
    · have h := corridor_left_long hF hΞ hrr hM hKp hRde hC₂ hInF1 hα hQAdm hσ hnorm hu hu2
        hτQ hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi hcase hlong
      simpa using h
  · push_neg at hlong
    -- ## 2. the short corridor: the `C₂`-free linear bound
    have hdev : ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀)‖
        ≤ 1025 * (z₀.re - z.re) :=
      corridor_dev_linear hΞ hrr hM hRde hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm hz₀ hcl
        hz hzlo hzhi hcase
    by_cases hcrude : 1025 * (z₀.re - z.re)
        ≤ (1 / 8 - (1 / 150 + 1 / 31)) * |z.im|
          + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
    · -- 2a. the crude bound is already enough
      refine ⟨1, (1 / 8 - (1 / 150 + 1 / 31)) * |z.im|
          + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)), ?_, ?_, ?_⟩
      · have e : ((1 / 8 - (1 / 150 + 1 / 31)) * |z.im|
              + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)))
              + (1 / 150 + 1 / 31) * |z.im|
            = |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
          ring
        exact le_of_eq e
      · simpa using hB
      · simp only [Nat.cast_one, one_mul]
        linarith [hdev, hcrude]
    · -- 2b. the failure regime: the cleared-piece cover with `N = 1`
      have hneg : (1 / 8 - (1 / 150 + 1 / 31)) * |z.im|
            + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
                + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
          < 1025 * (z₀.re - z.re) := not_le.mp hcrude
      have hK2 : (2 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
        have hinv : (2 : ℝ) ≤ Ξ + 1 / Ξ := by
          have h : Ξ + 1 / Ξ - 2 = (Ξ - 1) ^ 2 / Ξ := by field_simp; ring
          have h2 : 0 ≤ (Ξ - 1) ^ 2 / Ξ := div_nonneg (sq_nonneg _) hΞ.le
          linarith
        have h3 : (0 : ℝ) < 1 / rr := one_div_pos.mpr hrr
        linarith
      have hXnn : 0 ≤ Kp * (1 + Real.log (2 + M)) := mul_nonneg hKp hLpos.le
      have hfail1 : 2 ^ 37 * (Kp * (1 + Real.log (2 + M))) < 1025 * (z₀.re - z.re) := by
        have he : Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            = 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (Kp * (1 + Real.log (2 + M))) := by ring
        have h2 : 2 ^ 37 * (Kp * (1 + Real.log (2 + M)))
            ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (Kp * (1 + Real.log (2 + M))) := by
          have h36 : (0 : ℝ) ≤ 2 ^ 36 * (Kp * (1 + Real.log (2 + M))) :=
            mul_nonneg (by norm_num) hXnn
          have hstep := mul_le_mul_of_nonneg_right hK2 h36
          have hsplit : 2 ^ 37 * (Kp * (1 + Real.log (2 + M)))
              = 2 * (2 ^ 36 * (Kp * (1 + Real.log (2 + M)))) := by ring
          calc 2 ^ 37 * (Kp * (1 + Real.log (2 + M)))
              = 2 * (2 ^ 36 * (Kp * (1 + Real.log (2 + M)))) := hsplit
            _ ≤ (1 + Ξ + 1 / Ξ + 1 / rr)
                  * (2 ^ 36 * (Kp * (1 + Real.log (2 + M)))) := hstep
            _ = 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr)
                  * (Kp * (1 + Real.log (2 + M))) := by ring
        linarith [hneg, he, h2, hc0nn, hPnn]
      have hfail2 : 2 ^ 24 * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))
          < 1025 * (z₀.re - z.re) := by
        have h1 : (1 : ℝ) ≤ 1 + 1 / rr := by linarith [one_div_pos.mpr hrr]
        have ha : 2 ^ 24 * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))
            ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
          nlinarith [h1, hLg0]
        have hb : 0 ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hC₂.le (by norm_num))
            (by linarith [hΞ.le])) hLpos.le
        linarith [hneg, ha, hb, hKpslot_nn, hc0nn]
      have hΞX : Ξ ≤ M + 2 * (Kp * (1 + Real.log (2 + M))) := by linarith [hpin, hRde]
      have hgeom := fallback_clear_geom hM hΞ hlong hΞX hfail1 hfail2
      -- the case-A margin at the band abscissa
      have hmAq : (16 : ℝ) * M
          ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) :=
        (band_margins hΞ hM hInF1 hα hQAdm z.re z₀.im hzlo hzhi).2.2
      have hgood : Real.sqrt 2 * Rde
          ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
        by_contra hcon
        push_neg at hcon
        have hRde11 : 11 * M ≤ Rde := by
          have hs : Real.sqrt 2 < (16 : ℝ) / 11 := by
            rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 16 / 11)]
            norm_num
          have h16 : 16 * M < Real.sqrt 2 * Rde := lt_of_le_of_lt hmAq hcon
          nlinarith [h16, hs, hRde]
        have hpin' : Ξ + 2 * Rde ≤ M + 2 * (Kp * (1 + Real.log (2 + M))) := by
          have e : M + 2 * Kp * (1 + Real.log (2 + M))
              = M + 2 * (Kp * (1 + Real.log (2 + M))) := by ring
          linarith [hpin, e]
        have hcb := crude_of_caseB hΞ hrr hKp hM hRde11 hpin' hlen
        linarith [hcb, hfail1]
      -- the lattice clearance on the corridor
      have hx0 : z₀.re ≤ -M + Kp * (1 + Real.log (2 + M)) := by
        have h1 := Complex.abs_re_le_norm (z₀ + (((M : ℝ)) : ℂ))
        rw [Complex.add_re, Complex.ofReal_re] at h1
        have h2 : |z₀.re + M| ≤ Kp * (1 + Real.log (2 + M)) := le_trans h1 hpinbd
        have h3 := (abs_le.mp h2).2
        linarith
      have hclear : ∀ ξ ∈ Set.Icc z.re z₀.re, ∀ k : ℤ,
          ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) - (k : ℂ)‖ := by
        intro ξ hξ k
        obtain ⟨hlow, hhigh⟩ := hgeom ξ (le_trans hzlo hξ.1) (le_trans hξ.2 hx0)
        have hre : ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I).re = ξ := by simp
        have hwr : |((ξ : ℂ) + (z₀.im : ℂ) * Complex.I).re| ≤ 20 * (M + 2 + Ξ) := by
          rw [hre]; exact hhigh
        have hlown : (2 : ℝ) ^ 10 ≤ ‖((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)‖ := by
          have h1 := Complex.abs_re_le_norm ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
          rw [hre] at h1
          linarith
        exact clear_lattice_gate hΞ hM hInF1 hα hwr hlown k
      have hcover := corridor_left_cover hΞ hrr hM hRde hC₂ hInF1 hα hQAdm hσ hnorm hu hu2 hτQ
        hDE hNT hΦm hz₀ hcl hz hzlo hzhi hcase hgood hclear
      have hN1' : Nat.ceil ((z₀.re - z.re) / (16 * (M + 2 + Ξ))) ≤ 1 := by
        rw [Nat.ceil_le]
        push_cast
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 16 * (M + 2 + Ξ))]
        linarith [hlong, hM, hΞ]
      have hN1 : ((Nat.ceil ((z₀.re - z.re) / (16 * (M + 2 + Ξ))) : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast hN1'
      have hdevP : ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
            - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀)‖
          ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
        have h1 := mul_le_mul_of_nonneg_right hN1 hPpos.le
        rw [one_mul] at h1
        linarith [hcover, h1]
      refine ⟨1, (1 / 8 - (1 / 150 + 1 / 31)) * |z.im|
            + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)), ?_, ?_, ?_⟩
      · have e : ((1 / 8 - (1 / 150 + 1 / 31)) * |z.im|
              + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)))
              + (1 / 150 + 1 / 31) * |z.im|
            = |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
          ring
        exact le_of_eq e
      · simpa using hB
      · simp only [Nat.cast_one, one_mul]
        linarith [hdevP, hc0nn, hKpslot_nn]

end Work.Pert.V5
