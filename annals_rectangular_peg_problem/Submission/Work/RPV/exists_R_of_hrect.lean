import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.HrectPhase
import Submission.Work.RPV.hrectC_facts
import Submission.Work.RPV.neg_I_exp_half_re_im
import Submission.Work.RPV.exists_angle_toCircle

open RectangularPegProblem Manifold Complex Real

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.RPV

/-!
# Greene–Lobb normal form admits the rectangle chart (`Work.RPV.exists_R_of_hrect`)

The four points `x, x', y, y'` of the Greene–Lobb normal form (`x + y = x' + y'` and
`x' - y' = e^{iφ}(x - y)`, `0 < φ < π`, `x ≠ y`) span a rectangle whose diagonals differ by the
rotation `e^{iφ}`.  Writing `d = x - y` and

`c = i·e^{iφ/2}·d/‖d‖`  (the unit complex number `Work.RPV.hrectC φ d`),

the point `z = x·conj c` and the opposite corner `w = y·conj c` form the unrotated rectangle
whose `θ`-rotation (for any `θ` with `θ.toCircle = c`) is exactly `![x, x', y, y']`.  The two
remaining corners are recovered from

`(w.re + z.im·i)·c + (z.re + w.im·i)·c = z·c + w·c = x + y = x' + y'`  and
`(w.re + z.im·i)·c - (z.re + w.im·i)·c = -conj(z-w)·c = e^{iφ}·d = x' - y'`.

The width and height of the rectangle are the real and imaginary parts of

`z - w = d·conj c = -i·e^{-iφ/2}·‖d‖`,
hence `|z.re - w.re| = ‖d‖·sin(φ/2)` and `|z.im - w.im| = ‖d‖·cos(φ/2)`.

The algebraic facts about `c` are supplied by `Work.RPV.hrectC_facts`, the trigonometric
identity by `Work.RPV.neg_I_exp_half_re_im`, and the angle with `θ.toCircle = c` by
`Work.RPV.exists_angle_toCircle`.
-/

theorem exists_R_of_hrect {x y x' y' : ℂ} {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π) (hne : x ≠ y)
    (hs : x + y = x' + y') (hd : x' - y' = Complex.exp (φ * I) * (x - y)) :
    ∃ (θ' : Real.Angle) (z' w' : ℂ),
      RectangularPegProblem.R z' w' θ' = ![x, x', y, y'] ∧
      |z'.re - w'.re| = ‖x - y‖ * Real.sin (φ / 2) ∧
      |z'.im - w'.im| = ‖x - y‖ * Real.cos (φ / 2) := by
  have hdne : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨hC_norm, hC_mul, hC_sq, hC_sub⟩ := hrectC_facts φ (x - y) hdne
  obtain ⟨θ', hθ'⟩ := exists_angle_toCircle (hrectC φ (x - y)) hC_norm
  obtain ⟨hre, him⟩ := neg_I_exp_half_re_im φ ‖x - y‖
  set c : ℂ := hrectC φ (x - y) with hc
  have hθ'c : (θ'.toCircle : ℂ) = c := by rw [hc]; exact hθ'
  have hcmul : c * (starRingEnd ℂ) c = 1 := by rw [hc]; exact hC_mul
  have hcsq : (starRingEnd ℂ) (x - y) * c ^ 2 = -Complex.exp ((φ : ℂ) * Complex.I) * (x - y) := by
    rw [hc]; exact hC_sq
  have hcsub : (x - y) * (starRingEnd ℂ) c =
      -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) * (‖x - y‖ : ℂ) := by
    rw [hc]; exact hC_sub
  set z' : ℂ := x * (starRingEnd ℂ) c with hzdef
  set w' : ℂ := y * (starRingEnd ℂ) c with hwdef
  have hz : z' * c = x := by
    rw [hzdef, mul_assoc, mul_comm ((starRingEnd ℂ) c) c, hcmul, mul_one]
  have hw : w' * c = y := by
    rw [hwdef, mul_assoc, mul_comm ((starRingEnd ℂ) c) c, hcmul, mul_one]
  have hsum : (w'.re + z'.im * Complex.I) * c + (z'.re + w'.im * Complex.I) * c = x' + y' := by
    have hbr : (w'.re + z'.im * Complex.I) + (z'.re + w'.im * Complex.I) = z' + w' := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
    rw [← add_mul, hbr, add_mul, hz, hw, hs]
  have hdiff : (w'.re + z'.im * Complex.I) * c - (z'.re + w'.im * Complex.I) * c = x' - y' := by
    have hbr : (w'.re + z'.im * Complex.I) - (z'.re + w'.im * Complex.I) =
        -(starRingEnd ℂ) (z' - w') := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
        ring
      · simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
        ring
    have hconj : (starRingEnd ℂ) (z' - w') * c =
        -Complex.exp ((φ : ℂ) * Complex.I) * (x - y) := by
      have h1 : z' - w' = (x - y) * (starRingEnd ℂ) c := by rw [hzdef, hwdef]; ring
      rw [h1, map_mul, Complex.conj_conj]
      rw [show (starRingEnd ℂ) (x - y) * c * c = (starRingEnd ℂ) (x - y) * c ^ 2 by ring]
      exact hcsq
    rw [← sub_mul, hbr]
    calc -(starRingEnd ℂ) (z' - w') * c = -((starRingEnd ℂ) (z' - w') * c) := by ring
      _ = -(-Complex.exp ((φ : ℂ) * Complex.I) * (x - y)) := by rw [hconj]
      _ = Complex.exp ((φ : ℂ) * Complex.I) * (x - y) := by ring
      _ = x' - y' := hd.symm
  have hX : (w'.re + z'.im * Complex.I) * c = x' := by
    have h2 : 2 * ((w'.re + z'.im * Complex.I) * c) =
        ((w'.re + z'.im * Complex.I) * c + (z'.re + w'.im * Complex.I) * c) +
        ((w'.re + z'.im * Complex.I) * c - (z'.re + w'.im * Complex.I) * c) := by ring
    rw [hsum, hdiff] at h2
    linear_combination h2 / 2
  have hY : (z'.re + w'.im * Complex.I) * c = y' := by
    have h2 : 2 * ((z'.re + w'.im * Complex.I) * c) =
        ((w'.re + z'.im * Complex.I) * c + (z'.re + w'.im * Complex.I) * c) -
        ((w'.re + z'.im * Complex.I) * c - (z'.re + w'.im * Complex.I) * c) := by ring
    rw [hsum, hdiff] at h2
    linear_combination h2 / 2
  refine ⟨θ', z', w', ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [RectangularPegProblem.R, hθ'c, hz, hw, hX, hY]
  · have hsub : z' - w' =
        -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) * (‖x - y‖ : ℂ) := by
      have h1 : z' - w' = (x - y) * (starRingEnd ℂ) c := by rw [hzdef, hwdef]; ring
      rw [h1]; exact hcsub
    have hsin : 0 < Real.sin (φ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hre' : (z' - w').re = -‖x - y‖ * Real.sin (φ / 2) := by
      have hsub' : z' - w' =
          (-(Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I))) * (‖x - y‖ : ℂ) := by
        rw [hsub]; ring
      rw [hsub', hre]
    rw [← Complex.sub_re, hre']
    rw [show -‖x - y‖ * Real.sin (φ / 2) = -(‖x - y‖ * Real.sin (φ / 2)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (norm_nonneg (x - y)) hsin.le)]
  · have hsub : z' - w' =
        -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) * (‖x - y‖ : ℂ) := by
      have h1 : z' - w' = (x - y) * (starRingEnd ℂ) c := by rw [hzdef, hwdef]; ring
      rw [h1]; exact hcsub
    have hcos : 0 < Real.cos (φ / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [h1, Real.pi_pos]⟩
    have him' : (z' - w').im = -‖x - y‖ * Real.cos (φ / 2) := by
      have hsub' : z' - w' =
          (-(Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I))) * (‖x - y‖ : ℂ) := by
        rw [hsub]; ring
      rw [hsub', him]
    rw [← Complex.sub_im, him']
    rw [show -‖x - y‖ * Real.cos (φ / 2) = -(‖x - y‖ * Real.cos (φ / 2)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (norm_nonneg (x - y)) hcos.le)]

end Work.RPV
