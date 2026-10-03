import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.walk_re_mono
import Submission.Work.Pert.lattice_cell_harmonic
import Submission.Work.Pert.lattice_vshape_harmonic
import Submission.Work.Pert.Qm_slice

/-!
# PERT · `Work.Pert.lattice_sum_le`

The lattice sum of the gate walk (see the module comment in the final version).
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- `α ≠ 0` is part of `MandelDim.InF1`. -/
lemma InF1_ne_zero {α : ℂ} (h : MandelDim.InF1 α) : α ≠ 0 := by
  intro h0
  have h1 : |α.im| < α.re := h
  rw [h0] at h1
  simp at h1

lemma InF1_re_pos {α : ℂ} (h : MandelDim.InF1 α) : 0 < α.re := by
  have h1 : |α.im| < α.re := h
  linarith [abs_nonneg α.im]

/-- `(1/α).re = α.re / ‖α‖^2`. -/
lemma inv_re_eq {α : ℂ} (hα : α ≠ 0) : (1 / α).re = α.re / ‖α‖ ^ 2 := by
  rw [one_div, Complex.inv_re, Complex.sq_norm]

lemma inv_re_pos {α : ℂ} (h : MandelDim.InF1 α) : 0 < (1 / α).re := by
  have hne : α ≠ 0 := InF1_ne_zero h
  rw [inv_re_eq hne]
  exact div_pos (InF1_re_pos h) (pow_pos (norm_pos_iff.mpr hne) 2)

/-- `log x ≤ log A + log B` when `x ≤ A * B` and everything is positive. -/
lemma log_le_log_mul {x A B : ℝ} (hx : 0 < x) (hA : 0 < A) (hB : 0 < B) (h : x ≤ A * B) :
    Real.log x ≤ Real.log A + Real.log B := by
  calc Real.log x ≤ Real.log (A * B) := Real.log_le_log hx h
    _ = Real.log A + Real.log B := Real.log_mul (ne_of_gt hA) (ne_of_gt hB)

/-- `2 + 2/(Ξ*r) ≤ 4*(2 + 1/Ξ)*(2 + 1/r)`. -/
lemma two_add_two_div_le {Ξ r : ℝ} (hΞ : 0 < Ξ) (hr : 0 < r) :
    2 + 2 / (Ξ * r) ≤ 4 * (2 + 1 / Ξ) * (2 + 1 / r) := by
  have h : (0:ℝ) < Ξ * r := mul_pos hΞ hr
  have key : (2 + 2 / (Ξ * r)) * (Ξ * r) ≤ (4 * (2 + 1/Ξ) * (2 + 1/r)) * (Ξ * r) := by
    have expand : (4 * (2 + 1/Ξ) * (2 + 1/r)) * (Ξ * r) = 16 * Ξ * r + 8 * r + 8 * Ξ + 4 := by
      field_simp
      ring
    rw [expand]
    rw [show (2 + 2 / (Ξ * r)) * (Ξ * r) = 2 * (Ξ * r) + 2 by
      field_simp]
    nlinarith [hΞ, hr]
  exact (mul_le_mul_iff_of_pos_right h).mp key

/-- The gate gives `|Re w| ≤ |Im w| + 2 (1/α).re`. -/
lemma gate_abs_re_le {α : ℂ} {Ξ : ℝ} {w : ℂ} (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hw : w ∈ Work.Pert.Qm Ξ α) :
    |w.re| ≤ |w.im| + 2 * (1 / α).re := by
  obtain ⟨h1, h2⟩ := (Qm_mem_iff (ξ := Ξ) (α := α) (z := w)).mp hw
  have hα : |α.im| < α.re := hInF1
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr (InF1_ne_zero hInF1)
  have hre : (1 / α).re = α.re / Complex.normSq α := by rw [one_div, Complex.inv_re]
  have him : (1 / α).im = -α.im / Complex.normSq α := by rw [one_div, Complex.inv_im]
  have h3 : 0 < (1 / α).re := by rw [hre]; exact div_pos (InF1_re_pos hInF1) hns
  have hle : |(1 / α).im| ≤ (1 / α).re := by
    rw [hre, him, abs_div, abs_neg, abs_of_pos hns]
    exact div_le_div_of_nonneg_right (le_of_lt hα) (le_of_lt hns)
  have h2' : |w.im + (1 / α).im| ≤ |w.im| + |(1 / α).im| := abs_add_le _ _
  have hlow : -(2 * (1 / α).re) - |w.im| ≤ w.re := by
    have h4 : |(1 / α).im| ≤ Ξ + (1 / α).re := by linarith
    linarith
  have hup : w.re ≤ |w.im| := le_of_lt (lt_of_lt_of_le h2 (by linarith))
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- `(1/α).re ≤ 1/‖α‖`. -/
lemma inv_re_le {α : ℂ} (hα : α ≠ 0) : (1 / α).re ≤ 1 / ‖α‖ := by
  have h : (1 / α).re ≤ ‖(1 / α)‖ := Complex.re_le_norm _
  rw [one_div, norm_inv] at h
  simpa using h


/-- The real and imaginary parts of a near-translation step. -/
lemma step_parts {w : ℕ → ℂ} {n j : ℕ} (hj : j < n)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    |(w (j + 1)).re - (w j).re - 1| ≤ 1 / 32 ∧ |(w (j + 1)).im - (w j).im| ≤ 1 / 32 := by
  have h := hstep j hj
  have hre : (w (j + 1) - (w j + 1)).re = (w (j + 1)).re - (w j).re - 1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (w (j + 1) - (w j + 1)).im = (w (j + 1)).im - (w j).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.one_im, add_zero]
  constructor
  · calc |(w (j + 1)).re - (w j).re - 1| = |(w (j + 1) - (w j + 1)).re| := by rw [hre]
      _ ≤ ‖w (j + 1) - (w j + 1)‖ := Complex.abs_re_le_norm _
      _ ≤ 1 / 32 := h
  · calc |(w (j + 1)).im - (w j).im| = |(w (j + 1) - (w j + 1)).im| := by rw [him]
      _ ≤ ‖w (j + 1) - (w j + 1)‖ := Complex.abs_im_le_norm _
      _ ≤ 1 / 32 := h

/-- A walk with steps `≥ c` grows at least linearly. -/
lemma walk_re_mono_add {x : ℕ → ℝ} {k : ℕ} {c : ℝ} (hx : ∀ j < k, x j + c ≤ x (j + 1)) :
    ∀ i j, i ≤ j → j ≤ k → x i + ((j - i : ℕ) : ℝ) * c ≤ x j := by
  intro i j hij hjk
  have key : ∀ m ≤ k, ∀ i, i ≤ m → x i + ((m - i : ℕ) : ℝ) * c ≤ x m := by
    intro m
    induction m with
    | zero => intro _ i hi; interval_cases i; simp
    | succ m ih =>
      intro hmk i hi
      rcases eq_or_lt_of_le hi with h | h
      · subst h; simp
      · have him : i ≤ m := Nat.lt_succ_iff.mp h
        have h1 := ih (le_trans (Nat.le_succ m) hmk) i him
        have h2 := hx m (Nat.lt_of_succ_le hmk)
        have hsub : ((m + 1 - i : ℕ) : ℝ) = ((m - i : ℕ) : ℝ) + 1 := by
          rw [Nat.succ_sub him, Nat.cast_succ]
        rw [hsub, add_mul, one_mul]
        linarith
  exact key j hjk i hij

/-- A walk whose steps have absolute value `≤ c` stays within `j * c` of its starting point. -/
lemma walk_abs_mono {y : ℕ → ℝ} {k : ℕ} {c : ℝ} (hy : ∀ j < k, |y (j + 1) - y j| ≤ c) :
    ∀ j ≤ k, |y j - y 0| ≤ (j : ℝ) * c := by
  intro j hj
  have key : ∀ m ≤ k, |y m - y 0| ≤ (m : ℝ) * c := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hm' : m ≤ k := le_trans (Nat.le_succ m) hm
      have h2 := hy m (Nat.lt_of_succ_le hm)
      have h3 := ih hm'
      have hcast : ((m : ℝ) + 1) * c = (m : ℝ) * c + c := by ring
      rw [Nat.cast_succ, hcast]
      have h4 : |y (m + 1) - y 0| ≤ |y (m + 1) - y m| + |y m - y 0| := by
        have h := abs_add_le (y (m+1) - y m) (y m - y 0)
        simpa [sub_add_sub_cancel] using h
      linarith
  exact key j hj

/-- `Im (α * w j)` moves by `≤ ‖α‖/16` around `α.im`. -/
lemma vshape_step {α : ℂ} {w : ℕ → ℂ} {n j : ℕ} (hj : j < n)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    |(α * w (j + 1)).im - (α * w j).im - α.im| ≤ ‖α‖ / 16 := by
  obtain ⟨h1, h2⟩ := step_parts hj hstep
  have himge : (α * w (j+1)).im - (α * w j).im
      = α.re * ((w (j+1)).im - (w j).im) + α.im * ((w (j+1)).re - (w j).re) := by
    simp only [Complex.mul_im]; ring
  have hsplit : (α * w (j+1)).im - (α * w j).im - α.im
      = α.re * ((w (j+1)).im - (w j).im) + α.im * ((w (j+1)).re - (w j).re - 1) := by
    rw [himge]; ring
  rw [hsplit]
  have ha : |α.re| ≤ ‖α‖ := Complex.abs_re_le_norm α
  have hb : |α.im| ≤ ‖α‖ := Complex.abs_im_le_norm α
  calc |α.re * ((w (j+1)).im - (w j).im) + α.im * ((w (j+1)).re - (w j).re - 1)|
      ≤ |α.re * ((w (j+1)).im - (w j).im)| + |α.im * ((w (j+1)).re - (w j).re - 1)| :=
        abs_add_le _ _
    _ = |α.re| * |(w (j+1)).im - (w j).im| + |α.im| * |(w (j+1)).re - (w j).re - 1| := by
        rw [abs_mul, abs_mul]
    _ ≤ ‖α‖ * (1/32) + ‖α‖ * (1/32) := by
        have h0 : (0:ℝ) ≤ ‖α‖ := norm_nonneg α
        nlinarith [abs_nonneg ((w (j+1)).im - (w j).im),
                   abs_nonneg ((w (j+1)).re - (w j).re - 1)]
    _ = ‖α‖ / 16 := by ring

/-- From `M / r ≤ d` (`r, M, d > 0`) conclude `1 / d ≤ r / M`. -/
private lemma one_div_le_of_div_le {d r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (h : M / r ≤ d) : 1 / d ≤ r / M := by
  have hd : 0 < d := lt_of_lt_of_le (div_pos hM hr) h
  rw [div_le_div_iff₀ hd hM]
  have h' : M ≤ d * r := (div_le_iff₀ hr).mp h
  linarith

/-- `log (2 + a * b) ≤ log 2 + log (2 + a) + log (2 + b)` for `a, b ≥ 0`. -/
lemma log_two_add_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (2 + a * b) ≤ Real.log 2 + Real.log (2 + a) + Real.log (2 + b) := by
  have h2a : (0:ℝ) < 2 + a := by linarith
  have h2b : (0:ℝ) < 2 + b := by linarith
  have hab : (0:ℝ) ≤ a * b := mul_nonneg ha hb
  have hpos : (0:ℝ) < 2 + a * b := by linarith
  have hle : 2 + a * b ≤ 2 * (2 + a) * (2 + b) := by nlinarith
  calc Real.log (2 + a * b) ≤ Real.log (2 * (2 + a) * (2 + b)) := Real.log_le_log hpos hle
    _ = Real.log 2 + Real.log (2 + a) + Real.log (2 + b) := by
        rw [Real.log_mul (by positivity) (ne_of_gt h2b), Real.log_mul (by norm_num) (ne_of_gt h2a)]

/-- `2 + 2/(Ξ*r) ≤ 4*(2 + 1/Ξ)*(2 + 1/r)`. -/

lemma log4_le_two : Real.log 4 ≤ 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  rw [h]; linarith

lemma log12_le_four : Real.log 12 ≤ 4 := by
  have h : Real.log 12 = Real.log 3 + Real.log 4 := by
    rw [show (12:ℝ) = 3*4 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  rw [h]; linarith [log4_le_two]

/-- Numeric bound in case `|Im α| ≤ ‖α‖/8` and `‖α‖·|Im w 0| < 1`. -/
lemma A2_numeric {Ξ r W : ℝ} (hΞ : 0 < Ξ) (hr : 0 < r) (hW : 0 ≤ W) :
    10.4 * (2.1 * (2 + Real.log (2 + 2/(Ξ*r))) + 2/Ξ)
      ≤ 200 * (1 + 1/Ξ) * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
  have hL1 : (0:ℝ) ≤ Real.log (2 + 1/Ξ) := Real.log_nonneg (by have := one_div_pos.mpr hΞ; linarith)
  have hL2 : (0:ℝ) ≤ Real.log (2 + 1/r) := Real.log_nonneg (by have := one_div_pos.mpr hr; linarith)
  have hL3 : (0:ℝ) ≤ Real.log (2 + W) := Real.log_nonneg (by linarith)
  have hkey := two_add_two_div_le hΞ hr
  have h5 : (0:ℝ) < 2 + 2/(Ξ*r) := by positivity
  have h6 : Real.log (2 + 2/(Ξ*r)) ≤ Real.log 4 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) := by
    calc Real.log (2 + 2/(Ξ*r)) ≤ Real.log (4 * (2 + 1/Ξ) * (2 + 1/r)) := Real.log_le_log h5 hkey
      _ = Real.log 4 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  have hlog : 2 + Real.log (2 + 2/(Ξ*r))
      ≤ 8 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
    linarith [h6, log4_le_two, hL1, hL2, hL3]
  have hT1 : (1:ℝ) ≤ 1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W) := by linarith
  have hXi : 2/Ξ ≤ 2 * (1 + 1/Ξ) := by
    have h : (2:ℝ) * (1 + 1/Ξ) = 2 + 2/Ξ := by ring
    rw [h]; linarith [one_div_pos.mpr hΞ]
  have hG : (1:ℝ) ≤ 1 + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
  have step1 : 10.4 * (2.1 * (2 + Real.log (2 + 2/(Ξ*r))) + 2/Ξ)
      ≤ 10.4 * (2.1 * (8 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)))
          + 2 * (1 + 1/Ξ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (mul_le_mul_of_nonneg_left hlog (by norm_num)) hXi
  have step2 : 10.4 * (2.1 * (8 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)))
        + 2 * (1 + 1/Ξ))
      ≤ 196 * (1 + 1/Ξ) * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
    nlinarith [hT1, hG]
  have step3 : (196:ℝ) * (1 + 1/Ξ) * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W))
      ≤ 200 * (1 + 1/Ξ) * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
    have : (0:ℝ) ≤ (1 + 1/Ξ) * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by positivity
    nlinarith
  linarith [step1, step2, step3]

/-- Numeric bound in case `‖α‖/8 < |Im α|`. -/
lemma B_numeric {Ξ r W M n : ℝ} (hΞ : 0 < Ξ) (hr : 0 < r) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hn : 0 ≤ n) (hMW : M ≤ W + 1.1 * n) (hn4 : n ≤ 4 * W + 4 / r) :
    32 * (2 + Real.log (1 + 2 * M / (Ξ * r))) + 4 / Ξ
      ≤ 520 * (1 + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + W)) := by
  have hL1 : (0:ℝ) ≤ Real.log (2 + 1/Ξ) := Real.log_nonneg (by have := one_div_pos.mpr hΞ; linarith)
  have hL2 : (0:ℝ) ≤ Real.log (2 + 1/r) := Real.log_nonneg (by have := one_div_pos.mpr hr; linarith)
  have hL3 : (0:ℝ) ≤ Real.log (2 + W) := Real.log_nonneg (by linarith)
  have hΞr : (0:ℝ) < Ξ * r := mul_pos hΞ hr
  have ht : (0:ℝ) < 1/(Ξ*r) := one_div_pos.mpr hΞr
  have harg : 1 + 2 * M / (Ξ * r) ≤ 3 * (2 + 1/(Ξ*r)) * (2 + M) := by
    have h1 : (2:ℝ)*M/(Ξ*r) = 2*M*(1/(Ξ*r)) := by ring
    rw [h1]; nlinarith [ht, hM]
  have hlog1 : Real.log (1 + 2 * M / (Ξ * r))
      ≤ Real.log 3 + Real.log (2 + 1/(Ξ*r)) + Real.log (2 + M) := by
    have hp : (0:ℝ) < 1 + 2*M/(Ξ*r) := by positivity
    have h2 : (0:ℝ) < 2 + 1/(Ξ*r) := by linarith
    have h4 : (0:ℝ) < 2 + M := by linarith
    calc Real.log (1 + 2 * M / (Ξ*r)) ≤ Real.log (3 * (2 + 1/(Ξ*r)) * (2 + M)) :=
          Real.log_le_log hp harg
      _ = Real.log 3 + Real.log (2 + 1/(Ξ*r)) + Real.log (2 + M) := by
          rw [Real.log_mul (by positivity) (ne_of_gt h4), Real.log_mul (by norm_num) (ne_of_gt h2)]
  have hlog2 : Real.log (2 + 1/(Ξ*r)) ≤ 2 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) := by
    have hkey := two_add_two_div_le hΞ hr
    have hh : 1/(Ξ*r) ≤ 2/(Ξ*r) := by rw [div_le_div_iff_of_pos_right hΞr]; norm_num
    have hkey' : 2 + 1/(Ξ*r) ≤ 4 * (2 + 1/Ξ) * (2 + 1/r) := by linarith
    have h5 : (0:ℝ) < 2 + 1/(Ξ*r) := by linarith
    calc Real.log (2 + 1/(Ξ*r)) ≤ Real.log (4 * (2 + 1/Ξ) * (2 + 1/r)) := Real.log_le_log h5 hkey'
      _ = Real.log 4 + Real.log (2+1/Ξ) + Real.log (2+1/r) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
      _ ≤ 2 + Real.log (2+1/Ξ) + Real.log (2+1/r) := by linarith [log4_le_two]
  have hlog3 : Real.log (2 + M) ≤ 2 + Real.log (2 + W) + Real.log (2 + n) := by
    have h5 : (0:ℝ) < 2 + M := by linarith
    have h6 : 2 + M ≤ 4 * (2 + W) * (2 + n) := by nlinarith [hMW, hW, hn]
    calc Real.log (2 + M) ≤ Real.log (4 * (2 + W) * (2 + n)) := Real.log_le_log h5 h6
      _ = Real.log 4 + Real.log (2 + W) + Real.log (2 + n) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
      _ ≤ 2 + Real.log (2 + W) + Real.log (2 + n) := by linarith [log4_le_two]
  have hlog4 : Real.log (2 + n) ≤ 4 + Real.log (2 + W) + Real.log (2 + 1/r) := by
    have h5 : (0:ℝ) < 2 + n := by linarith
    have h1r : (0:ℝ) < 1/r := one_div_pos.mpr hr
    have hexp : 12 * (2 + W) * (2 + 1/r) = 48 + 24*W + 24*(1/r) + 12*W*(1/r) := by ring
    have h6 : 2 + n ≤ 12 * (2 + W) * (2 + 1/r) := by
      rw [hexp]
      have hWr : (0:ℝ) ≤ 12*W*(1/r) := by positivity
      have h4r : (4:ℝ)/r = 4*(1/r) := by ring
      nlinarith [hn4, hW, h1r, hWr, h4r]
    calc Real.log (2 + n) ≤ Real.log (12 * (2 + W) * (2 + 1/r)) := Real.log_le_log h5 h6
      _ = Real.log 12 + Real.log (2 + W) + Real.log (2 + 1/r) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
      _ ≤ 4 + Real.log (2 + W) + Real.log (2 + 1/r) := by linarith [log12_le_four]
  have hlog3' : Real.log (2 + M) ≤ 6 + 2 * Real.log (2 + W) + Real.log (2 + 1/r) := by
    linarith [hlog3, hlog4]
  have h3' : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have hlogtot : Real.log (1 + 2 * M / (Ξ * r))
      ≤ 10 + Real.log (2+1/Ξ) + 2*Real.log (2+1/r) + 2*Real.log (2+W) := by
    linarith [hlog1, hlog2, hlog3', h3']
  have hlogtot2 : Real.log (1 + 2 * M / (Ξ * r))
      ≤ 10 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
    linarith [hlogtot, hL1, hL2, hL3]
  have hbig : 2 + Real.log (1 + 2 * M / (Ξ * r))
      ≤ 12 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
    linarith [hlogtot2, hL1, hL2, hL3]
  have hXi : 4/Ξ ≤ 4 * (1 + 1/Ξ) := by
    have h : (4:ℝ) * (1 + 1/Ξ) = 4 + 4/Ξ := by ring
    rw [h]; linarith [one_div_pos.mpr hΞ]
  have hG : (1:ℝ) ≤ 1 + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
  have hT1 : (1:ℝ) ≤ 1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W) := by linarith
  have step1 : 32 * (2 + Real.log (1 + 2 * M / (Ξ*r))) + 4/Ξ
      ≤ 32 * (12 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W))) + 4 * (1 + 1/Ξ) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hbig (by norm_num)
    · exact hXi
  have step2 : 32 * (12 * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W))) + 4 * (1 + 1/Ξ)
      ≤ 520 * (1 + 1/Ξ) * (1 + Real.log (2+1/Ξ) + Real.log (2+1/r) + Real.log (2+W)) := by
    nlinarith [hT1, hG]
  linarith [step1, step2]

theorem lattice_sum_le {α : ℂ} {Ξ : ℝ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hstep : ∀ j < n, ‖w (j+1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
      ≤ 2 ^ 20 * (1 + Ξ + 1 / Ξ)
          * (1 + Real.log (2 + 1 / Ξ) + Real.log (2 + 1 / ‖α‖) + Real.log (2 + ‖w 0‖)) := by
  have hαne : α ≠ 0 := InF1_ne_zero hInF1
  have hαre : 0 < α.re := InF1_re_pos hInF1
  set r : ℝ := ‖α‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hαne
  have hr64 : r ≤ 1 / 64 := by rw [hr]; exact hα64
  have hre_le : α.re ≤ r := by rw [hr]; exact Complex.re_le_norm α
  have hb_le : |α.im| ≤ r := by rw [hr]; exact Complex.abs_im_le_norm α
  have hb1 : -r ≤ α.im := (abs_le.mp hb_le).1
  have hb2 : α.im ≤ r := (abs_le.mp hb_le).2
  have hinvre : (1 / α).re ≤ 1 / r := by rw [hr]; exact inv_re_le hαne
  have hW : (0:ℝ) ≤ ‖w 0‖ := norm_nonneg _
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [Finset.range_zero, Finset.sum_empty]
    have h2 : (0:ℝ) < 1 + Ξ + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
    have h3 : (0:ℝ) ≤ Real.log (2 + 1/Ξ) := Real.log_nonneg (by have := one_div_pos.mpr hΞ; linarith)
    have h4 : (0:ℝ) ≤ Real.log (2 + 1/‖α‖) := by
      apply Real.log_nonneg
      have : (0:ℝ) ≤ 1/‖α‖ := by positivity
      linarith
    have h5 : (0:ℝ) ≤ Real.log (2 + ‖w 0‖) := Real.log_nonneg (by linarith [hW])
    have h6 : (0:ℝ) < (2:ℝ)^20 := by norm_num
    positivity
  -- ============ main case ============
  set H : ℝ := Ξ * r / 2 with hHdef
  have hHpos : 0 < H := by rw [hHdef]; positivity
  have hHr : H / r = Ξ / 2 := by rw [hHdef]; field_simp
  have hstepre : ∀ j < n, |(w (j+1)).re - (w j).re - 1| ≤ 1/32 := fun j hj => (step_parts hj hstep).1
  have hstepim : ∀ j < n, |(w (j+1)).im - (w j).im| ≤ 1/32 := fun j hj => (step_parts hj hstep).2
  have hre_step : ∀ j < n, (w j).re + 31/32 ≤ (w (j+1)).re := by
    intro j hj
    have h := hstepre j hj
    obtain ⟨h1, _⟩ := abs_le.mp h
    linarith
  have him0 : ∀ j ≤ n, |(w j).im - (w 0).im| ≤ (j:ℝ) * (1/32) :=
    fun j hj => walk_abs_mono (y := fun j => (w j).im) (k := n) (c := 1/32) hstepim j hj
  have hre0' : (w 0).re + (n:ℝ) * (31/32) ≤ (w n).re := by
    have h := walk_re_mono_add hre_step 0 n (Nat.zero_le n) (le_refl n)
    simpa using h
  have hgate_re : ∀ j ≤ n, |(w j).re| ≤ |(w j).im| + 2 * (1/α).re :=
    fun j hj => gate_abs_re_le hΞ hInF1 (hgate j hj)
  have hgate_hi : ∀ j ≤ n, (w j).re ≤ |(w j).im| - Ξ :=
    fun j hj => le_of_lt ((Qm_mem_iff (ξ := Ξ) (α := α) (z := w j)).mp (hgate j hj)).2
  have hgate_lo : ∀ j ≤ n, -(2 * (1/α).re) - |(w j).im| ≤ (w j).re := by
    intro j hj
    have h := hgate_re j hj
    obtain ⟨h1, _⟩ := abs_le.mp h
    linarith
  have h2invre : 2 * (1/α).re ≤ 2 / r := by
    have h := mul_le_mul_of_nonneg_left hinvre (by norm_num : (0:ℝ) ≤ 2)
    have h' : 2 * (1/r) = 2/r := by ring
    linarith
  -- room bound
  have hnest : |(w n).im| ≤ |(w 0).im| + (n:ℝ) * (1/32) := by
    have h := him0 n (le_refl n)
    obtain ⟨h1, h2⟩ := abs_le.mp h
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [h1, neg_abs_le (w 0).im]
    · linarith [h2, le_abs_self (w 0).im]
  have hroom : (n:ℝ) * (30/32) < 2 * |(w 0).im| + 2 / r := by
    have h1 := hgate_hi n (le_refl n)
    have h2 := hgate_lo 0 (Nat.zero_le n)
    have h3 : -(w 0).re ≤ 2 / r + |(w 0).im| := by linarith
    have h4 := hre0'
    linarith
  have hn4 : (n:ℝ) ≤ 4 * |(w 0).im| + 4 / r := by
    have h2 : (30:ℝ)/32 = 15/16 := by norm_num
    rw [h2] at hroom
    have h1 : (n:ℝ) * (15/16) ≤ 2 * |(w 0).im| + 2 / r := le_of_lt hroom
    have hn' : (n:ℝ) ≤ (2 * |(w 0).im| + 2 / r) / (15/16) :=
      (le_div_iff₀ (by norm_num : (0:ℝ) < 15/16)).mpr h1
    have he : (2 * |(w 0).im| + 2 / r) / (15/16) = (16/15) * (2 * |(w 0).im| + 2 / r) := by ring
    have hA : (0:ℝ) ≤ 2 * |(w 0).im| + 2 / r := by positivity
    rw [he] at hn'
    have hlin : (16/15) * (2 * |(w 0).im| + 2 / r) ≤ 4 * |(w 0).im| + 4 / r := by
      have h1 : (0:ℝ) ≤ (14/15) * (2 * |(w 0).im| + 2 / r) := mul_nonneg (by norm_num) hA
      have h2 : (14/15) * (2 * |(w 0).im| + 2 / r) = 28/15 * |(w 0).im| + (28/15)/r := by ring
      rw [h2] at h1
      have h3 : (28/15)/r = (28/15) * (1/r) := by ring
      rw [h3] at h1
      have h4 : (4:ℝ)/r = 4 * (1/r) := by ring
      rw [h4]
      linarith
    linarith [hn', hlin]
  -- ============ per-term bounds ============
  have keyY : ∀ j, j < n → 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) ≤ r / max |(α * w j).im| H := by
    intro j hj
    have hjn : j ≤ n := le_of_lt hj
    have hdge : Ξ / 2 ≤ (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) := by
      refine le_ciInf (fun k => ?_)
      simpa only [dist_eq_norm] using (scale_lattice hΞ hInF1).2 (hgate j hjn) k
    have hdY : |(α * w j).im| / r ≤ (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) := by
      refine le_ciInf (fun k => ?_)
      rw [dist_eq_norm, div_le_iff₀ hrpos]
      have hmul : α * (w j - (k : ℂ) / α) = α * w j - (k : ℂ) := by field_simp
      calc |(α * w j).im| = |(α * (w j - (k : ℂ) / α)).im| := by rw [hmul]; simp
        _ ≤ ‖α * (w j - (k : ℂ) / α)‖ := Complex.abs_im_le_norm _
        _ = r * ‖w j - (k : ℂ) / α‖ := by rw [norm_mul, hr]
        _ = ‖w j - (k : ℂ) / α‖ * r := by ring
    have hM : max |(α * w j).im| H / r ≤ (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) := by
      rw [div_le_iff₀ hrpos]
      refine max_le ?_ ?_
      · exact (div_le_iff₀ hrpos).mp hdY
      · exact (div_le_iff₀ hrpos).mp (le_trans (le_of_eq hHr) hdge)
    exact one_div_le_of_div_le hrpos (lt_max_of_lt_right hHpos) hM
  have keyS : ∀ j, j < n →
      1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α))
        ≤ r / max (Metric.infDist ((α * w j).re) (Set.range (fun k : ℤ => (k : ℝ)))) H := by
    intro j hj
    have hjn : j ≤ n := le_of_lt hj
    have hdge : Ξ / 2 ≤ (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) := by
      refine le_ciInf (fun k => ?_)
      simpa only [dist_eq_norm] using (scale_lattice hΞ hInF1).2 (hgate j hjn) k
    have hdS : Metric.infDist ((α * w j).re) (Set.range (fun k : ℤ => (k : ℝ))) / r
        ≤ (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) := by
      refine le_ciInf (fun k => ?_)
      rw [dist_eq_norm, div_le_iff₀ hrpos]
      have hmul : α * (w j - (k : ℂ) / α) = α * w j - (k : ℂ) := by field_simp
      have hinf : Metric.infDist ((α * w j).re) (Set.range (fun k : ℤ => (k : ℝ)))
          ≤ |(α * w j).re - (k : ℝ)| := Metric.infDist_le_dist_of_mem ⟨k, rfl⟩
      have h1 : |(α * w j).re - (k : ℝ)| ≤ ‖α * w j - (k : ℂ)‖ := by
        have h2 : (α * w j - (k : ℂ)).re = (α * w j).re - (k : ℝ) := by simp
        rw [← h2]
        exact Complex.abs_re_le_norm _
      have h3 : ‖α * w j - (k : ℂ)‖ = ‖α * (w j - (k : ℂ) / α)‖ := by rw [hmul]
      calc Metric.infDist ((α * w j).re) (Set.range (fun k : ℤ => (k : ℝ)))
          ≤ |(α * w j).re - (k : ℝ)| := hinf
        _ ≤ ‖α * w j - (k : ℂ)‖ := h1
        _ = r * ‖w j - (k : ℂ) / α‖ := by rw [h3, norm_mul, hr]
        _ = ‖w j - (k : ℂ) / α‖ * r := by ring
    have hM : max (Metric.infDist ((α * w j).re) (Set.range (fun k : ℤ => (k : ℝ)))) H / r
        ≤ (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) := by
      rw [div_le_iff₀ hrpos]
      refine max_le ?_ ?_
      · exact (div_le_iff₀ hrpos).mp hdS
      · exact (div_le_iff₀ hrpos).mp (le_trans (le_of_eq hHr) hdge)
    exact one_div_le_of_div_le hrpos (lt_max_of_lt_right hHpos) hM
  -- ============ final comparison helper ============
  have hfin : ∀ C : ℝ, C ≤ 2^20 → C * (1 + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r)
        + Real.log (2 + ‖w 0‖))
      ≤ 2^20 * (1 + Ξ + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/‖α‖) + Real.log (2 + ‖w 0‖)) := by
    intro C hC
    have hG1 : (1:ℝ) ≤ 1 + Ξ + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
    have hG2 : (1 + 1/Ξ : ℝ) ≤ 1 + Ξ + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
    have hL1 : (0:ℝ) ≤ Real.log (2 + 1/Ξ) := Real.log_nonneg (by have := one_div_pos.mpr hΞ; linarith)
    have hL2 : (0:ℝ) ≤ Real.log (2 + 1/r) := Real.log_nonneg (by have := one_div_pos.mpr hrpos; linarith)
    have hL3 : (0:ℝ) ≤ Real.log (2 + ‖w 0‖) := Real.log_nonneg (by linarith [hW])
    have hT1 : (0:ℝ) ≤ 1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖) :=
      add_nonneg (add_nonneg (add_nonneg (by norm_num : (0:ℝ) ≤ 1) hL1) hL2) hL3
    have hT2 : (0:ℝ) ≤ 1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/‖α‖) + Real.log (2 + ‖w 0‖) := by
      have : Real.log (2 + 1/r) = Real.log (2 + 1/‖α‖) := by rw [hr]
      rw [← this]; linarith
    have hswap : C * (1 + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖))
        ≤ 2^20 * (1 + Ξ + 1/Ξ)
          * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖)) := by
      have hpos2 : (0:ℝ) < 1 + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
      have h1 : C * (1 + 1/Ξ) ≤ 2^20 * (1 + Ξ + 1/Ξ) := by
        calc C * (1 + 1/Ξ) ≤ 2^20 * (1 + 1/Ξ) := mul_le_mul_of_nonneg_right hC (le_of_lt hpos2)
          _ ≤ 2^20 * (1 + Ξ + 1/Ξ) := mul_le_mul_of_nonneg_left hG2 (by norm_num)
      calc C * (1 + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖))
          ≤ (2^20 * (1 + Ξ + 1/Ξ))
            * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖)) :=
            mul_le_mul_of_nonneg_right h1 hT1
        _ = 2^20 * (1 + Ξ + 1/Ξ)
            * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖)) := by ring
    rw [show Real.log (2 + 1/‖α‖) = Real.log (2 + 1/r) from by rw [hr]]
    exact hswap
  by_cases hbsmall : |α.im| ≤ r / 8
  · -- ===== CASE A : |Im α| ≤ r/8 =====
    have ha : 0.99 * r ≤ α.re := by
      have h1 : α.re ^ 2 + α.im ^ 2 = r ^ 2 := by
        rw [hr, Complex.sq_norm, Complex.normSq_apply]; ring
      have h2 : α.im ^ 2 ≤ (r/8)^2 := by
        rw [show α.im ^ 2 = |α.im|^2 by rw [sq_abs]]
        exact pow_le_pow_left₀ (abs_nonneg _) hbsmall 2
      nlinarith [h1, h2, hαre, hrpos]
    have hbq : 2 * |α.im| * (1/α).re ≤ 0.26 := by
      have h4 : (0:ℝ) ≤ (1/α).re := le_of_lt (inv_re_pos hInF1)
      have h5 : 2 * |α.im| * (1/α).re ≤ 2 * (r/8) * (1/r) := by
        apply mul_le_mul
        · linarith
        · exact hinvre
        · exact h4
        · positivity
      have h6 : 2 * (r/8) * (1/r) = 1/4 := by field_simp; ring
      linarith
    have hYlow : ∀ j ≤ n, 0.75 * r * |(w 0).im| - 0.4 ≤ |(α * w j).im| := by
      intro j hj
      have hx := hgate_re j hj
      have hy := him0 j hj
      have hy' : |(w 0).im| - (j:ℝ) * (1/32) ≤ |(w j).im| := by
        have h : |(w 0).im| - |(w j).im| ≤ |(w 0).im - (w j).im| := abs_sub_abs_le_abs_sub _ _
        have h2 : |(w 0).im - (w j).im| ≤ (j:ℝ) * (1/32) := by rw [abs_sub_comm]; exact hy
        linarith
      have hjn' : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hj
      have hj32 : (j:ℝ) * (1/32) ≤ (4 * |(w 0).im| + 4 / r) * (1/32) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        linarith [hn4, hjn']
      have hY : |(α * w j).im| = |α.re * (w j).im + α.im * (w j).re| := by
        rw [show (α * w j).im = α.re * (w j).im + α.im * (w j).re by
          simp only [Complex.mul_im]]
      have habs : α.re * |(w j).im| - |α.im| * |(w j).re| ≤ |(α * w j).im| := by
        rw [hY]
        have h1 : |α.re * (w j).im + α.im * (w j).re| ≥ |α.re * (w j).im| - |α.im * (w j).re| :=
          abs_sub_abs_le_abs_add _ _
        rw [abs_mul, abs_mul, abs_of_pos hαre] at h1
        linarith
      have hbnd : α.re * |(w j).im| - |α.im| * (|(w j).im| + 2 * (1/α).re)
          ≤ α.re * |(w j).im| - |α.im| * |(w j).re| := by
        have h := mul_le_mul_of_nonneg_left hx (abs_nonneg α.im)
        linarith
      have hcombo : (α.re - |α.im|) * |(w j).im| - 2 * |α.im| * (1/α).re ≤ |(α * w j).im| := by
        nlinarith [habs, hbnd]
      have hcoef : 0.86 * r ≤ α.re - |α.im| := by linarith [ha, hbsmall]
      have hy0nn : (0:ℝ) ≤ |(w 0).im| := abs_nonneg _
      have hstep1 : (0.86 * r) * (|(w 0).im| - (j:ℝ) * (1/32)) ≤ (α.re - |α.im|) * |(w j).im| := by
        refine le_trans (mul_le_mul_of_nonneg_left hy' (by positivity : (0:ℝ) ≤ 0.86 * r)) ?_
        exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      have hstep2 : (0.86 * r) * (|(w 0).im| - (4 * |(w 0).im| + 4 / r) * (1/32))
          ≤ (0.86 * r) * (|(w 0).im| - (j:ℝ) * (1/32)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hj32]
      have hfour : r * (4 / r) * (1/32) = 4 * (1/32) := by field_simp
      have hfinal_a : 0.75 * r * |(w 0).im| - 0.1075
          ≤ (0.86 * r) * (|(w 0).im| - (4 * |(w 0).im| + 4 / r) * (1/32)) := by
        have he : (0.86 * r) * (|(w 0).im| - (4 * |(w 0).im| + 4 / r) * (1/32))
            = 0.7525 * r * |(w 0).im| - 0.1075 := by
          field_simp
          ring
        rw [he]
        nlinarith [hy0nn, hrpos]
      linarith [hcombo, hstep1, hstep2, hfinal_a, hbq]
    by_cases hbig0 : 1 ≤ r * |(w 0).im|
    · -- ===== A1 : 1 ≤ r*|Im w 0| =====
      have hy0pos : 0 < |(w 0).im| := by
        rcases lt_or_ge 0 |(w 0).im| with h | h
        · exact h
        · have : r * |(w 0).im| ≤ 0 := by nlinarith [h, hrpos]
          linarith
      have hterm : ∀ j, j < n → 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)) ≤ 1 / (0.35 * |(w 0).im|) := by
        intro j hj
        refine le_trans (keyY j hj) ?_
        have hY := hYlow j (le_of_lt hj)
        have h1 : 0.35 * (r * |(w 0).im|) ≤ max |(α * w j).im| H := by
          have h2 : 0.35 * (r * |(w 0).im|) ≤ |(α * w j).im| := by nlinarith [hY, hbig0]
          exact le_trans h2 (le_max_left _ _)
        have hMpos : 0 < max |(α * w j).im| H := lt_max_of_lt_right hHpos
        have h3 : 0 < 0.35 * |(w 0).im| := by positivity
        rw [div_le_div_iff₀ hMpos h3]
        have hr1 : r ≤ 1 := by linarith [hr64]
        nlinarith [h1, hr1, le_of_lt hMpos]
      have hsum1 : (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
          ≤ (n:ℝ) * (1 / (0.35 * |(w 0).im|)) := by
        calc (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
            ≤ ∑ j ∈ Finset.range n, 1 / (0.35 * |(w 0).im|) :=
              Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
          _ = (n:ℝ) * (1 / (0.35 * |(w 0).im|)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn8 : (n:ℝ) ≤ 8 * |(w 0).im| := by
        have h : 1/r ≤ |(w 0).im| := (div_le_iff₀ hrpos).mpr (by linarith [hbig0])
        have h4 : (4:ℝ)/r ≤ 4 * |(w 0).im| := by
          have := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 4)
          rwa [mul_one_div] at this
        linarith [hn4, h4]
      have hA1 : (n:ℝ) * (1 / (0.35 * |(w 0).im|)) ≤ 8/0.35 := by
        have hC : 0 < 0.35 * |(w 0).im| := by positivity
        have h3 : (n:ℝ) * (1 / (0.35 * |(w 0).im|)) = (n:ℝ) / (0.35 * |(w 0).im|) := by ring
        rw [h3]
        have h1 : (n:ℝ) / (0.35 * |(w 0).im|) ≤ (8 * |(w 0).im|) / (0.35 * |(w 0).im|) :=
          div_le_div_of_nonneg_right hn8 (le_of_lt hC)
        have h2 : (8 * |(w 0).im|) / (0.35 * |(w 0).im|) = 8 / 0.35 := by
          field_simp
        linarith [h1, h2.le]
      refine le_trans (le_trans hsum1 hA1) ?_
      have h12 : (8:ℝ)/0.35 ≤ 2^20 := by norm_num
      have hG1 : (1:ℝ) ≤ 1 + Ξ + 1/Ξ := by have := one_div_pos.mpr hΞ; linarith
      have hT1 : (1:ℝ) ≤ 1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖) := by
        have hL1 : (0:ℝ) ≤ Real.log (2 + 1/Ξ) := Real.log_nonneg (by have := one_div_pos.mpr hΞ; linarith)
        have hL2 : (0:ℝ) ≤ Real.log (2 + 1/r) := Real.log_nonneg (by have := one_div_pos.mpr hrpos; linarith)
        have hL3 : (0:ℝ) ≤ Real.log (2 + ‖w 0‖) := Real.log_nonneg (by linarith [hW])
        linarith
      calc (8:ℝ)/0.35 ≤ 2^20 := h12
        _ = 2^20 * 1 * 1 := by ring
        _ ≤ 2^20 * (1 + Ξ + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖)) := by
            have hL2 : (0:ℝ) ≤ Real.log (2 + 1/r) := Real.log_nonneg (by have := one_div_pos.mpr hrpos; linarith)
            have hL3 : (0:ℝ) ≤ Real.log (2 + ‖w 0‖) := Real.log_nonneg (by linarith [hW])
            have hL1 : (0:ℝ) ≤ Real.log (2 + 1/Ξ) := Real.log_nonneg (by have := one_div_pos.mpr hΞ; linarith)
            have hT1' : (1:ℝ) ≤ 1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖) := by linarith
            have h2 : 2^20 * 1 ≤ 2^20 * (1 + Ξ + 1/Ξ) :=
              mul_le_mul_of_nonneg_left hG1 (by norm_num)
            calc 2^20 * 1 * 1 ≤ (2^20 * (1 + Ξ + 1/Ξ)) * 1 :=
                  mul_le_mul_of_nonneg_right h2 (by norm_num)
              _ ≤ (2^20 * (1 + Ξ + 1/Ξ))
                  * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/r) + Real.log (2 + ‖w 0‖)) :=
                  mul_le_mul_of_nonneg_left hT1' (by positivity)
        _ ≤ 2^20 * (1 + Ξ + 1/Ξ) * (1 + Real.log (2 + 1/Ξ) + Real.log (2 + 1/‖α‖) + Real.log (2 + ‖w 0‖)) := by
            rw [show Real.log (2 + 1/‖α‖) = Real.log (2 + 1/r) from by rw [hr]]
    · -- ===== A2 : r*|Im w 0| < 1 =====
      have hsmall1 : r * |(w 0).im| < 1 := lt_of_not_ge hbig0
      have hn8 : (n:ℝ) < 8 / r := by
        have h : |(w 0).im| < 1 / r := (lt_div_iff₀ hrpos).mpr (by linarith [hsmall1])
        have h4 : 4 * |(w 0).im| < (4:ℝ)/r := by
          have := mul_lt_mul_of_pos_left h (by norm_num : (0:ℝ) < 4)
          rwa [mul_one_div] at this
        have h8 : (8:ℝ)/r = 4/r + 4/r := by ring
        linarith [hn4, h4.le, h8.le, h8.ge]
      have hcellstep : ∀ j < n,
          (31/32) * α.re - (1/32) * |α.im| ≤ (α * w (j+1)).re - (α * w j).re
            ∧ (α * w (j+1)).re - (α * w j).re ≤ (33/32) * α.re + (1/32) * |α.im| := by
        intro j hj
        obtain ⟨h1, h2⟩ := step_parts hj hstep
        obtain ⟨h1a, h1b⟩ := abs_le.mp h1
        obtain ⟨h2a, h2b⟩ := abs_le.mp h2
        have hm : (α * w (j+1)).re - (α * w j).re
            = α.re * ((w (j+1)).re - (w j).re) - α.im * ((w (j+1)).im - (w j).im) := by
          simp only [Complex.mul_re]; ring
        have hia : -|α.im| ≤ α.im := neg_abs_le α.im
        have hib : α.im ≤ |α.im| := le_abs_self α.im
        constructor
        · rw [hm]; nlinarith [h1a, h2a, h2b, hαre, hia, hib]
        · rw [hm]; nlinarith [h1b, h2a, h2b, hαre, hia, hib]
      have hc0 : 0 < (31/32) * α.re - (1/32) * |α.im| := by
        have hb' : (1/32) * |α.im| ≤ (1/32) * (r/8) :=
          mul_le_mul_of_nonneg_left hbsmall (by norm_num)
        nlinarith [ha, hb']
      have hc1 : (33/32) * α.re + (1/32) * |α.im| < 1 := by
        nlinarith [hre_le, hbsmall, hr64]
      have h2c0 : 2 / ((31/32) * α.re - (1/32) * |α.im|) ≤ 2.1 / r := by
        have h1 : 0.9 * r ≤ (31/32) * α.re - (1/32) * |α.im| := by
          have hb' : (1/32) * |α.im| ≤ (1/32) * (r/8) :=
            mul_le_mul_of_nonneg_left hbsmall (by norm_num)
          nlinarith [ha, hb']
        rw [div_le_iff₀ hc0, div_mul_eq_mul_div, le_div_iff₀ hrpos]
        nlinarith [h1, hrpos]
      have hcells := lattice_cell_harmonic (m := fun j => (α * w j).re)
        (c₀ := (31/32) * α.re - (1/32) * |α.im|)
        (c₁ := (33/32) * α.re + (1/32) * |α.im|) (H := H) (n := n) hc0 hHpos hc1 hcellstep
      have hsumS : (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
          ≤ r * (((n:ℝ) * ((33/32) * α.re + (1/32) * |α.im|) + 2)
              * ((2 / ((31/32) * α.re - (1/32) * |α.im|)) * (2 + Real.log (2 + 1/H)) + 1/H)) := by
        calc (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
            ≤ ∑ j ∈ Finset.range n, r / max (Metric.infDist ((α * w j).re)
                (Set.range (fun k : ℤ => (k : ℝ)))) H :=
              Finset.sum_le_sum (fun j hj => keyS j (Finset.mem_range.mp hj))
          _ = r * ∑ j ∈ Finset.range n, 1 / max (Metric.infDist ((α * w j).re)
                (Set.range (fun k : ℤ => (k : ℝ)))) H := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [div_eq_mul_one_div]
          _ ≤ r * (((n:ℝ) * ((33/32) * α.re + (1/32) * |α.im|) + 2)
              * ((2 / ((31/32) * α.re - (1/32) * |α.im|)) * (2 + Real.log (2 + 1/H)) + 1/H)) := by
              apply mul_le_mul_of_nonneg_left hcells (le_of_lt hrpos)
      refine le_trans hsumS ?_
      have hc1r : (33/32) * α.re + (1/32) * |α.im| ≤ 1.04 * r := by
        nlinarith [hre_le, hbsmall]
      have hnc1 : (n:ℝ) * ((33/32) * α.re + (1/32) * |α.im|) + 2 ≤ 10.4 := by
        have h1 : (n:ℝ) * ((33/32) * α.re + (1/32) * |α.im|) ≤ (n:ℝ) * (1.04 * r) :=
          mul_le_mul_of_nonneg_left hc1r (Nat.cast_nonneg n)
        have h2 : (n:ℝ) * (1.04 * r) ≤ (8/r) * (1.04 * r) :=
          mul_le_mul_of_nonneg_right (le_of_lt hn8) (by positivity)
        have h3 : (8/r) * (1.04 * r) = 8.32 := by field_simp; norm_num
        linarith [h1, h2, h3.le]
      have h1H : 1 / H = 2 / (Ξ * r) := by rw [hHdef]; field_simp
      have h2c0' : 2 / ((31/32) * α.re - (1/32) * |α.im|) ≤ 2.1 / r := h2c0
      have hmid : ((n:ℝ) * ((33/32) * α.re + (1/32) * |α.im|) + 2)
            * ((2 / ((31/32) * α.re - (1/32) * |α.im|)) * (2 + Real.log (2 + 1/H)) + 1/H)
          ≤ 10.4 * (2.1 / r * (2 + Real.log (2 + 2/(Ξ*r))) + 2 / (Ξ * r)) := by
        rw [h1H]
        have hlog1 : (0:ℝ) ≤ Real.log (2 + 2/(Ξ*r)) := by
          apply Real.log_nonneg
          have : (0:ℝ) ≤ 2/(Ξ*r) := by positivity
          linarith
        have hpos1 : (0:ℝ) ≤ (2 / ((31/32) * α.re - (1/32) * |α.im|)) * (2 + Real.log (2 + 2/(Ξ*r))) + 2/(Ξ*r) := by
          positivity
        apply mul_le_mul hnc1 ?_ hpos1 (by norm_num)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right h2c0' (by linarith)
        · rfl
      have hscale : r * (10.4 * (2.1 / r * (2 + Real.log (2 + 2/(Ξ*r))) + 2 / (Ξ * r)))
          = 10.4 * (2.1 * (2 + Real.log (2 + 2/(Ξ*r))) + 2 / Ξ) := by
        field_simp
      have hA2 := A2_numeric (Ξ := Ξ) (r := r) (W := ‖w 0‖) hΞ hrpos hW
      linarith [hmid, hscale.le, hA2, mul_le_mul_of_nonneg_left hmid (le_of_lt hrpos),
                le_of_eq hscale, hfin 200 (by norm_num)]
  · -- ===== CASE B : r/8 < |Im α| =====
    have hbbig : r / 8 < |α.im| := lt_of_not_ge hbsmall
    have hvs : ∀ j < n, r/16 ≤ |(α * w (j+1)).im - (α * w j).im| := by
      intro j hj
      have h := vshape_step (α := α) hj hstep
      obtain ⟨h1, h2⟩ := abs_le.mp h
      have hlib : |α.im| - r/16 ≤ |(α * w (j+1)).im - (α * w j).im| := by
        rcases lt_or_ge 0 α.im with hp | hn
        · rw [abs_of_pos hp]
          linarith [le_abs_self ((α * w (j+1)).im - (α * w j).im)]
        · rw [abs_of_nonpos hn]
          linarith [neg_abs_le ((α * w (j+1)).im - (α * w j).im)]
      linarith
    have hdir : (∀ j < n, (α * w j).im ≤ (α * w (j+1)).im) ∨ (∀ j < n, (α * w (j+1)).im ≤ (α * w j).im) := by
      rcases lt_or_ge 0 α.im with hpos | hneg
      · left
        intro j hj
        have h := vshape_step (α := α) hj hstep
        obtain ⟨h1, h2⟩ := abs_le.mp h
        have h3 : r / 8 < α.im := by rw [abs_of_pos hpos] at hbbig; exact hbbig
        linarith
      · right
        intro j hj
        have h := vshape_step (α := α) hj hstep
        obtain ⟨h1, h2⟩ := abs_le.mp h
        have h3 : α.im < -(r / 8) := by rw [abs_of_nonpos hneg] at hbbig; linarith
        linarith
    have hstepB : ∀ i < n, |(α * w (i+1)).im - (α * w i).im| ≤ 1.0625 * r := by
      intro i hi
      have h := vshape_step (α := α) hi hstep
      obtain ⟨h1, h2⟩ := abs_le.mp h
      rw [abs_le]
      constructor <;> linarith [hb1, hb2]
    have hMbound : ∀ j ≤ n, |(α * w j).im| ≤ |(α * w 0).im| + 1.1 * (n:ℝ) * r := by
      intro j hj
      have h := walk_abs_mono (y := fun j => (α * w j).im) (k := n) (c := 1.0625 * r) hstepB j hj
      have hjn : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hj
      have h2 : (j:ℝ) * (1.0625 * r) ≤ (n:ℝ) * (1.1 * r) := by
        apply mul_le_mul hjn (by linarith) (by positivity) (Nat.cast_nonneg n)
      have h3 : (0:ℝ) ≤ |(α * w 0).im| := abs_nonneg _
      have hsub : |(α * w j).im| - |(α * w 0).im| ≤ |(α * w j).im - (α * w 0).im| :=
        abs_sub_abs_le_abs_sub _ _
      have h4 : 1.1 * (n:ℝ) * r = (n:ℝ) * (1.1 * r) := by ring
      nlinarith [h, h2, h3, hsub, h4]
    have hvsh := lattice_vshape_harmonic (Y := fun j => (α * w j).im) (ν := r/16) (H := H)
      (M := |(α * w 0).im| + 1.1 * (n:ℝ) * r) (n := n)
      (by positivity) hHpos (by positivity) hvs hdir (fun j hj => hMbound j (le_of_lt hj))
    have hsumB : (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
        ≤ r * ((2 / (r/16)) * (2 + Real.log (1 + (|(α * w 0).im| + 1.1 * (n:ℝ) * r) / H)) + 2 / H) := by
      calc (∑ j ∈ Finset.range n, 1 / (⨅ k : ℤ, dist (w j) ((k : ℂ) / α)))
          ≤ ∑ j ∈ Finset.range n, r / max |(α * w j).im| H :=
            Finset.sum_le_sum (fun j hj => keyY j (Finset.mem_range.mp hj))
        _ = r * ∑ j ∈ Finset.range n, 1 / max |(α * w j).im| H := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [div_eq_mul_one_div]
        _ ≤ r * ((2 / (r/16)) * (2 + Real.log (1 + (|(α * w 0).im| + 1.1 * (n:ℝ) * r) / H)) + 2 / H) := by
            apply mul_le_mul_of_nonneg_left hvsh (le_of_lt hrpos)
    refine le_trans hsumB ?_
    have h2H : (2:ℝ) / H = 4 / (Ξ * r) := by rw [hHdef]; field_simp; ring
    have hratio : (|(α * w 0).im| + 1.1 * (n:ℝ) * r) / H
        = 2 * (|(α * w 0).im| + 1.1 * (n:ℝ) * r) / (Ξ * r) := by
      rw [hHdef]; field_simp
    rw [h2H, hratio]
    have hcomb : r * (2 / (r/16) * (2 + Real.log (1 + 2 * (|(α * w 0).im| + 1.1 * (n:ℝ) * r) / (Ξ * r)))
          + 4 / (Ξ * r))
        = 32 * (2 + Real.log (1 + 2 * (|(α * w 0).im| + 1.1 * (n:ℝ) * r) / (Ξ * r))) + 4 / Ξ := by
      field_simp
      ring
    rw [hcomb]
    have hMn : (0:ℝ) ≤ |(α * w 0).im| + 1.1 * (n:ℝ) * r := by positivity
    have hMW : |(α * w 0).im| + 1.1 * (n:ℝ) * r ≤ ‖w 0‖ + 1.1 * (n:ℝ) := by
      have h4 : |(α * w 0).im| ≤ r * ‖w 0‖ := by
        calc |(α * w 0).im| ≤ ‖α * w 0‖ := Complex.abs_im_le_norm _
          _ = r * ‖w 0‖ := by rw [norm_mul, hr]
      have h5 : r * ‖w 0‖ ≤ ‖w 0‖ := by nlinarith [hr64, hW]
      have h6 : 1.1 * (n:ℝ) * r ≤ 1.1 * (n:ℝ) := by
        have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        nlinarith [hr64, hn0]
      linarith
    have hB := B_numeric (Ξ := Ξ) (r := r) (W := ‖w 0‖)
      (M := |(α * w 0).im| + 1.1 * (n:ℝ) * r) (n := (n:ℝ)) hΞ hrpos hW hMn
      (Nat.cast_nonneg n) hMW (by
        have hw0 : |(w 0).im| ≤ ‖w 0‖ := Complex.abs_im_le_norm _
        linarith [hn4, hw0])
    exact le_trans hB (hfin 520 (by norm_num))


end

end Work.Pert
