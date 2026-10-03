import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.low_margin_in_window
import Submission.Work.Pert.V5.clear_lattice_band
import Submission.Work.Pert.V5.clear_lattice_gate
import Submission.Work.Pert.V5.corridor_left_wk
import Submission.Work.Pert.V5.P_le_B_pin

/-!
# `Work.Pert.V5.W2.Setup` — common structural facts for the right corridor

The target `Work.Pert.V5.corridor_right_wk2` (the certificate consumed by `gate_lin_asm_gen` in the
case `z₀.re ≤ z.re`) is proved by a case analysis on the corridor

  `C := [x₀, x]` at height `y₀`,  `x = z.re`, `x₀ = z₀.re`, `y₀ = z₀.im`, `ℓ := x - x₀ ≥ 0`,

where `x` is a *band* abscissa (`-(Ξ+2^10+2M) ≤ x ≤ -(Ξ+2^10)`) and `z₀` is the pin
(`‖z₀ + M‖ ≤ Kp L`, `L := 1 + log (2+M)`).

Notation: `mgA Ξ α z = z.re - Ξ + (1/α).re + |z.im + (1/α).im|`, `mgB Ξ z = |z.im| - Ξ - z.re` (the
marginals of the gate `Qm Ξ α`), `A := (1/α).re`, `B := (1/α).im`; `µ := min (mgA) (mgB)` is a tent
on the corridor; `ξ_B := |y₀| - Ξ - √2 Rde` is where `mgB (· + i y₀)` crosses `√2 Rde`; and
`c := ((Ξ:ℂ) - 1/α).re + 1 = Ξ - A + 1` is the left edge of the window strip
`{z | c < z.re < -Ξ - 3}`, where `‖Φm' - 1‖ ≤ c₀` (`deriv_sub_one_le_window`).
-/

open Set Metric Filter
open scoped _root_.Topology

namespace Work.Pert.V5

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 1. The pin's coordinates and the length bound -/

/-- The pin bound in real coordinates. -/
theorem rw_pin_re_im {M Kp : ℝ} {z₀ : ℂ}
    (h : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    |z₀.re + M| ≤ Kp * (1 + Real.log (2 + M)) ∧
      |z₀.im| ≤ Kp * (1 + Real.log (2 + M)) := by
  have h1 : |(z₀ + (((M : ℝ)) : ℂ)).re| ≤ ‖z₀ + (((M : ℝ)) : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : |(z₀ + (((M : ℝ)) : ℂ)).im| ≤ ‖z₀ + (((M : ℝ)) : ℂ)‖ := Complex.abs_im_le_norm _
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, add_zero] at h1 h2
  exact ⟨le_trans h1 h, le_trans h2 h⟩

/-- **The corridor is no longer than the pin's displacement plus the band's width.** -/
lemma rw_len_le {Ξ M Kp : ℝ} {z₀ : ℂ} {x : ℝ}
    (hx : x ≤ -(Ξ + 2 ^ 10))
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    x - z₀.re ≤ Kp * (1 + Real.log (2 + M)) + M - Ξ - 2 ^ 10 := by
  obtain ⟨hre, _⟩ := rw_pin_re_im hpinbd
  have h : -(Kp * (1 + Real.log (2 + M))) ≤ z₀.re + M := (abs_le.mp hre).1
  linarith

/-! ## 2. Margins along the corridor -/

/-- `mgA` increases in the abscissa along a horizontal line. -/
lemma rw_mgA_mono {Ξ : ℝ} {α : ℂ} (s : ℝ) {x y : ℝ} (h : x ≤ y) :
    mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I) ≤ mgA Ξ α ((y : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgA_re_im, mgA_re_im]; linarith

/-- `mgB` decreases in the abscissa along a horizontal line. -/
lemma rw_mgB_anti {Ξ : ℝ} (s : ℝ) {x y : ℝ} (h : x ≤ y) :
    mgB Ξ ((y : ℂ) + (s : ℂ) * Complex.I) ≤ mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgB_re_im, mgB_re_im]; linarith

/-- The `mgA`-margin at the pin is a lower bound for `mgA` on the whole corridor. -/
lemma rw_mgA_corridor {Ξ : ℝ} {α : ℂ} {z₀ : ℂ} {x : ℝ} (hx₀ : z₀.re ≤ x) :
    mgA Ξ α z₀ ≤ mgA Ξ α ((x : ℂ) + (z₀.im : ℂ) * Complex.I) := by
  have h := rw_mgA_mono (Ξ := Ξ) (α := α) z₀.im hx₀
  rw [Complex.re_add_im] at h
  simpa using h

/-- The `mgB`-margin at the band abscissa is a lower bound for `mgB` on the whole corridor. -/
lemma rw_mgB_corridor {Ξ : ℝ} {z₀ : ℂ} {x : ℝ} (hx₀ : z₀.re ≤ x) :
    mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I) ≤ mgB Ξ z₀ := by
  have h := rw_mgB_anti (Ξ := Ξ) z₀.im hx₀
  rw [Complex.re_add_im] at h
  simpa using h

/-- The band's `mgB`-margin at any height. -/
lemma rw_band_mgB {Ξ M : ℝ} {α : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    {x s : ℝ} (hx : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hx' : x ≤ -(Ξ + 2 ^ 10)) :
    2 ^ 10 ≤ mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) :=
  (band_margins hΞ hM hInF1 hα hQAdm x s hx hx').2.1

/-! ## 3. The corridor in the gate -/

/-- **The whole corridor at height `y₀` lies in the gate.** -/
lemma rw_corridor_mem {Ξ M : ℝ} {α : ℂ} {z₀ : ℂ} {x : ℝ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hxlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hxhi : x ≤ -(Ξ + 2 ^ 10))
    (hx₀ : z₀.re ≤ x) {ξ : ℝ} (hξ : ξ ∈ Set.Icc z₀.re x) :
    ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
  have hA0 : 0 < mgA Ξ α z₀ := (mem_Qm_iff_mg.mp hz₀).1
  have hB0 : 2 ^ 10 ≤ mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I) :=
    rw_band_mgB hΞ hM hInF1 hα hQAdm hxlo hxhi
  have hAsh : mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
      = mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) + (ξ - z₀.re) :=
    mgA_shift (Ξ := Ξ) (α := α) (x := z₀.re) (x' := ξ) (y := z₀.im)
  have hBsh : mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
      = mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I) + (x - ξ) := by
    have h := mgB_shift (Ξ := Ξ) (x := x) (x' := ξ) (y := z₀.im)
    linarith
  have hz₀' : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = z₀ := Complex.re_add_im z₀
  rw [mem_Qm_iff_mg]
  refine ⟨?_, ?_⟩
  · rw [hAsh, hz₀']; linarith [hξ.1]
  · rw [hBsh]; linarith [hξ.2, hB0]

/-! ## 4. The bad (`mgB`-small) piece -/

/-- `mgB (ξ + i y₀) ≥ √2 Rde` for `ξ ≤ ξ_B`. -/
lemma rw_mgB_ge_of_le_xiB {Ξ Rde : ℝ} {y₀ ξ : ℝ}
    (h : ξ ≤ |y₀| - Ξ - Real.sqrt 2 * Rde) :
    Real.sqrt 2 * Rde ≤ mgB Ξ ((ξ : ℂ) + (y₀ : ℂ) * Complex.I) := by
  rw [mgB_re_im]; linarith

/-- `mgB (ξ + i y₀) < √2 Rde` for `ξ > ξ_B`. -/
lemma rw_mgB_lt_of_gt_xiB {Ξ Rde : ℝ} {y₀ ξ : ℝ}
    (h : |y₀| - Ξ - Real.sqrt 2 * Rde < ξ) :
    mgB Ξ ((ξ : ℂ) + (y₀ : ℂ) * Complex.I) < Real.sqrt 2 * Rde := by
  rw [mgB_re_im]; linarith

/-- **`ξ_B ≥ x₀`.**  Otherwise `mgB z₀ < √2 Rde`, contradicting the pin's clearing. -/
lemma rw_xiB_ge_x₀ {Ξ Rde : ℝ} {α : ℂ} {z₀ : ℂ}
    (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α) :
    z₀.re ≤ |z₀.im| - Ξ - Real.sqrt 2 * Rde := by
  have hpin := (zo_margins hRde hcl).2
  rw [mgB] at hpin
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 * Rde ≤ 2 * Rde := by nlinarith
  linarith

/-! ## 5. The two linear slots -/

/-- **The `|Im|`-slot pays `c₀ √2 Rde`** for free. -/
lemma rw_slot_bad {Rde t : ℝ} (hRde : 0 < Rde) (ht : 4 * Rde ≤ |t|) :
    (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde
      ≤ |t| / 8 - (1 / 150 + 1 / 31) * |t| := by
  have c0nn : (0 : ℝ) ≤ 1 / 150 + 1 / 31 := by norm_num
  have c0le : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 12 := by norm_num
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h1 : (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde ≤ (1 / 150 + 1 / 31) * 2 * Rde := by
    nlinarith [hRde, c0nn]
  have h2 : (1 / 150 + 1 / 31) * 2 * Rde ≤ |t| / 8 - (1 / 150 + 1 / 31) * |t| := by
    nlinarith [abs_nonneg t, ht, c0le, hRde]
  linarith

/-! ## 6. The `|Im|`+`Kp` slots pay `c₀ ℓ` in the long case -/

/-- **The window cost `c₀ ℓ` is paid by the `Kp`-slot in the long case.**  With `ℓ ≤ Kp L + M`
(`rw_len_le`) and `Kp L ≥ 16 M + 17 Ξ + 2^10`, one has `c₀ ℓ ≤ Kp 2^36 K L`. -/
lemma rw_slot_window {Ξ rr M Kp ℓ : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hKp : 0 ≤ Kp)
    (hlen : ℓ ≤ Kp * (1 + Real.log (2 + M)) + M)
    (hbig : 16 * M + 17 * Ξ + 2 ^ 10 ≤ Kp * (1 + Real.log (2 + M))) :
    (1 / 150 + 1 / 31) * ℓ
      ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
  set L : ℝ := 1 + Real.log (2 + M) with hL
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    linarith
  have hLnn : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hK1 : (1 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : (0 : ℝ) ≤ 1 / Ξ := div_nonneg zero_le_one (le_of_lt hΞ)
    have h2 : (0 : ℝ) ≤ 1 / rr := div_nonneg zero_le_one (le_of_lt hrr)
    linarith
  have hMnn : (0 : ℝ) ≤ M := by
    have h : (0 : ℝ) ≤ 2 ^ 10 := by norm_num
    linarith
  have hXinn : (0 : ℝ) ≤ Ξ := le_of_lt hΞ
  have hMle : 16 * M + 2 ^ 10 ≤ Kp * L := by linarith
  have hMle' : 16 * M ≤ Kp * L := by linarith
  have hML : M ≤ Kp * L := by linarith
  have hc0 : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 12 := by norm_num
  have hc0nn : (0 : ℝ) ≤ 1 / 150 + 1 / 31 := by norm_num
  have hstep : (1 / 150 + 1 / 31) * ℓ ≤ (1 / 150 + 1 / 31) * (Kp * L + M) := by
    have := mul_le_mul_of_nonneg_left hlen hc0nn
    rwa [hL] at this
  have hfin : (1 / 150 + 1 / 31) * (Kp * L + M)
      ≤ Kp * L * (2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr)) := by
    have h2 : (1 / 150 + 1 / 31 : ℝ) * (Kp * L + M) ≤ (1 / 150 + 1 / 31) * (2 * (Kp * L)) := by
      nlinarith [hML]
    have h3 : (1 / 150 + 1 / 31 : ℝ) * 2 ≤ (2 : ℝ) * (1 / 12) := by linarith
    have h4 : (2 : ℝ) * (1 / 12) ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
      have h5 : (2 ^ 36 : ℝ) * 1 ≥ 1 := by norm_num
      nlinarith [hK1, h5, show ((2:ℝ) * (1/12)) ≤ 1 by norm_num]
    have hKL : (0 : ℝ) ≤ Kp * L := mul_nonneg hKp hLnn
    calc (1 / 150 + 1 / 31) * (Kp * L + M)
        ≤ (1 / 150 + 1 / 31) * (2 * (Kp * L)) := h2
      _ = (Kp * L) * ((1 / 150 + 1 / 31) * 2) := by ring
      _ ≤ (Kp * L) * (2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr)) :=
          mul_le_mul_of_nonneg_left (le_trans h3 h4) hKL
  calc (1 / 150 + 1 / 31) * ℓ
      ≤ (1 / 150 + 1 / 31) * (Kp * L + M) := hstep
    _ ≤ Kp * L * (2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr)) := hfin
    _ = Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
        rw [hL]; ring

end

end Work.Pert.V5
