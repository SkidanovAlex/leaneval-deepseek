import Mathlib
import Submission.Work.Repel.V10.chain_v9_isl
import Submission.Work.Repel.V10.SrcC_sub_Dflat

/-!
# `Work.Repel.Isl_sub_halfball` : the island of a §6 cell lies in the half-ball `ball p (r/2)`

The island `V.Isl j k n = φ₀ '' Giw j k n` is the image under the level-0 Fatou coordinate of the
source region of the cell.  Since `Giw j k n ⊆ SrcC j k n`, it suffices to bound `φ₀` on the whole
source region: for every `w ∈ SrcC j k n`,

  `‖φ₀ w - 1.05 i / η‖ < (9/40)/η = r/2`.

This is the same computation as `Work.Repel.phi_close_to_p` (write `u = τ₀ (φ₀ w) = -1/(φ₀ w)`, then
split `φ₀ w - p = (-1/u + 1/w) + (-1/w - p)`), but with the *weak* source-region bounds

  `|Re w| ≤ η/8`,   `|Im w - η| ≤ 3/2`

in place of the slab bounds `|Re w| ≤ η/8`, `|Im w - η| ≤ 1/8` used there.  The first comes from
`SrcC ⊆ Dflat η`, the second from the round box `ball (w_c + n) (1/2)` together with
`|Im w_c - η| ≤ 1` (the level-1 `φ₁`-bounds).  Both halves of the split are weakened accordingly:

* `‖-1/w - 1.05 i/η‖ ≤ (3/20)/η` (in place of `1412/10000`): the corner `(η/8, η+3/2)` of the
  rectangle is still comfortably inside the ball of radius `3/20`;
* `‖-1/u + 1/w‖ ≤ 1/(37 η)` (in place of `1/(38 η)`), because `‖w‖ ≥ η - 3/2` rather than `η - 1/8`.

Finally `1/37 + 3/20 = 131/740 < 9/40`.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- Real part of `-1/w - s·i/η`: it equals `-(w.re / normSq w)`, independent of `s`. -/
private lemma re_helper_w (η s : ℝ) (w : ℂ) :
    (-1 / w - (s:ℂ) * Complex.I / η).re = -(w.re / Complex.normSq w) := by
  simp only [Complex.sub_re, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Imaginary part of `-1/w - s·i/η`: it equals `w.im / normSq w - s/η`. -/
private lemma im_helper_w (η s : ℝ) (hη : η ≠ 0) (w : ℂ) :
    (-1 / w - (s:ℂ) * Complex.I / η).im = w.im / Complex.normSq w - s / η := by
  simp only [Complex.sub_im, Complex.neg_im, Complex.neg_re, Complex.div_im, Complex.one_im,
    Complex.one_re, Complex.mul_im, Complex.I_im, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

/-- For `w` with `|Re w| ≤ η/8` and `|Im w - η| ≤ 3/2` (and `η ≥ 100`), the quantity `-1/w` is
within `(3/20)/η` of `1.05 i/η`.  This is `Work.Repel.norm_neg_inv_sub_const_le` with the weak
height bound `3/2` in place of `1/8`; the extremal corner `(η/8, η + 3/2)` gives `0.1436 < 0.15`. -/
private lemma neg_inv_sub_const_le_wide {η : ℝ} (hη : 100 ≤ η) {w : ℂ}
    (hre : |w.re| ≤ η / 8) (him : |w.im - η| ≤ 3 / 2) :
    ‖-1 / w - 1.05 * Complex.I / η‖ ≤ (3 / 20) / η := by
  have hηpos : 0 < η := by linarith
  have hηne : η ≠ 0 := ne_of_gt hηpos
  rcases abs_le.mp him with ⟨him1, him2⟩
  have hy_pos : 0 < w.im := by linarith
  have hw : w ≠ 0 := by intro h; rw [h] at hy_pos; simp at hy_pos
  -- the polynomial core: `η² - 2.1 η y + (27/25)(x² + y²) ≤ 0`, i.e. `η²‖·‖² ≤ (3/20)²`
  have hkey : η^2 - 2.1*η*w.im + (27/25)*(w.re^2 + w.im^2) ≤ 0 := by
    have hE : η^2 - 2.1*η*w.im + (27/25)*(w.re^2 + w.im^2)
        = -(1/50)*η^2 + (3/50)*η*(w.im - η) + (27/25)*(w.re^2 + (w.im - η)^2) := by ring
    rw [hE]
    have hx : w.re^2 ≤ η^2/64 := by
      have h := abs_le.mp hre
      nlinarith [h.1, h.2, sq_nonneg (η/8 + w.re), sq_nonneg (η/8 - w.re)]
    have hv : (w.im - η)^2 ≤ 9/4 := by
      nlinarith [him1, him2, sq_nonneg ((3:ℝ)/2 + (w.im - η)), sq_nonneg ((3:ℝ)/2 - (w.im-η))]
    nlinarith [hx, hv, him2, hη, sq_nonneg η]
  have hzre : (-1 / w - 1.05 * Complex.I / η).re = -(w.re / Complex.normSq w) :=
    re_helper_w η (1.05) w
  have hzim : (-1 / w - 1.05 * Complex.I / η).im = w.im / Complex.normSq w - 1.05 / η :=
    im_helper_w η (1.05) hηne w
  have hsq : ‖-1 / w - 1.05 * Complex.I / η‖^2 ≤ ((3 / 20) / η)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    simp only [Complex.normSq_apply]
    have hc : (1.05:ℝ)^2 - (3/20:ℝ)^2 = 27/25 := by norm_num
    field_simp
    nlinarith [hkey, hc]
  have htg : 0 ≤ (3 / 20) / η := by positivity
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg htg] at h

/-- If `u` is within `η/40` of `w`, and `‖w‖ ≥ η - 3/2` with `η ≥ 100`, then the reciprocal shift
`-1/u + 1/w` is bounded by `1/(37η)`.  This is `Work.Repel.inv_shift_close` with the weak lower
bound `η - 3/2` on `‖w‖` in place of `η - 1/8`. -/
private lemma inv_shift_close_wide {η : ℝ} (hη : 100 ≤ η) {u w : ℂ}
    (huw : ‖u - w‖ ≤ η / 40) (hw : η - 3 / 2 ≤ ‖w‖) :
    ‖-1 / u + 1 / w‖ ≤ 1 / (37 * η) := by
  have h37pos : (0 : ℝ) < 37 * η := by linarith
  have hC : (0 : ℝ) < η - 3 / 2 := by linarith
  have hB : (0 : ℝ) < 39 * η / 40 - 3 / 2 := by linarith
  have hu_low : 39 * η / 40 - 3 / 2 ≤ ‖u‖ := by
    have h2 := norm_sub_norm_le w u
    rw [norm_sub_rev w u] at h2
    linarith
  have hu_pos : (0 : ℝ) < ‖u‖ := lt_of_lt_of_le hB hu_low
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hunz : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hwnz : w ≠ 0 := norm_pos_iff.mp hw_pos
  have hkey : -1 / u + 1 / w = (u - w) / (u * w) := by
    rw [div_add_div _ _ hunz hwnz]
    congr 1
    ring
  rw [hkey, norm_div, norm_mul, div_le_div_iff₀ (mul_pos hu_pos hw_pos) h37pos]
  have h1 : ‖u - w‖ * (37 * η) ≤ (η / 40) * (37 * η) :=
    mul_le_mul_of_nonneg_right huw (by linarith)
  have h2 : (η / 40) * (37 * η) ≤ (39 * η / 40 - 3 / 2) * (η - 3 / 2) := by
    nlinarith [hη]
  have h3 : (39 * η / 40 - 3 / 2) * (η - 3 / 2) ≤ ‖u‖ * ‖w‖ :=
    mul_le_mul hu_low hw (le_of_lt hC) (norm_nonneg u)
  linarith

/-- **The level-0 Fatou coordinate on a weak source box.**  If `u` is the `τ₀`-image of `φ w` (i.e.
`‖u - w‖ ≤ η/40`) and `w` lies in the weak box `|Re w| ≤ η/8`, `|Im w - η| ≤ 3/2`, then
`φ w = -1/u` lies within `(9/40)/η` of `1.05 i/η`. -/
private lemma neg_inv_close_wide {η : ℝ} (hη : 100 ≤ η) {u w : ℂ}
    (huw : ‖u - w‖ ≤ η / 40) (hre : |w.re| ≤ η / 8) (him : |w.im - η| ≤ 3 / 2) :
    ‖-1 / u - 1.05 * Complex.I / η‖ < (9 / 40) / η := by
  have hηpos : 0 < η := by linarith
  have hwn : η - 3 / 2 ≤ ‖w‖ := by
    have h1 : η - 3 / 2 ≤ w.im := by have := (abs_le.mp him).1; linarith
    have h2 : w.im ≤ ‖w‖ := by
      have := Complex.abs_im_le_norm w
      rwa [abs_of_pos (by linarith : (0:ℝ) < w.im)] at this
    linarith
  have hsplit : -1 / u - 1.05 * Complex.I / η
      = (-1 / u + 1 / w) + (-1 / w - 1.05 * Complex.I / η) := by ring
  calc ‖-1 / u - 1.05 * Complex.I / η‖
      = ‖(-1 / u + 1 / w) + (-1 / w - 1.05 * Complex.I / η)‖ := by rw [hsplit]
    _ ≤ ‖-1 / u + 1 / w‖ + ‖-1 / w - 1.05 * Complex.I / η‖ := norm_add_le _ _
    _ ≤ 1 / (37 * η) + (3 / 20) / η :=
        add_le_add (inv_shift_close_wide hη huw hwn) (neg_inv_sub_const_le_wide hη hre him)
    _ < (9 / 40) / η := by
        rw [show (1:ℝ) / (37 * η) = (1/37) / η by ring, ← add_div]
        rw [div_lt_div_iff_of_pos_right hηpos]
        norm_num

namespace V10

variable (V : V10)

/-- The imaginary part of a source point of a cell is within `3/2` of `η`: the round box
`ball (w_c + n) (1/2)` gives `|Im w - Im w_c| < 1/2`, and `|Im w_c - η| ≤ 1`. -/
theorem SrcC_im_close {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {w : ℂ}
    (hw : w ∈ V.SrcC j k n) : |w.im - V.η| ≤ 3 / 2 := by
  obtain ⟨hwRaw, hwball⟩ := hw
  rw [Metric.mem_ball, dist_eq_norm] at hwball
  have him1 : |w.im - (V.wc j k).im| < 1 / 2 := by
    have h := Complex.abs_im_le_norm (w - (V.wc j k + ((n : ℤ) : ℂ)))
    have him_eq : (w - (V.wc j k + ((n : ℤ) : ℂ))).im = w.im - (V.wc j k).im := by
      simp [Complex.sub_im, Complex.add_im]
    rw [him_eq] at h
    linarith
  have him2 : |(V.wc j k).im - V.η| ≤ 1 := V.abs_im_wc_sub_eta_le hSm
  have hsplit : w.im - V.η = (w.im - (V.wc j k).im) + ((V.wc j k).im - V.η) := by ring
  rw [hsplit]
  calc |(w.im - (V.wc j k).im) + ((V.wc j k).im - V.η)|
      ≤ |w.im - (V.wc j k).im| + |(V.wc j k).im - V.η| := abs_add_le _ _
    _ ≤ 3 / 2 := by linarith

end V10

/-- **The island of a §6 cell lies in the half-ball.**  `Isl j k n = φ₀ '' Giw j k n` and
`Giw j k n ⊆ SrcC j k n`; on `SrcC j k n` the weak source bounds hold, so the `φ₀`-image of the
whole source region (hence the island) is contained in `ball p (r/2)`. -/
theorem Isl_sub_halfball (V : Work.Repel.V10) {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) :
    V.Isl j k n ⊆ Metric.ball V.p (V.r / 2) := by
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨hwSrc, hwtgt⟩ := hw
  have hη : 100 ≤ V.η := V.hη
  have hηpos : 0 < V.η := V.hηpos
  have hflat : w ∈ Work.Repel.Dflat V.η := SrcC_sub_Dflat V hSm hn hwSrc
  have hnorm : ‖w - Complex.I * (V.η : ℂ)‖ ≤ V.η / 8 := by
    have h := hflat
    rw [Work.Repel.Dflat, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hηpos] at h
    exact h
  have hre : |w.re| ≤ V.η / 8 := by
    have h := Complex.abs_re_le_norm (w - Complex.I * (V.η : ℂ))
    have he : (w - Complex.I * (V.η : ℂ)).re = w.re := by simp
    rw [he] at h
    exact le_trans h hnorm
  have him : |w.im - V.η| ≤ 3 / 2 := V.SrcC_im_close hSm hwSrc
  have hdsm : w ∈ MandelDim.Dsm V.η := Work.Repel.Dflat_subset_Dsm V.η hflat
  have hcl : ‖MandelDim.tau0 (V.P₀.φ w) - w‖ ≤ V.η / 40 := by
    have h := V.P₀.φ_star_close w (Or.inl hdsm)
    rwa [abs_of_pos hηpos] at h
  -- `φ w = -1/τ₀(φ w)` (also when `φ w = 0`, both sides being `0`)
  have hphi : V.P₀.φ w = -1 / MandelDim.tau0 (V.P₀.φ w) := by
    rw [MandelDim.tau0]
    by_cases h0 : V.P₀.φ w = 0
    · rw [h0]; simp
    · field_simp
  rw [Metric.mem_ball, dist_eq_norm, V10.p, V10.r, hphi]
  rw [show (9 / (20 * V.η)) / 2 = (9 / 40) / V.η by ring]
  exact neg_inv_close_wide hη hcl hre him

end

end Work.Repel
