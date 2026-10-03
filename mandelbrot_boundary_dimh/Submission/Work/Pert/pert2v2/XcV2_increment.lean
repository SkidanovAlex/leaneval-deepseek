import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Parab.Setup
import Submission.Work.PertCrux.QLeft_sub_real

/-!
# `Work.Pert.pert2v2.XcV2_increment`

For a §4.1 parabolic datum `d` (`MandelDim.ParabData f₀ D₀`) the curve
`Xc d u = τ₀ (φ u)` is asymptotically the identity on the repelling sector `QLeft ξ₀`
(`d.φ_asymp`: `Xc d u = u + a log(-u) + b + o(1)`).

Write `g u = |(Xc d u).im| - (Xc d u).re` (the "height" functional).  For the model
`P u = u + a log(-u) + b` the shift `u ↦ u - 1` changes the real part by exactly `+1` and
leaves the imaginary part unchanged, while the logarithmic terms contribute only
`‖a‖ · ‖log(-(u-1)) - log(-u)‖ = O(1/‖u‖)`.  Hence, for `u` deep in the sector,

`g (v - 1) ≥ g v + 1/2`,

which is the statement below: the "height" `|Im| - Re` of the curve's walk grows by at least
`1/2` per step.

The two ingredients are
* `Work.PertCrux.QLeft_sub_real`: the sector is closed under subtracting nonnegative reals, so
  `v - 1 ∈ QLeft ξ₀` whenever `v ∈ QLeft ξ₀`;
* the elementary logarithmic difference bound `norm_log_sub_log_le` below, proved by the mean
  value theorem along the segment `[v - 1, v]` (which stays away from the branch cut since the
  sector contains no nonnegative real).
-/

namespace Work.Pert.pert2v2

open Complex Metric

noncomputable section

/-! ## Elementary facts about the sector `QLeft` -/

/-- A nonnegative real is never in the left sector `QLeft ξ` for `ξ > 0`: its translate `s + ξ`
is a positive real and has argument `0`. -/
theorem not_mem_QLeft_ofReal_nonneg {ξ : ℝ} (hξ : 0 < ξ) {s : ℝ} (hs : 0 ≤ s) :
    (s : ℂ) ∉ MandelDim.QLeft ξ := by
  intro hmem
  rw [Work.Parab.QLeft_iff] at hmem
  have hcast : (s : ℂ) + (ξ : ℂ) = ((s + ξ : ℝ) : ℂ) := by rw [← Complex.ofReal_add]
  have hnorm : ‖((s + ξ : ℝ) : ℂ)‖ = s + ξ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hcast, Complex.ofReal_re, hnorm] at hmem
  linarith

/-- For `v` in the sector `QLeft ξ` (`ξ > 0`) and `0 ≤ x`, the point `-(v - x)` lies in the
slit plane `{z | 0 < z.re ∨ z.im ≠ 0}`: otherwise `v` would be a nonnegative real.  This is
exactly the condition under which `Complex.log` is differentiable at `-(v - x)`. -/
theorem neg_sub_mem_slitPlane {ξ : ℝ} (hξ : 0 < ξ) {v : ℂ} (hv : v ∈ MandelDim.QLeft ξ)
    {x : ℝ} (hx : 0 ≤ x) : -(v - (x : ℂ)) ∈ Complex.slitPlane := by
  rw [Complex.slitPlane, Set.mem_ofPred_eq]
  by_contra h
  simp only [not_or, not_lt, not_ne_iff] at h
  obtain ⟨hre, him⟩ := h
  have him' : (v - (x : ℂ)).im = 0 := by
    have h := Complex.neg_im (v - (x : ℂ))
    rw [h] at him
    exact neg_eq_zero.mp him
  have hre' : 0 ≤ (v - (x : ℂ)).re := by
    have h := Complex.neg_re (v - (x : ℂ))
    rw [h] at hre
    linarith
  have hvim : v.im = 0 := by
    have h := Complex.sub_im v (x : ℂ)
    rw [h] at him'
    simpa using him'
  have hvre : 0 ≤ v.re := by
    have h := Complex.sub_re v (x : ℂ)
    rw [h] at hre'
    simp only [Complex.ofReal_re] at hre'
    linarith
  have hv_eq : v = (v.re : ℂ) := by
    apply Complex.ext <;> simp [hvim]
  exact not_mem_QLeft_ofReal_nonneg hξ hvre (hv_eq ▸ hv)

/-- `Complex.log ∘ (fun t : ℝ => -(v - t))` is differentiable at `x` with derivative
`(-(v - x))⁻¹`. -/
theorem hasDerivAt_log_neg_sub (v : ℂ) {x : ℝ}
    (hz : -(v - (x : ℂ)) ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log (-(v - (t : ℂ)))) (-(v - (x : ℂ)))⁻¹ x := by
  have h1 : HasDerivAt (fun t : ℝ => -(v - (t : ℂ))) (1 : ℂ) x := by
    have h : (fun t : ℝ => -(v - (t : ℂ))) = fun t : ℝ => (-v) + (t : ℂ) := by ext t; ring
    rw [h]
    exact (Complex.ofRealCLM.hasDerivAt (x := x)).const_add (-v)
  have h2 : HasDerivAt Complex.log (-(v - (x : ℂ)))⁻¹ (-(v - (x : ℂ))) :=
    Complex.hasDerivAt_log hz
  have h3 : HasDerivAt (Complex.log ∘ fun t : ℝ => -(v - (t : ℂ)))
      ((-(v - (x : ℂ)))⁻¹ * 1) x := h2.comp x h1
  have h4 : HasDerivAt (fun t : ℝ => Complex.log (-(v - (t : ℂ))))
      ((-(v - (x : ℂ)))⁻¹ * 1) x := h3
  simpa only [mul_one] using h4

/-- **Logarithmic difference of two neighbouring sector points.**  For `v ∈ QLeft ξ` (`ξ > 0`)
with `‖v‖ ≥ 2`,

`‖log(-(v-1)) - log(-v)‖ ≤ 1/(‖v‖ - 1)`.

The segment joining `v - 1` to `v` stays in the sector's complement of the positive real axis, so
`t ↦ log(-(v - t))` is differentiable on it with derivative `-(v - t)⁻¹` of norm
`1/‖v - t‖ ≤ 1/(‖v‖ - 1)`; the mean value theorem gives the bound. -/
theorem norm_log_sub_log_le {ξ : ℝ} (hξ : 0 < ξ) {v : ℂ} (hv : v ∈ MandelDim.QLeft ξ)
    (h2 : 2 ≤ ‖v‖) :
    ‖Complex.log (-(v - 1)) - Complex.log (-v)‖ ≤ 1 / (‖v‖ - 1) := by
  set C : ℝ := 1 / (‖v‖ - 1) with hC
  have hvpos : 0 < ‖v‖ - 1 := by linarith
  have hder : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => Complex.log (-(v - (t : ℂ))))
        ((fun t : ℝ => (-(v - (t : ℂ)))⁻¹) x) (Set.Icc (0 : ℝ) 1) x := by
    intro x hx
    exact (hasDerivAt_log_neg_sub v (neg_sub_mem_slitPlane hξ hv hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖((fun t : ℝ => (-(v - (t : ℂ)))⁻¹) x)‖ ≤ C := by
    intro x hx
    have hxabs : |x| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hx.1], hx.2⟩
    have hle : ‖v‖ - 1 ≤ ‖v - (x : ℂ)‖ := by
      have h := norm_add_le (v - (x : ℂ)) ((x : ℝ) : ℂ)
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at h
      linarith
    have hpos : 0 < ‖v - (x : ℂ)‖ := by linarith
    rw [norm_inv, norm_neg, hC, one_div]
    exact (inv_le_inv₀ hpos hvpos).mpr hle
  have hMVT := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => Complex.log (-(v - (t : ℂ))))
    (f' := fun t : ℝ => (-(v - (t : ℂ)))⁻¹) (s := Set.Icc (0 : ℝ) 1)
    (x := 0) (y := 1) (C := C) hder hbound (convex_Icc 0 1) (by norm_num) (by norm_num)
  have hgoal : ‖Complex.log (-(v - 1)) - Complex.log (-v)‖ ≤ C := by
    simpa using hMVT
  rwa [hC] at hgoal

/-! ## The height functional `|Im ·| - Re ·` -/

/-- Moving from `w` to the nearby point `z` costs at most `2‖z - w‖` in the functional
`z ↦ |z.im| - z.re`. -/
theorem abs_im_sub_re_le (z w : ℂ) :
    |z.im| - z.re ≤ |w.im| - w.re + 2 * ‖z - w‖ := by
  have h1 : |z.im| ≤ |w.im| + ‖z - w‖ := by
    have heq : w.im + (z - w).im = z.im := by rw [Complex.sub_im]; ring
    calc |z.im| = |w.im + (z - w).im| := by rw [heq]
      _ ≤ |w.im| + |(z - w).im| := abs_add_le _ _
      _ ≤ |w.im| + ‖z - w‖ := by linarith [Complex.abs_im_le_norm (z - w)]
  have h2 : -z.re ≤ -w.re + ‖z - w‖ := by
    have h := Complex.abs_re_le_norm (z - w)
    have heq : z.re = w.re + (z - w).re := by rw [Complex.sub_re]; ring
    rw [heq]
    linarith [neg_le_abs (z - w).re]
  linarith

/-- Shifting by `-1 + e` increases the functional `|·.im| - ·.re` by at least
`1 - 2‖e‖`. -/
theorem abs_im_sub_re_shift_add (y e : ℂ) :
    |(y + (-1 + e)).im| - (y + (-1 + e)).re ≥ |y.im| - y.re + 1 - 2 * ‖e‖ := by
  have him : (y + (-1 + e)).im = y.im + e.im := by
    simp only [Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero, zero_add]
  have hre : (y + (-1 + e)).re = y.re - 1 + e.re := by
    rw [Complex.add_re, Complex.add_re, Complex.neg_re, Complex.one_re]; ring
  have h1 : |y.im| - ‖e‖ ≤ |(y + (-1 + e)).im| := by
    rw [him]
    have hle : |e.im| ≤ ‖e‖ := Complex.abs_im_le_norm e
    have hkey : |y.im| ≤ |y.im + e.im| + |e.im| := by
      have h := abs_add_le (y.im + e.im) (-e.im)
      simp only [add_neg_cancel_right, abs_neg] at h
      exact h
    linarith
  have h2 : e.re ≤ ‖e‖ := Complex.re_le_norm e
  rw [hre]
  linarith

/-! ## The increment -/

theorem XcV2_increment {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : ℂ, v ∈ MandelDim.QLeft d.ξ₀ → R ≤ ‖v‖ →
      |(Work.Pert.Xc d v).im| - (Work.Pert.Xc d v).re + 1 / 2 ≤
        |(Work.Pert.Xc d (v - 1)).im| - (Work.Pert.Xc d (v - 1)).re := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨Ra, hRa⟩ := hasym (1 / 32) (by norm_num)
  refine ⟨max 2 (max (Ra + 2) (1 + 8 * ‖a‖)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  · intro v hvQ hRv
    have hξ : 0 < d.ξ₀ := d.ξ₀_pos
    have hv2 : 2 ≤ ‖v‖ := le_trans (le_max_left _ _) hRv
    have hvRa : Ra + 2 ≤ ‖v‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRv
    have hva : 1 + 8 * ‖a‖ ≤ ‖v‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRv
    -- the shifted point is still in the sector
    have hv1Q : v - 1 ∈ MandelDim.QLeft d.ξ₀ := by
      have h := Work.PertCrux.QLeft_sub_real (ξ := d.ξ₀) hvQ (t := 1) (by norm_num)
      simpa using h
    have hnorm_v1 : Ra < ‖v - 1‖ := by
      have hle : ‖v‖ - 1 ≤ ‖v - 1‖ := by
        have h := norm_add_le (v - 1) (1 : ℂ)
        rw [sub_add_cancel, norm_one] at h
        linarith
      linarith
    have hnorm_v : Ra < ‖v‖ := by linarith
    -- the model `P u = u + a log(-u) + b`
    set P : ℂ → ℂ := fun u => u + a * Complex.log (-u) + b with hP
    have hPv : ‖Work.Pert.Xc d v - P v‖ < 1 / 32 := by
      simpa [Work.Pert.Xc, hP] using hRa v hvQ hnorm_v
    have hPv1 : ‖Work.Pert.Xc d (v - 1) - P (v - 1)‖ < 1 / 32 := by
      simpa [Work.Pert.Xc, hP] using hRa (v - 1) hv1Q hnorm_v1
    -- the logarithmic defect
    set e : ℂ := a * (Complex.log (-(v - 1)) - Complex.log (-v)) with he
    have he_bound : ‖e‖ ≤ 1 / 8 := by
      have hlog : ‖Complex.log (-(v - 1)) - Complex.log (-v)‖ ≤ 1 / (‖v‖ - 1) :=
        norm_log_sub_log_le hξ hvQ hv2
      have hpos : 0 < ‖v‖ - 1 := by linarith
      rw [he, norm_mul]
      have h2 : ‖a‖ / (‖v‖ - 1) ≤ 1 / 8 := by
        rw [div_le_iff₀ hpos]
        linarith
      calc ‖a‖ * ‖Complex.log (-(v - 1)) - Complex.log (-v)‖
          ≤ ‖a‖ * (1 / (‖v‖ - 1)) := mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
        _ = ‖a‖ / (‖v‖ - 1) := by rw [mul_one_div]
        _ ≤ 1 / 8 := h2
    -- the model shift `P (v-1) = P v + (-1 + e)`
    have heq : P (v - 1) = P v + (-1 + e) := by
      rw [he, hP]
      simp only
      ring
    have hinc : |(P v).im| - (P v).re + 1 - 2 * ‖e‖ ≤
        |(P (v - 1)).im| - (P (v - 1)).re := by
      rw [heq]
      exact abs_im_sub_re_shift_add (P v) e
    -- the two approximation steps and the conclusion
    have hA : |(Work.Pert.Xc d v).im| - (Work.Pert.Xc d v).re ≤
        |(P v).im| - (P v).re + 2 * (1 / 32) := by
      have := abs_im_sub_re_le (Work.Pert.Xc d v) (P v)
      linarith [hPv]
    have hB : |(P (v - 1)).im| - (P (v - 1)).re ≤
        |(Work.Pert.Xc d (v - 1)).im| - (Work.Pert.Xc d (v - 1)).re + 2 * (1 / 32) := by
      have := abs_im_sub_re_le (P (v - 1)) (Work.Pert.Xc d (v - 1))
      have hrev : ‖P (v - 1) - Work.Pert.Xc d (v - 1)‖ < 1 / 32 := by
        rw [norm_sub_rev]; exact hPv1
      linarith [this, hrev]
    linarith [hA, hB, hinc, he_bound]

end

end Work.Pert.pert2v2
