import Mathlib
import Submission.Work.Pert.Qm_slice

/-!
# PERT · `Work.Pert.GateDriftRate.waist_geo_re`

**Waist geometry of the lower gate.**  If `w` lies in the lower gate `Qm Ξ α` of §4.2 and the
rotated point `α w` lies in the horizontal strip `|Im (α w)| < 1` ("the waist"), then its real
part is bounded by `3`.

## Math

Write `p = Re α > 0`, `q = Im α`, `m = p² + q² = ‖α‖²`, `X = Re w`, `T = Im w`,
`B = Im (α w) = q X + p T`, so that `T = (B - q X)/p` and

  `Re (α w) = p X - q T = (m X - q B)/p`.

The gate is `Qreg (Ξ - 1/α) (-Ξ)`, i.e. the pair of cone conditions (`Work.Pert.Qm_mem_iff`)
* `(A)  X - Ξ + p/m > -|T - q/m|`   (`= -|(B - qX)/p - q/m|`),  and
* `(B)  X + Ξ < |T|`.

Since `α ∈ 𝓕₁` (`|q| < p`) and `|q| ≤ ‖α‖/16` (so `|q| ≤ p/15`), the strip hypothesis `|B| < 1`
converts (B) into an upper bound for `X` when `X ≥ 0` and (A) into a lower bound when `X < 0`:

* `X ≥ 0`: `p X - |q| X < 1`, so `X m < 113/105 · p`, and then
  `Re (α w) ≤ 113/105 p + |q| ≤ 8/7 p < 3 p`;
* `X < 0`: `|X| m (p - |q|) < p² + m + p|q|`, hence `|X| m < 233/105 p` and then
  `Re (α w) ≥ -(233/105 p + |q|) > -16/7 p > -3 p`.

The real-arithmetic core of this is isolated in `waist_core_aux` (a `private` copy of the
independently developed `Work.Pert.GateDriftRate.waist_real_core`).
-/

namespace Work.Pert.GateDriftRate

open Complex

set_option maxHeartbeats 1000000 in
/-- Real-arithmetic core of `waist_geo_re`: if `X` is bounded above by the gate condition (B)
when it is non-negative (`h2`) and below by (A) when it is negative (`h1`), and `|B| < 1`,
`15|q| ≤ p`, then `|(p²+q²)X - qB| ≤ 3p`. -/
private theorem waist_core_aux {p q X B : ℝ} (hp : 0 < p) (hq : 15 * |q| ≤ p) (hB : |B| < 1)
    (h1 : 0 < X + p / (p ^ 2 + q ^ 2) + |(B - q * X) / p - q / (p ^ 2 + q ^ 2)|)
    (h2 : p * X - |q| * |X| < 1) :
    |(p ^ 2 + q ^ 2) * X / p - q * B / p| ≤ 3 := by
  set m : ℝ := p ^ 2 + q ^ 2 with hmdef
  have hmpos : 0 < m := by rw [hmdef]; positivity
  have hpne : p ≠ 0 := ne_of_gt hp
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hs : |q| ≤ p / 15 := by linarith
  have hs0 : 0 ≤ |q| := abs_nonneg q
  have hq2 : q ^ 2 ≤ p ^ 2 / 225 := by
    have h : q ^ 2 ≤ (p / 15) ^ 2 := by
      calc q ^ 2 = |q| ^ 2 := by rw [sq_abs]
        _ ≤ (p / 15) ^ 2 := pow_le_pow_left₀ hs0 hs 2
    nlinarith [h]
  have hm226 : 225 * m ≤ 226 * p ^ 2 := by rw [hmdef]; linarith
  have habs : |m * X - q * B| ≤ m * |X| + |q| * |B| := by
    calc |m * X - q * B| = |m * X + -(q * B)| := by rw [sub_eq_add_neg]
      _ ≤ |m * X| + |-(q * B)| := abs_add_le _ _
      _ = m * |X| + |q| * |B| := by rw [abs_neg, abs_mul, abs_mul, abs_of_pos hmpos]
  have hgoal : |(p ^ 2 + q ^ 2) * X / p - q * B / p| = |m * X - q * B| / p := by
    rw [← hmdef, ← sub_div, abs_div, abs_of_pos hp]
  have h13 : |q| * |B| < p / 15 := by
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · rw [← h0, zero_mul]; positivity
    · calc |q| * |B| < |q| * 1 := mul_lt_mul_of_pos_left hB hpos
        _ = |q| := mul_one _
        _ ≤ p / 15 := hs
  suffices hfin : |m * X - q * B| < 3 * p by
    rw [hgoal, div_le_iff₀ hp]
    linarith
  rcases lt_or_ge X 0 with hX | hX
  · -- ## case `X < 0`: the gate condition (A) bounds `|X|`
    have hXa : |X| = -X := abs_of_nonpos (le_of_lt hX)
    have hbn : |(B - q * X) / p - q / m| ≤ (|B| + |q| * |X|) / p + |q| / m := by
      have e1 : |(B - q * X) / p - q / m| ≤ |(B - q * X) / p| + |q / m| := by
        have h := abs_add_le ((B - q * X) / p) (-(q / m))
        simpa [sub_eq_add_neg] using h
      have e2 : |(B - q * X) / p| = |B - q * X| / p := by rw [abs_div, abs_of_pos hp]
      have e3 : |q / m| = |q| / m := by rw [abs_div, abs_of_pos hmpos]
      have e4 : |B - q * X| ≤ |B| + |q| * |X| := by
        have h := abs_add_le B (-(q * X))
        rw [abs_neg, abs_mul] at h
        simpa [sub_eq_add_neg] using h
      have e5 : |B - q * X| / p ≤ (|B| + |q| * |X|) / p :=
        div_le_div_of_nonneg_right e4 (le_of_lt hp)
      linarith [e1, e2, e3, e5]
    have h1' : 0 < X + p / m + (|B| + |q| * |X|) / p + |q| / m := by linarith [h1, hbn]
    have h4 : |X| * (p * m) < p ^ 2 + m * |B| + m * (|q| * |X|) + |q| * p := by
      have hpos : 0 < p * m := by positivity
      have h5 := mul_pos h1' hpos
      have he : (X + p / m + (|B| + |q| * |X|) / p + |q| / m) * (p * m)
          = X * (p * m) + p ^ 2 + (|B| + |q| * |X|) * m + |q| * p := by
        field_simp
      rw [he] at h5
      nlinarith [h5, hXa]
    have h6 : |X| * (p * m) < p ^ 2 + m + m * (|q| * |X|) + |q| * p := by
      nlinarith [h4, hB, hmpos]
    have h7 : |X| * m * (p - |q|) < p ^ 2 + m + |q| * p := by nlinarith [h6]
    have h7' : |X| * m * (14 * p / 15) < p ^ 2 + m + |q| * p := by
      have h14 : 14 * p / 15 ≤ p - |q| := by linarith [hs]
      have hXm : 0 ≤ |X| * m := by positivity
      nlinarith [h7, h14, hXm]
    have hpqq : p * |q| ≤ p ^ 2 / 15 := by nlinarith [hs, hp]
    have h8 : |X| * m * (14 * p / 15) < 466/225 * p ^ 2 := by linarith [h7', hm226, hpqq]
    have h9 : |X| * m * (14 * p) < 466/15 * p ^ 2 := by linarith [h8]
    have h10 : |X| * m < 233/105 * p := by
      have h11 : |X| * m < (466/15 * p ^ 2) / (14 * p) :=
        (lt_div_iff₀ (by positivity : (0:ℝ) < 14 * p)).mpr h9
      have h12 : (466/15 * p ^ 2) / (14 * p) = 233/105 * p := by
        rw [div_eq_iff (by positivity : (14:ℝ) * p ≠ 0)]
        ring
      linarith
    have hA : |X| * m + |q| * |B| < 233/105 * p + p / 15 := by linarith [h10, h13]
    have hB' : (233:ℝ)/105 * p + p / 15 = 16/7 * p := by ring
    have hC : (16:ℝ)/7 * p < 3 * p := by linarith [hp]
    have hsum : m * |X| + |q| * |B| < 3 * p := by linarith [hA, hB', hC]
    linarith [habs, hsum]
  · -- ## case `0 ≤ X`: the gate condition (B) bounds `X`
    have hXa : |X| = X := abs_of_nonneg hX
    rw [hXa] at h2
    have h2' : X * (p - |q|) < 1 := by nlinarith [h2]
    have h14 : 14 * p / 15 ≤ p - |q| := by linarith [hs]
    have hXm : 0 ≤ X * m := by positivity
    have h4 : X * m * (14 * p / 15) < m := by nlinarith [h2', h14, hXm, hmpos]
    have h5 : X * m * (14 * p / 15) < 226/225 * p ^ 2 := by linarith [h4, hm226]
    have h7 : X * m * (14 * p) < 226/15 * p ^ 2 := by linarith [h5]
    have h6 : X * m < 113/105 * p := by
      have h8 : X * m < (226/15 * p ^ 2) / (14 * p) :=
        (lt_div_iff₀ (by positivity : (0:ℝ) < 14 * p)).mpr h7
      have h9 : (226/15 * p ^ 2) / (14 * p) = 113/105 * p := by
        rw [div_eq_iff (by positivity : (14:ℝ) * p ≠ 0)]
        ring
      linarith
    have habs' : |m * X - q * B| ≤ m * X + |q| * |B| := by rw [hXa] at habs; exact habs
    have hA : X * m + |q| * |B| < 113/105 * p + p / 15 := by linarith [h6, h13]
    have hB' : (113:ℝ)/105 * p + p / 15 = 8/7 * p := by ring
    have hC : (8:ℝ)/7 * p < 3 * p := by linarith [hp]
    have hsum : m * X + |q| * |B| < 3 * p := by linarith [hA, hB', hC]
    linarith [habs', hsum]

theorem waist_geo_re {Ξ : ℝ} {α : ℂ} {w : ℂ}
    (hΞ : 0 ≤ Ξ) (hInF1 : MandelDim.InF1 α) (hw : w ∈ Work.Pert.Qm Ξ α)
    (hR : |α.im| ≤ ‖α‖ / 16) (hwaist : |(α * w).im| < 1) :
    |(α * w).re| ≤ 3 := by
  -- ## basic facts about `α`
  have hq_lt_p : |α.im| < α.re := hInF1
  have hp : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hq_lt_p
  have hpre : α.re ≠ 0 := ne_of_gt hp
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hp
    simp at hp
  have hnormsq : (0 : ℝ) < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have hq15 : 15 * |α.im| ≤ α.re := by
    have h1 : ‖α‖ ≤ |α.re| + |α.im| := Complex.norm_le_abs_re_add_abs_im α
    rw [abs_of_pos hp] at h1
    have h2 : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
    linarith
  -- ## the gate, in coordinates (`Qm_mem_iff`)
  obtain ⟨hg1, hg2⟩ := (Work.Pert.Qm_mem_iff (ξ := Ξ) (α := α) (z := w)).mp hw
  -- ## coordinates of `1/α` and the expression of `T = w.im` through `B = Im (α w)`
  have hQ : (1 / α).im = -(α.im / Complex.normSq α) := by
    rw [one_div, Complex.inv_im, neg_div]
  have hP : (1 / α).re = α.re / Complex.normSq α := by rw [one_div, Complex.inv_re]
  have hT : w.im = ((α * w).im - α.im * w.re) / α.re := by
    rw [eq_div_iff hpre, Complex.mul_im]
    ring
  -- ## hypothesis `h1` of the core
  have hcore1 : 0 < w.re + α.re / (α.re ^ 2 + α.im ^ 2) +
      |((α * w).im - α.im * w.re) / α.re - α.im / (α.re ^ 2 + α.im ^ 2)| := by
    have harg : w.im + (1 / α).im
        = ((α * w).im - α.im * w.re) / α.re - α.im / (α.re ^ 2 + α.im ^ 2) := by
      rw [hQ, hT]
      simp only [Complex.normSq_apply]
      ring
    have hpre' : (1 / α).re = α.re / (α.re ^ 2 + α.im ^ 2) := by
      rw [hP, Complex.normSq_apply]
      ring
    rw [hpre', harg] at hg1
    linarith
  -- ## hypothesis `h2` of the core
  have hcore2 : α.re * w.re - |α.im| * |w.re| < 1 := by
    have h1 : w.re + Ξ < |w.im| := by linarith
    have h2 : α.re * w.im = (α * w).im - α.im * w.re := by
      rw [hT, mul_div_cancel₀ _ hpre]
    have h3 : α.re * |w.im| = |α.re * w.im| := by
      rw [abs_mul, abs_of_pos hp]
    have h4 : α.re * (w.re + Ξ) < |(α * w).im - α.im * w.re| := by
      have h5 : α.re * (w.re + Ξ) < α.re * |w.im| := mul_lt_mul_of_pos_left h1 hp
      rw [h3, h2] at h5
      exact h5
    have h6 : α.re * (w.re + Ξ) < 1 + |α.im| * |w.re| := by
      refine lt_of_lt_of_le h4 ?_
      have h7 : |(α * w).im - α.im * w.re| ≤ |(α * w).im| + |α.im * w.re| := by
        have h := abs_add_le ((α * w).im) (-(α.im * w.re))
        simpa [sub_eq_add_neg] using h
      rw [abs_mul] at h7
      linarith
    have h8 : 0 ≤ α.re * Ξ := by positivity
    linarith
  -- ## the core and the identification of the conclusion
  have hcore : |(α.re ^ 2 + α.im ^ 2) * w.re / α.re - α.im * (α * w).im / α.re| ≤ 3 :=
    waist_core_aux hp hq15 hwaist hcore1 hcore2
  have hrel : (α * w).re = (Complex.normSq α * w.re - α.im * (α * w).im) / α.re := by
    rw [eq_div_iff hpre, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have habs : |(α * w).re|
      = |(α.re ^ 2 + α.im ^ 2) * w.re / α.re - α.im * (α * w).im / α.re| := by
    rw [hrel, sub_div]
    congr 1
    rw [Complex.normSq_apply]
    ring
  rw [habs]
  exact hcore

end Work.Pert.GateDriftRate
