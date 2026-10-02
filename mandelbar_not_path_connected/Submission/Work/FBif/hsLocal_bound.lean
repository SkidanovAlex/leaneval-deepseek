import Mathlib
import Submission.Work.FBif.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- Real part of `A * (star u)^2`, expanded in coordinates. -/
private lemma re_mul_conj_sq (A u : ℂ) :
    (A * (star u)^2).re = A.re * (u.re^2 - u.im^2) + 2 * A.im * u.re * u.im := by
  have h : (star u : ℂ)^2 = star (u^2) := (map_pow (starRingEnd ℂ) u 2).symm
  rw [h]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Imaginary part of `A * (star u)^2`, expanded in coordinates. -/
private lemma im_mul_conj_sq (A u : ℂ) :
    (A * (star u)^2).im = A.im * (u.re^2 - u.im^2) - 2 * A.re * u.re * u.im := by
  have h : (star u : ℂ)^2 = star (u^2) := (map_pow (starRingEnd ℂ) u 2).symm
  rw [h]
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

/-- `‖u‖^2 = u.re^2 + u.im^2`. -/
private lemma norm_sq_eq (u : ℂ) : ‖u‖^2 = u.re^2 + u.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- The purely real numerical content of the "near the real axis" case: if `u` is close
to the real axis (`|y| ≤ ε r`) then `Re(A ū²)` dominates `(Re A)/4 ‖u‖²`. -/
private lemma case1_arith {a b n eps x y r : ℝ} (hr0 : 0 ≤ r) (ha : 0 < a) (heps : 0 ≤ eps)
    (hb : |b| ≤ n) (hY : |y| ≤ eps * r) (hX : |x| ≤ r) (hr : r^2 = x^2 + y^2)
    (heps8 : eps ≤ 1/8) (hneeps : 2 * n * eps ≤ a / 4) :
    (a / 4) * r^2 ≤ a * (x^2 - y^2) + 2 * b * x * y := by
  have hn0 : 0 ≤ n := le_trans (abs_nonneg b) hb
  have heps2 : eps^2 ≤ 1/64 := by nlinarith [heps, heps8]
  have hy2 : y^2 ≤ eps^2 * r^2 := by
    have h1 : |y| ≤ |eps * r| := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ eps * r)]; exact hY
    have h2 : y^2 ≤ (eps * r)^2 := (sq_le_sq).mpr h1
    nlinarith [h2]
  have hxy : |x * y| ≤ eps * r^2 := by
    rw [abs_mul]
    calc |x| * |y| ≤ r * (eps * r) := mul_le_mul hX hY (abs_nonneg y) hr0
      _ = eps * r^2 := by ring
  have hay2 : a * y^2 ≤ a * (eps^2 * r^2) := mul_le_mul_of_nonneg_left hy2 (le_of_lt ha)
  have hbx : b * x * y ≥ -n * (eps * r^2) := by
    have h1 : b * (x*y) ≥ -(|b| * |x*y|) := by
      have := neg_abs_le (b * (x*y)); rwa [abs_mul] at this
    have h2 : |b| * |x*y| ≤ n * (eps * r^2) := mul_le_mul hb hxy (abs_nonneg _) hn0
    nlinarith [h1, h2]
  have hfin : a * (1 - 2*eps^2) - 2 * n * eps ≥ a / 4 := by nlinarith [heps2, hneeps, ha]
  nlinarith [hay2, hbx, hneeps, ha, hr, hr0, hfin]

/-- The numerical content of the "off the real axis" case. -/
private lemma case2_arith {αre αim β eps M r δ : ℝ}
    (hβ0 : 0 ≤ β) (hδhalf : δ ≤ 1/2) (heps : 0 ≤ eps)
    (hM0 : 0 ≤ M) (hr0 : 0 ≤ r) (hrδ : r ≤ δ) (hMδ : M * δ ≤ eps / 4)
    (hα : αre ≤ M * r ^ 2 + β * r)
    (hgap : β * (1 - δ) + (7 * eps / 4) * r ≤ β + |αim|) :
    αre ≤ β + |αim| := by
  have hMr : M * r ≤ eps / 4 := le_trans (mul_le_mul_of_nonneg_left hrδ hM0) hMδ
  have h1 : M * r ^ 2 ≤ (eps / 4) * r := by nlinarith [hMr, hr0]
  have h2 : β * r ≤ β * (1 - δ) := by
    have hh : β * r ≤ β * (1 - δ) := mul_le_mul_of_nonneg_left (by linarith) hβ0
    exact hh
  have h3 : (eps / 4) * r ≤ (7 * eps / 4) * r := by nlinarith [heps, hr0]
  linarith [hα, h1, h2, h3, hgap]

/-- **The local estimate of Hubbard–Schleicher's Lemma 3.4** (arXiv:1209.1753).

Let `A : ℂ` have positive real part.  There are `δ, c₀ > 0` and `K > 0` such that for every
`e : ℂ → ℂ` and every `α : ℂ`, `β : ℝ`, `u : ℂ` with `0 ≤ β`, `β ≤ 1`, `‖u‖ ≤ δ`,
`‖e u‖ ≤ c₀‖u‖² + β‖u‖` and `ū + A ū² + α + e u = u`, we have `α.re ≤ K (β + |α.im|)`.

This is the case analysis of HS: writing `u = x + iy`, the equation splits into
`Re(A ū²) + Re α + Re(e u) = 0` and `2y = Im(A ū²) + Im α + Im(e u)`; near the real axis
(`|y| ≤ 8‖A‖x²`, where `Re(A ū²) ≥ (Re A)/3 ‖u‖²`) the first contradicts `Re α > 0`, and off
it the second forces `|y| = O(β + |Im α|)`, after which the first gives the stated bound. -/
theorem hsLocal_bound {A : ℂ} (hA : 0 < A.re) :
    ∃ δ > 0, ∃ c₀ > 0, ∃ K > 0, ∀ (e : ℂ → ℂ) (α : ℂ) (β : ℝ) (u : ℂ), 0 ≤ β → β ≤ 1 →
      ‖u‖ ≤ δ → ‖e u‖ ≤ c₀ * ‖u‖ ^ 2 + β * ‖u‖ →
      star u + A * (star u) ^ 2 + α + e u = u → α.re ≤ K * (β + |α.im|) := by
  have hA0 : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
  have hnpos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
  have hn0 : 0 ≤ ‖A‖ := le_of_lt hnpos
  have hna : A.re ≤ ‖A‖ := by
    have h := Complex.abs_re_le_norm A
    rwa [abs_of_pos hA] at h
  set eps : ℝ := A.re / (8 * ‖A‖) with heps
  have hepspos : 0 < eps := by rw [heps]; exact div_pos hA (mul_pos (by norm_num) hnpos)
  have heps0 : 0 ≤ eps := le_of_lt hepspos
  have heps8 : eps ≤ 1 / 8 := by
    rw [heps, div_le_iff₀ (mul_pos (by norm_num) hnpos)]
    nlinarith [hna]
  have h8eps : 8 * ‖A‖ * eps = A.re := by
    rw [heps]
    exact mul_div_cancel₀ A.re (mul_ne_zero (by norm_num) (ne_of_gt hnpos))
  have h2neps : 2 * ‖A‖ * eps ≤ A.re / 4 := by nlinarith [h8eps]
  set c0 : ℝ := A.re / 8 with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; exact div_pos hA (by norm_num)
  have hc0eq : c0 = A.re / 8 := hc0
  have hMpos : 0 < ‖A‖ + c0 := by
    rw [hc0]; exact add_pos_of_nonneg_of_pos hn0 (div_pos hA (by norm_num))
  have hM0 : 0 ≤ ‖A‖ + c0 := le_of_lt hMpos
  set δ : ℝ := min (1/2) (eps / (4 * (‖A‖ + c0))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by norm_num) (div_pos hepspos (mul_pos (by norm_num) hMpos))
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact le_trans (min_le_left _ _) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := by rw [hδ]; exact min_le_left _ _
  have hδle : δ ≤ eps / (4 * (‖A‖ + c0)) := by rw [hδ]; exact min_le_right _ _
  have hMδ : (‖A‖ + c0) * δ ≤ eps / 4 := by
    have h4 : δ * (4 * (‖A‖ + c0)) ≤ eps :=
      (le_div_iff₀ (mul_pos (by norm_num) hMpos)).mp hδle
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [h4]
  refine ⟨δ, hδpos, c0, hc0pos, 1, one_pos, ?_⟩
  intro e α β u hβ0 hβ1 hu heu heq
  have hre : (A * (star u)^2).re + α.re + (e u).re = 0 := by
    have h := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at h ⊢
    linarith
  have him : α.im = 2 * u.im - (A * (star u)^2).im - (e u).im := by
    have h := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.star_def, Complex.conj_im] at h ⊢
    linarith
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  by_cases hclose : |u.im| ≤ eps * ‖u‖
  · -- near the real axis
    have hlow : (A.re / 4) * ‖u‖^2 ≤ (A * (star u)^2).re := by
      rw [re_mul_conj_sq A u]
      exact case1_arith hu0 hA heps0 (Complex.abs_im_le_norm A) hclose
        (Complex.abs_re_le_norm u) (norm_sq_eq u) heps8 h2neps
    have hαre : α.re = -(A * (star u)^2).re - (e u).re := by linarith [hre]
    have hstep1 : α.re ≤ (c0 - A.re / 4) * ‖u‖^2 + β * ‖u‖ := by
      have h2 : -((e u).re) ≤ ‖e u‖ := by
        have h := Complex.abs_re_le_norm (e u); linarith [neg_le_abs (e u).re]
      nlinarith [hαre, hlow, h2, heu]
    have hstep2 : α.re ≤ β := by
      have hb1 : β * ‖u‖ ≤ β := by
        have h1 : β * ‖u‖ ≤ β * δ := mul_le_mul_of_nonneg_left hu hβ0
        have h2 : β * δ ≤ β := by simpa using mul_le_mul_of_nonneg_left hδ1 hβ0
        linarith [h1, h2]
      have hnn : (c0 - A.re / 4) * ‖u‖^2 ≤ 0 := by
        have hle : c0 - A.re / 4 ≤ 0 := by nlinarith [hc0eq, hA]
        exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg ‖u‖)
      linarith [hstep1, hnn, hb1]
    have hgoal : α.re ≤ β + |α.im| :=
      le_trans hstep2 (le_add_of_nonneg_right (abs_nonneg α.im))
    exact hgoal.trans (le_of_eq (one_mul (β + |α.im|)).symm)
  · -- off the real axis
    have hgt : eps * ‖u‖ < |u.im| := lt_of_not_ge hclose
    have htri : 2 * |u.im| ≤ |α.im| + |(A * (star u)^2).im| + |(e u).im| := by
      have h0 : 2 * u.im = α.im + (A * (star u)^2).im + (e u).im := by linarith [him]
      calc 2 * |u.im| = |2 * u.im| := by rw [abs_mul]; norm_num
        _ = |α.im + (A * (star u)^2).im + (e u).im| := by rw [h0]
        _ ≤ |α.im + (A * (star u)^2).im| + |(e u).im| := abs_add_le _ _
        _ ≤ (|α.im| + |(A * (star u)^2).im|) + |(e u).im| := by
            linarith [abs_add_le α.im (A * (star u)^2).im]
    have hAim : |(A * (star u)^2).im| ≤ ‖A‖ * ‖u‖^2 := by
      calc |(A * (star u)^2).im| ≤ ‖A * (star u)^2‖ := Complex.abs_im_le_norm _
        _ = ‖A‖ * ‖(star u)^2‖ := norm_mul A _
        _ = ‖A‖ * ‖u‖^2 := by rw [norm_pow, norm_star]
    have hQu : |(e u).im| ≤ c0 * ‖u‖^2 + β * ‖u‖ :=
      le_trans (Complex.abs_im_le_norm (e u)) heu
    have himlow : 2 * (eps * ‖u‖) - ‖A‖ * ‖u‖^2 - (c0 * ‖u‖^2 + β * ‖u‖) ≤ |α.im| := by
      nlinarith [htri, hAim, hQu, hgt]
    have hquad : (‖A‖ + c0) * ‖u‖^2 ≤ (eps / 4) * ‖u‖ := by
      have hMr : (‖A‖ + c0) * ‖u‖ ≤ eps / 4 :=
        le_trans (mul_le_mul_of_nonneg_left hu hM0) hMδ
      calc (‖A‖ + c0) * ‖u‖^2 = ((‖A‖ + c0) * ‖u‖) * ‖u‖ := by ring
        _ ≤ (eps / 4) * ‖u‖ := mul_le_mul_of_nonneg_right hMr hu0
    have hgap : β * (1 - δ) + (7 * eps / 4) * ‖u‖ ≤ β + |α.im| := by
      have hb1 : β * ‖u‖ ≤ β * δ := mul_le_mul_of_nonneg_left hu hβ0
      have h7 : (eps / 4) * ‖u‖ ≤ (7 * eps / 4) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (by linarith [heps0] : eps / 4 ≤ 7 * eps / 4) hu0
      nlinarith [himlow, hquad, hb1, h7]
    have hαub : α.re ≤ (‖A‖ + c0) * ‖u‖^2 + β * ‖u‖ := by
      have hαre : α.re = -(A * (star u)^2).re - (e u).re := by linarith [hre]
      have hP : -(A * (star u)^2).re ≤ ‖A‖ * ‖u‖^2 := by
        have h := Complex.abs_re_le_norm (A * (star u)^2)
        have hnorm : ‖A * (star u)^2‖ = ‖A‖ * ‖u‖^2 := by
          rw [norm_mul, norm_pow, norm_star]
        linarith [h, hnorm, neg_le_abs (A * (star u)^2).re]
      have hQ : -((e u).re) ≤ c0 * ‖u‖^2 + β * ‖u‖ := by
        have h := Complex.abs_re_le_norm (e u); linarith [neg_le_abs (e u).re, heu]
      calc α.re = -(A * (star u)^2).re - (e u).re := hαre
        _ = -(A * (star u)^2).re + (-((e u).re)) := by ring
        _ ≤ ‖A‖ * ‖u‖^2 + (c0 * ‖u‖^2 + β * ‖u‖) := add_le_add hP hQ
        _ = (‖A‖ + c0) * ‖u‖^2 + β * ‖u‖ := by ring
    have hgoal : α.re ≤ β + |α.im| :=
      case2_arith hβ0 hδhalf heps0 hM0 hu0 hu hMδ hαub hgap
    exact hgoal.trans (le_of_eq (one_mul (β + |α.im|)).symm)

end Work.FBif
