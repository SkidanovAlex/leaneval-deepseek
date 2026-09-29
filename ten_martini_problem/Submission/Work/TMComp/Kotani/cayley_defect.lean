import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.Psi_bounds

/-!
# The Schwarz-Pick bound for the jump of `Psi` (replaces the route's (K3))

For `X Y : C` with `0 < X.im`, `0 < Y.im`:

  `norm (cayley X - cayley Y) <= 2 * sqrt (delta X Y / (delta X Y + 4))`,  `delta X Y = norm (X-Y)^2/(X.im*Y.im)`,

i.e. the Euclidean jump is controlled by the *hyperbolic* distance (Schwarz-Pick).  Since
`delta a c / (delta a c + 4) = norm (a-c)^2/norm (a - conj c)^2`, and `a - c`, `a - conj c = defect`
are the route's objects, the jump of `cayley o Psi` is bounded by `2 * norm (a-c)/norm (defect)`,
whose `y`-integral is controlled by the (K2)-quantity `Integral X_K`
(`X_K = im(defect) * norm (a-c)^2/(N1*N2*norm (defect)^2)`) times the *first* moment
`Integral im(defect)` in the phase.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `norm (X + i)^2 = X.re^2 + (X.im + 1)^2`. -/
theorem norm_add_I_sq (X : ℂ) :
    ‖X + Complex.I‖ ^ 2 = X.re ^ 2 + (X.im + 1) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  ring

/-- `cayley X - cayley Y = 2i(X-Y)/((X+i)(Y+i))`. -/
theorem cayley_sub_eq (X Y : ℂ) (hX : X + Complex.I ≠ 0) (hY : Y + Complex.I ≠ 0) :
    cayley X - cayley Y
      = 2 * Complex.I * (X - Y) / ((X + Complex.I) * (Y + Complex.I)) := by
  unfold cayley
  have hXY : (X + Complex.I) * (Y + Complex.I) ≠ 0 := mul_ne_zero hX hY
  field_simp
  ring

/-- **The key inequality.**  For `X Y` in the upper half plane,
`norm (X-Y)^2 + 4*X.im*Y.im <= norm (X+i)^2 * norm (Y+i)^2`. -/
theorem key_ineq (X Y : ℂ) (hX : 0 < X.im) (hY : 0 < Y.im) :
    ‖X - Y‖ ^ 2 + 4 * (X.im * Y.im) ≤ ‖X + Complex.I‖ ^ 2 * ‖Y + Complex.I‖ ^ 2 := by
  have h1 : ‖X - Y‖ ^ 2 = (X.re - Y.re) ^ 2 + (X.im - Y.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  rw [h1, norm_add_I_sq, norm_add_I_sq]
  nlinarith [sq_nonneg (X.re * Y.re + 1), sq_nonneg X.im, sq_nonneg Y.im,
    sq_nonneg (X.im * Y.re), sq_nonneg (X.re * Y.im), sq_nonneg (X.im * Y.im),
    sq_nonneg X.re, sq_nonneg Y.re, hX, hY]

/-- The algebraic rewrite:
`2*sqrt (delta X Y / (delta X Y + 4)) = 2*norm (X-Y)/sqrt (norm (X-Y)^2 + 4*X.im*Y.im)`. -/
theorem two_sqrt_delta_eq {X Y : ℂ} (hX : 0 < X.im) (hY : 0 < Y.im) :
    2 * Real.sqrt (delta X Y / (delta X Y + 4))
      = 2 * ‖X - Y‖ / Real.sqrt (‖X - Y‖ ^ 2 + 4 * (X.im * Y.im)) := by
  have hp : 0 < X.im * Y.im := mul_pos hX hY
  have h4 : 0 < ‖X - Y‖ ^ 2 + 4 * (X.im * Y.im) := by positivity
  have hne : X.im * Y.im ≠ 0 := ne_of_gt hp
  have hkey : delta X Y / (delta X Y + 4)
      = ‖X - Y‖ ^ 2 / (‖X - Y‖ ^ 2 + 4 * (X.im * Y.im)) := by
    rw [delta]
    field_simp
  rw [hkey, Real.sqrt_div (by positivity : (0 : ℝ) ≤ ‖X - Y‖ ^ 2),
    Real.sqrt_sq (norm_nonneg _)]
  ring

/-- **Schwarz-Pick bound for the Cayley transform (jump form).** -/
theorem norm_cayley_sub_le {X Y : ℂ} (hX : 0 < X.im) (hY : 0 < Y.im) :
    ‖cayley X - cayley Y‖ ≤ 2 * Real.sqrt (delta X Y / (delta X Y + 4)) := by
  have hX0 : X + Complex.I ≠ 0 := by
    intro h; have him := congrArg Complex.im h
    simp at him
    linarith
  have hY0 : Y + Complex.I ≠ 0 := by
    intro h; have him := congrArg Complex.im h
    simp at him
    linarith
  rw [cayley_sub_eq X Y hX0 hY0, two_sqrt_delta_eq hX hY]
  have hgoal : ‖(2 : ℂ) * Complex.I * (X - Y) / ((X + Complex.I) * (Y + Complex.I))‖
      = 2 * ‖X - Y‖ / (‖X + Complex.I‖ * ‖Y + Complex.I‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    norm_num
  rw [hgoal]
  have hAB : 0 < ‖X + Complex.I‖ * ‖Y + Complex.I‖ :=
    mul_pos (norm_pos_iff.mpr hX0) (norm_pos_iff.mpr hY0)
  have hs : 0 < Real.sqrt (‖X - Y‖ ^ 2 + 4 * (X.im * Y.im)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hle : Real.sqrt (‖X - Y‖ ^ 2 + 4 * (X.im * Y.im))
      ≤ ‖X + Complex.I‖ * ‖Y + Complex.I‖ := by
    have h := key_ineq X Y hX hY
    have h2 : (‖X + Complex.I‖ * ‖Y + Complex.I‖) ^ 2
        = ‖X + Complex.I‖ ^ 2 * ‖Y + Complex.I‖ ^ 2 := by ring
    calc Real.sqrt (‖X - Y‖ ^ 2 + 4 * (X.im * Y.im))
        ≤ Real.sqrt ((‖X + Complex.I‖ * ‖Y + Complex.I‖) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [h2]; exact h)
      _ = ‖X + Complex.I‖ * ‖Y + Complex.I‖ := Real.sqrt_sq (by positivity)
  exact div_le_div_of_nonneg_left (by positivity) hs hle

/-- `Im (-1/z) = z.im/norm z^2` for `z` nonzero. -/
theorem neg_one_div_im {z : ℂ} (hz : z ≠ 0) : (-1 / z).im = z.im / ‖z‖ ^ 2 := by
  rw [show (-1 : ℂ) / z = -(z⁻¹) by ring, Complex.neg_im, Complex.inv_im,
    Complex.normSq_eq_norm_sq]
  ring

/-- `delta` is invariant under inversion (on the upper half plane). -/
theorem delta_inv {a c : ℂ} (ha : 0 < a.im) (hc : 0 < c.im) :
    delta (-1 / a) (-1 / c) = delta a c := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  have hsub : -1 / a - -1 / c = (a - c) / (a * c) := by field_simp; ring
  rw [delta, delta, neg_one_div_im ha0, neg_one_div_im hc0, hsub, norm_div, norm_mul]
  have han : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
  field_simp

/-- `delta` is invariant under `z -> -1/(z - w)` for real `w`. -/
theorem delta_inv_sub {a c : ℂ} (w : ℝ) (ha : 0 < a.im) (hc : 0 < c.im) :
    delta (-1 / (a - (w : ℂ))) (-1 / (c - (w : ℂ))) = delta a c := by
  have h1 : (a - (w : ℂ)).im = a.im := by simp
  have h2 : (c - (w : ℂ)).im = c.im := by simp
  have ha' : 0 < (a - (w : ℂ)).im := by rw [h1]; exact ha
  have hc' : 0 < (c - (w : ℂ)).im := by rw [h2]; exact hc
  rw [delta_inv ha' hc']
  have h : delta (a - (w : ℂ)) (c - (w : ℂ)) = delta a c := by
    have h2 := delta_add_re (a - (w : ℂ)) (c - (w : ℂ)) (w : ℝ)
    rw [sub_add_cancel, sub_add_cancel] at h2
    exact h2.symm
  rw [h]

/-- **The algebraic form of the Schwarz-Pick factor.**  For `a c` in the upper half plane,
`delta a c / (delta a c + 4) = norm (a-c)^2/norm (a - conj c)^2`. -/
theorem delta_div_delta_add_four {a c : ℂ} (ha : 0 < a.im) (hc : 0 < c.im) :
    delta a c / (delta a c + 4) = ‖a - c‖ ^ 2 / ‖a - star c‖ ^ 2 := by
  have hpos : 0 < a.im * c.im := mul_pos ha hc
  have hkey : ‖a - star c‖ ^ 2 = ‖a - c‖ ^ 2 + 4 * (a.im * c.im) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.star_def, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  have hδ : delta a c = ‖a - c‖ ^ 2 / (a.im * c.im) := rfl
  rw [hδ, hkey]
  have h4 : 0 < ‖a - c‖ ^ 2 + 4 * (a.im * c.im) := by positivity
  field_simp

/-- **Schwarz-Pick jump bound, inversion form.**  For `a c` in the upper half plane and real `w`:
`norm (cayley (-1/(a-w)) - cayley (-1/(c-w))) <= 2*norm (a-c)/norm (a - conj c)`. -/
theorem norm_cayley_inv_sub_le {a c : ℂ} (w : ℝ) (ha : 0 < a.im) (hc : 0 < c.im) :
    ‖cayley (-1 / (a - (w : ℂ))) - cayley (-1 / (c - (w : ℂ)))‖
      ≤ 2 * ‖a - c‖ / ‖a - star c‖ := by
  have him1 : 0 < (-1 / (a - (w : ℂ))).im := by
    have hne : a - (w : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have h := neg_one_div_im hne
    rw [h]
    exact div_pos (by simpa using ha) (by positivity)
  have him2 : 0 < (-1 / (c - (w : ℂ))).im := by
    have hne : c - (w : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have h := neg_one_div_im hne
    rw [h]
    exact div_pos (by simpa using hc) (by positivity)
  have h1 := norm_cayley_sub_le (X := -1 / (a - (w : ℂ))) (Y := -1 / (c - (w : ℂ))) him1 him2
  have h2 : delta (-1 / (a - (w : ℂ))) (-1 / (c - (w : ℂ))) = delta a c :=
    delta_inv_sub w ha hc
  rw [h2] at h1
  have h3 : delta a c / (delta a c + 4) = ‖a - c‖ ^ 2 / ‖a - star c‖ ^ 2 :=
    delta_div_delta_add_four ha hc
  rw [h3] at h1
  have h4 : 0 < ‖a - star c‖ := by
    have h : (a - star c).im = a.im + c.im := by
      simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]
      ring
    refine norm_pos_iff.mpr ?_
    intro hh
    have h5 := congrArg Complex.im hh
    rw [h] at h5
    simp at h5
    linarith
  have h5 : Real.sqrt (‖a - c‖ ^ 2 / ‖a - star c‖ ^ 2) = ‖a - c‖ / ‖a - star c‖ := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [h5] at h1
  calc ‖cayley (-1 / (a - (w : ℂ))) - cayley (-1 / (c - (w : ℂ)))‖
      ≤ 2 * (‖a - c‖ / ‖a - star c‖) := h1
    _ = 2 * ‖a - c‖ / ‖a - star c‖ := by ring

/-- **Schwarz-Pick jump bound, defect form.**  For `X Y` in the upper half plane,
`norm (cayley X - cayley Y) <= 2*norm (X-Y)/norm (X - conj Y)`. -/
theorem norm_cayley_sub_le' {X Y : ℂ} (hX : 0 < X.im) (hY : 0 < Y.im) :
    ‖cayley X - cayley Y‖ ≤ 2 * ‖X - Y‖ / ‖X - star Y‖ := by
  have h1 := norm_cayley_sub_le hX hY
  have h2 : delta X Y / (delta X Y + 4) = ‖X - Y‖ ^ 2 / ‖X - star Y‖ ^ 2 :=
    delta_div_delta_add_four hX hY
  rw [h2] at h1
  have h3 : Real.sqrt (‖X - Y‖ ^ 2 / ‖X - star Y‖ ^ 2) = ‖X - Y‖ / ‖X - star Y‖ := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [h3] at h1
  calc ‖cayley X - cayley Y‖ ≤ 2 * (‖X - Y‖ / ‖X - star Y‖) := h1
    _ = 2 * ‖X - Y‖ / ‖X - star Y‖ := by ring

/-- **The jump bound in the form of the route's (K2)-quantity.**
For `X Y` in the upper half plane, with `B = X - conj Y`:
`norm (cayley X - cayley Y)^2 <= (im B * delta X Y / norm B^2) * im B`,
and `im B * delta X Y / norm B^2 = im B * norm (X-Y)^2/(X.im * Y.im * norm B^2)` is exactly the
integrand of (K2), while `im B = X.im + Y.im`. -/
theorem norm_cayley_sub_sq_le {X Y : ℂ} (hX : 0 < X.im) (hY : 0 < Y.im) :
    ‖cayley X - cayley Y‖ ^ 2
      ≤ (X.im + Y.im) ^ 2 * ‖X - Y‖ ^ 2 / ((X.im * Y.im) * ‖X - star Y‖ ^ 2) := by
  have h1 := norm_cayley_sub_le' hX hY
  have him : (X - star Y).im = X.im + Y.im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]
    ring
  have hB2 : 0 < ‖X - star Y‖ ^ 2 := by
    refine pow_pos (norm_pos_iff.mpr ?_) 2
    intro hh
    have h5 := congrArg Complex.im hh
    rw [him] at h5
    simp at h5
    linarith
  have hNpos : 0 < X.im * Y.im := mul_pos hX hY
  have hCnn : 0 ≤ ‖X - Y‖ ^ 2 := by positivity
  have h4N : 4 * (X.im * Y.im) ≤ (X.im + Y.im) ^ 2 := by
    nlinarith [sq_nonneg (X.im - Y.im)]
  have hRnn : 0 ≤ 2 * ‖X - Y‖ / ‖X - star Y‖ :=
    div_nonneg (by positivity) (norm_nonneg (X - star Y))
  have h1sq : ‖cayley X - cayley Y‖ ^ 2
      ≤ (2 * ‖X - Y‖ / ‖X - star Y‖) ^ 2 := by
    nlinarith [norm_nonneg (cayley X - cayley Y), h1, hRnn]
  have hgoal : (2 * ‖X - Y‖ / ‖X - star Y‖) ^ 2
      = 4 * ‖X - Y‖ ^ 2 / ‖X - star Y‖ ^ 2 := by
    rw [div_pow]
    ring
  have hmono : 4 * ‖X - Y‖ ^ 2 / ‖X - star Y‖ ^ 2
      ≤ (X.im + Y.im) ^ 2 * ‖X - Y‖ ^ 2 / ((X.im * Y.im) * ‖X - star Y‖ ^ 2) := by
    have hNA : 0 < (X.im * Y.im) * ‖X - star Y‖ ^ 2 := by positivity
    rw [div_le_iff₀ hB2, div_mul_eq_mul_div, le_div_iff₀ hNA]
    nlinarith [h4N, hCnn, hNpos, hB2, mul_nonneg hCnn (le_of_lt hNpos),
      mul_nonneg hCnn (le_of_lt hB2)]
  linarith [h1sq, hgoal ▸ le_refl ((2 * ‖X - Y‖ / ‖X - star Y‖) ^ 2), hmono]

/-- The (K2)-form of the bound: rewriting `delta X Y` and `(X - conj Y).im`. -/
theorem norm_cayley_sub_sq_le_K {X Y : ℂ} (hX : 0 < X.im) (hY : 0 < Y.im) :
    ‖cayley X - cayley Y‖ ^ 2
      ≤ ((X - star Y).im * delta X Y / ‖X - star Y‖ ^ 2) * (X.im + Y.im) := by
  have h := norm_cayley_sub_sq_le hX hY
  have him : (X - star Y).im = X.im + Y.im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]
    ring
  have hL : ((X - star Y).im * delta X Y / ‖X - star Y‖ ^ 2) * (X.im + Y.im)
      = (X.im + Y.im) ^ 2 * ‖X - Y‖ ^ 2 / ((X.im * Y.im) * ‖X - star Y‖ ^ 2) := by
    rw [delta, him, mul_comm (X.im + Y.im), div_mul_eq_mul_div, mul_assoc,
      div_mul_eq_mul_div]
    ring
  rw [hL]
  exact h

/-- **The jump bound of (L7)/(L9), in the correct form.**  With `E = E₀ + iε` (`ε > 0`),
`a = mfun E y - iε/2` and `c = sigSec E y + iε/2` (so that `a - conj c = defect E y`),
the Euclidean jump of `cayley ∘ Psi` across the real axis satisfies
`norm (cayley Ψ⁺ - cayley Ψ⁻) <= 2 * norm (a-c) / norm (defect E y)`. -/
theorem cayley_Psi_jump_le (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    ‖cayley (Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y)‖
      ≤ 2 * ‖(mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
                - ((ε / 2 : ℝ) : ℂ) * Complex.I)
              - (sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
                + ((ε / 2 : ℝ) : ℂ) * Complex.I)‖
          / ‖defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y‖ := by
  set E : ℂ := (E₀ : ℂ) + (ε : ℂ) * Complex.I with hEdef
  set E' : ℂ := (E₀ : ℂ) - (ε : ℂ) * Complex.I with hEpdef
  have hEim : E.im = ε := by
    rw [hEdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hEpim : E'.im = -ε := by
    rw [hEpdef]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hEpos : 0 < E.im := by rw [hEim]; exact hε
  have hEpneg : E'.im < 0 := by rw [hEpim]; linarith
  have hstar : star E' = E := by
    rw [hEdef, hEpdef]
    simp only [Complex.star_def, star_sub, star_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hPsi_up : Psi α lam E y
      = -1 / ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)) := by
    rw [Psi, glued_of_pos α lam hEpos y, hEdef]
    congr 1
    push_cast
    ring
  have hPsi_dn : Psi α lam E' y
      = -1 / ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)) := by
    rw [Psi, glued_of_neg α lam hEpneg hstar y, hEpdef]
    congr 1
    push_cast
    ring
  rw [hPsi_up, hPsi_dn]
  have ha : 0 < (mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I).im := by
    have h := mfun_im_ge_self α lam hEpos y
    rw [hEim] at h
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, sub_zero]
    linarith
  have hc : 0 < (sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I).im := by
    have h := sigSec_im_pos α lam hEpos y
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, add_zero]
    linarith
  have hdef : (mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - star (sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I) = defect α lam E y := by
    have h1 : star (sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
        = sSec α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I := by
      simp only [star_add, conj_sigSec, star_mul, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal]
      try ring
    rw [defect, h1]
    ring
  have hmain := norm_cayley_inv_sub_le (a := mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
    (c := sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I) (E₀ / 2) ha hc
  rw [hdef] at hmain
  have hgoal : ‖(mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
                - ((ε / 2 : ℝ) : ℂ) * Complex.I)
              - (sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
                + ((ε / 2 : ℝ) : ℂ) * Complex.I)‖
      = ‖(mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
          - (sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by
    rw [← hEdef]
  rw [hgoal]
  exact hmain

end Work.TMComp.Kotani
