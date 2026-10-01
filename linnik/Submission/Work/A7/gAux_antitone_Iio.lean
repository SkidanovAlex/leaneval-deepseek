/-
# Area 7 — antitonicity of `g` on the negative half-line

`Work.A7.gAux t = (t - 1 + e^{-t})/t²` is the Laplace transform `∫₀¹ (1-u)e^{-tu} du`,
hence decreasing in `t` on each half-line.  The companion result on `(0, ∞)` lives in
`Submission/Work/A7/Bfun_antitone.lean`; here we prove the mirrored statement on `(-∞, 0)`.
There the derivative numerator `N(t) = 2 - t - (t+2)e^{-t}` is *positive* while `t³` is
negative, so again `g' ≤ 0`.

The sign of the numerator is reduced, by the substitution `u = -t > 0`, to

  `2 + u - (2 - u)e^u > 0   (u > 0)`,

i.e. to `M(u) = (2 + u)e^{-u} + (u - 2) > 0`.  `M(0) = 0` and
`M'(u) = 1 - (1+u)e^{-u} > 0` for `u > 0` (because `1 + u < e^u` for `u ≠ 0`), so `M` is
strictly increasing on `[0, ∞)` and `M(u) > 0` for `u > 0`.
-/
import Mathlib
import Submission.Work.A7.BfunAux

noncomputable section

namespace Work.A7

open Set

/-- Derivative of `gAux` at `x ≠ 0`: `g'(t) = (2 - t - (t+2)e^{-t})/t³`. -/
private lemma hasDerivAt_gAux {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt gAux ((2 - x - (x + 2) * Real.exp (-x)) / x^3) x := by
  have hnum : HasDerivAt (fun t : ℝ => t - 1 + Real.exp (-t))
      (1 + Real.exp (-x) * (-1)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
      HasDerivAt.exp (hasDerivAt_neg x)
    exact h1.add h2
  have hden : HasDerivAt (fun t : ℝ => t^2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hdenne : x^2 ≠ 0 := pow_ne_zero 2 hx
  have h := hnum.div hden hdenne
  have heq : ((1 + Real.exp (-x) * (-1)) * x ^ 2 - (x - 1 + Real.exp (-x)) * (2 * x))
        / (x^2)^2
      = (2 - x - (x + 2) * Real.exp (-x)) / x^3 := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- The test function `M(u) = (2 + u)e^{-u} + (u - 2)`, written as a sum of two functions so
that the shape produced by `HasDerivAt.add` matches definitionally.  `M(0) = 0`. -/
private def Mf : ℝ → ℝ :=
  (fun v : ℝ => (2 + v) * Real.exp (-v)) + (fun v : ℝ => v - 2)

private lemma hasDerivAt_Mf (u : ℝ) :
    HasDerivAt Mf (1 - (1 + u) * Real.exp (-u)) u := by
  have h1 : HasDerivAt (fun v : ℝ => (2 + v) * Real.exp (-v))
      (1 * Real.exp (-u) + (2 + u) * (Real.exp (-u) * (-1))) u :=
    ((hasDerivAt_id u).const_add 2).mul (HasDerivAt.exp (hasDerivAt_neg u))
  have h2 : HasDerivAt (fun v : ℝ => v - 2) 1 u := by
    simpa using (hasDerivAt_id u).sub_const 2
  have h := h1.add h2
  have heq : (1 * Real.exp (-u) + (2 + u) * (Real.exp (-u) * (-1)) + 1)
      = 1 - (1 + u) * Real.exp (-u) := by ring
  rw [heq] at h
  exact h

private lemma exp_mul_exp_neg (u : ℝ) : Real.exp u * Real.exp (-u) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- `M` is strictly increasing on `[0, ∞)`, since `M'(u) = 1 - (1+u)e^{-u} > 0` for `u > 0`. -/
private lemma Mf_strictMono : StrictMonoOn Mf (Set.Ici 0) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) (f := Mf)
    (f' := fun u => 1 - (1 + u) * Real.exp (-u)) ?_ ?_ ?_
  · intro u _
    exact (hasDerivAt_Mf u).continuousAt.continuousWithinAt
  · intro u _
    exact (hasDerivAt_Mf u).hasDerivWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    have h1 : 1 + u < Real.exp u := by
      have := Real.add_one_lt_exp (x := u) (ne_of_gt hu)
      linarith
    have h3 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (-u))
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
    linarith

/-- `2 + u - (2 - u)e^u > 0` for `u > 0` (the numerator of `g'` at `t = -u`). -/
private lemma two_add_sub_mul_exp_pos {u : ℝ} (hu : 0 < u) :
    0 < 2 + u - (2 - u) * Real.exp u := by
  have hM0 : Mf 0 = 0 := by simp [Mf]
  have hM : Mf 0 < Mf u :=
    Mf_strictMono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu.le) hu
  have hMu : 0 < Mf u := by rw [hM0] at hM; exact hM
  have hkey : Real.exp u * Mf u = 2 + u - (2 - u) * Real.exp u := by
    have h1 : Real.exp u * Mf u
        = (2 + u) * (Real.exp u * Real.exp (-u)) + (u - 2) * Real.exp u := by
      simp only [Mf, Pi.add_apply]
      ring
    rw [exp_mul_exp_neg, mul_one] at h1
    linarith
  rw [← hkey]
  exact mul_pos (Real.exp_pos u) hMu

theorem gAux_antitone_Iio : AntitoneOn Work.A7.gAux (Set.Iio 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iio 0) (f := gAux)
    (f' := fun x => (2 - x - (x + 2) * Real.exp (-x)) / x^3) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_gAux (ne_of_lt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    exact (hasDerivAt_gAux (ne_of_lt hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    have hx' : x < 0 := hx
    have hnum : 0 < 2 - x - (x + 2) * Real.exp (-x) := by
      have h := two_add_sub_mul_exp_pos (u := -x) (neg_pos.mpr hx')
      have heq : (2 + -x - (2 - -x) * Real.exp (-x))
          = 2 - x - (x + 2) * Real.exp (-x) := by ring
      rw [heq] at h
      exact h
    have hden : x^3 < 0 := Odd.pow_neg (by norm_num) hx'
    exact le_of_lt (div_neg_of_pos_of_neg hnum hden)

end Work.A7
