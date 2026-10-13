/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Support/jet2_sub_le` — Lipschitz (in the four second partials) control of the order-2 jet

The setting of `Submission/Work/FTS_EllLimOK/BoxRegAux/Defs.lean`: `copBilin` is the continuous
linear map `(p,q) ↦ ellCop p q`, so that the second Fréchet derivative of a function `F : ℝ × ℝ → ℝ`
whose second partials `(∂_z∂_z, ∂_θ∂_z, ∂_z∂_θ, ∂_θ∂_θ)` are `(A,B,C,D)` is
`copBilin.comp ((ellCop A B).prod (ellCop C D))`.

Here we prove that the *norm* of the order-2 iterated Fréchet derivative is `1`-Lipschitz with
respect to those four partials: if the second derivative of `F` at `x` is the curried bilinear map
with entries `(A,B,C,D)` and at `y` the one with entries `(A',B',C',D')`, then

  `‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ |A-A'|+|B-B'|+|C-C'|+|D-D'|`.

The proof is a direct computation on the two directions `m 0`, `m 1`, using
`iteratedFDeriv_two_apply` (`(iteratedFDeriv ℝ 2 F x) m = (fderiv (fderiv F) x (m 0)) (m 1)`),
the linearity of the difference, and the elementary estimate `|v| ≤ ‖v‖` for the coordinates of a
point of `ℝ × ℝ` (whose norm is the sup norm).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

open scoped Real

/-- **The order-2 jet is `1`-Lipschitz in the four second partials.**  If the second Fréchet
derivative of `F : ℝ × ℝ → ℝ` at `x` (resp. `y`) is the curried bilinear map with entries
`(A,B,C,D)` (resp. `(A',B',C',D')`), then the difference of the two iterated second derivatives is
bounded in operator norm by `|A-A'| + |B-B'| + |C-C'| + |D-D'|`. -/
theorem norm_iterDF2_sub_le {F : ℝ × ℝ → ℝ} {x y : ℝ × ℝ} {A B C D A' B' C' D' : ℝ}
    (hx : fderiv ℝ (fderiv ℝ F) x = Work.FTS_EllLimOK.copBilin.comp
      ((Work.FTS_EllLimOK.ellCop A B).prod (Work.FTS_EllLimOK.ellCop C D)))
    (hy : fderiv ℝ (fderiv ℝ F) y = Work.FTS_EllLimOK.copBilin.comp
      ((Work.FTS_EllLimOK.ellCop A' B').prod (Work.FTS_EllLimOK.ellCop C' D'))) :
    ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖
      ≤ |A - A'| + |B - B'| + |C - C'| + |D - D'| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [sub_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hx, hy]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Work.FTS_EllLimOK.copBilin_apply, Work.FTS_EllLimOK.ellCop_apply]
  rw [Real.norm_eq_abs, Fin.prod_univ_two]
  have hh1 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
  have hh2 : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
  have hk1 : |(m 1).1| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 1)
  have hk2 : |(m 1).2| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 1)
  have h1n : (0 : ℝ) ≤ ‖m 1‖ := norm_nonneg _
  have hkey : (m 1).1 * ((m 0).1 * A + (m 0).2 * B) + (m 1).2 * ((m 0).1 * C + (m 0).2 * D) -
        ((m 1).1 * ((m 0).1 * A' + (m 0).2 * B') + (m 1).2 * ((m 0).1 * C' + (m 0).2 * D'))
      = (m 1).1 * (m 0).1 * (A - A') + (m 1).1 * (m 0).2 * (B - B')
        + (m 1).2 * (m 0).1 * (C - C') + (m 1).2 * (m 0).2 * (D - D') := by ring
  rw [hkey]
  have e1 : |(m 1).1 * (m 0).1 * (A - A')| ≤ ‖m 1‖ * (‖m 0‖ * |A - A'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).1| * |(m 0).1| * |A - A'| ≤ (‖m 1‖ * ‖m 0‖) * |A - A'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk1 hh1 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |A - A'|) := by ring
  have e2 : |(m 1).1 * (m 0).2 * (B - B')| ≤ ‖m 1‖ * (‖m 0‖ * |B - B'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).1| * |(m 0).2| * |B - B'| ≤ (‖m 1‖ * ‖m 0‖) * |B - B'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk1 hh2 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |B - B'|) := by ring
  have e3 : |(m 1).2 * (m 0).1 * (C - C')| ≤ ‖m 1‖ * (‖m 0‖ * |C - C'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).2| * |(m 0).1| * |C - C'| ≤ (‖m 1‖ * ‖m 0‖) * |C - C'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk2 hh1 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |C - C'|) := by ring
  have e4 : |(m 1).2 * (m 0).2 * (D - D')| ≤ ‖m 1‖ * (‖m 0‖ * |D - D'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).2| * |(m 0).2| * |D - D'| ≤ (‖m 1‖ * ‖m 0‖) * |D - D'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk2 hh2 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |D - D'|) := by ring
  have hsplit : |(m 1).1 * (m 0).1 * (A - A') + (m 1).1 * (m 0).2 * (B - B')
        + (m 1).2 * (m 0).1 * (C - C') + (m 1).2 * (m 0).2 * (D - D')|
      ≤ |(m 1).1 * (m 0).1 * (A - A')| + |(m 1).1 * (m 0).2 * (B - B')|
        + |(m 1).2 * (m 0).1 * (C - C')| + |(m 1).2 * (m 0).2 * (D - D')| := by
    have h12 := abs_add_le ((m 1).1 * (m 0).1 * (A - A')) ((m 1).1 * (m 0).2 * (B - B'))
    have h123 := abs_add_le (((m 1).1 * (m 0).1 * (A - A')) + ((m 1).1 * (m 0).2 * (B - B')))
      ((m 1).2 * (m 0).1 * (C - C'))
    have h1234 := abs_add_le ((((m 1).1 * (m 0).1 * (A - A')) + ((m 1).1 * (m 0).2 * (B - B')))
      + ((m 1).2 * (m 0).1 * (C - C'))) ((m 1).2 * (m 0).2 * (D - D'))
    linarith
  refine le_trans hsplit ?_
  calc |(m 1).1 * (m 0).1 * (A - A')| + |(m 1).1 * (m 0).2 * (B - B')|
        + |(m 1).2 * (m 0).1 * (C - C')| + |(m 1).2 * (m 0).2 * (D - D')|
      ≤ ‖m 1‖ * (‖m 0‖ * |A - A'|) + ‖m 1‖ * (‖m 0‖ * |B - B'|)
        + ‖m 1‖ * (‖m 0‖ * |C - C'|) + ‖m 1‖ * (‖m 0‖ * |D - D'|) := by linarith
    _ = (|A - A'| + |B - B'| + |C - C'| + |D - D'|) * (‖m 0‖ * ‖m 1‖) := by ring

theorem jet2_sub_le
    {F : ℝ × ℝ → ℝ} {x y : ℝ × ℝ} {A B C D A' B' C' D' : ℝ}
    (hx : fderiv ℝ (fderiv ℝ F) x = Work.FTS_EllLimOK.copBilin.comp
      ((Work.FTS_EllLimOK.ellCop A B).prod (Work.FTS_EllLimOK.ellCop C D)))
    (hy : fderiv ℝ (fderiv ℝ F) y = Work.FTS_EllLimOK.copBilin.comp
      ((Work.FTS_EllLimOK.ellCop A' B').prod (Work.FTS_EllLimOK.ellCop C' D'))) :
    ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖
      ≤ |A - A'| + |B - B'| + |C - C'| + |D - D'| :=
  norm_iterDF2_sub_le hx hy

end Work.FTS_EllLimOK.ProducerH.H2.Support
