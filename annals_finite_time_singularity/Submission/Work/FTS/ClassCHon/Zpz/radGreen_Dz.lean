import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassC.radGreen_deriv1_form
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_lower
import Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_lower
import Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_upper
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_lower
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_upper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

/-
# `Work.FTS.ClassCHon.Zpz.radGreen_Dz`

`radGreen α m c` (`Work.FTS.PhiStar.Radial.radGreen`, the explicit decaying-at-`∞` solution of the
mode-`m` radial Euler equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, with
`λ_m = 2m(2m+5)`) is the Euler Green function

  `radGreen α m c z = K·(z^{-q}·∫_0^z c t^{q-1} + z^{p}·∫_z^∞ c t^{-p-1})`,
  `K = 1/(α(4m+5))`, `q = (2m+5)/α`, `p = 2m/α`.

The claim is that the `t ∂_t`-weighted source `t ↦ t·c'(t)` is again handled by the *same* Green
function, one order up: `z·∂_z(radGreen α m c) z = radGreen α m (t·c') z`.  The reason is that
`D = z∂_z` commutes with the Euler operator `R = -(α²D² + 5αD)`; on the explicit formula this is
the pair of integration-by-parts identities

  `∫_0^z c'(t) t^q dt = c(z)z^q - q·∫_0^z c t^{q-1}dt`   (boundary `c t^q → 0` at `0⁺`),
  `∫_z^∞ c'(t)t^{-p}dt = -c(z)z^{-p} + p·∫_z^∞ c t^{-p-1}dt`  (boundary `c t^{-p} → 0` at `∞`),

whose boundary terms vanish (`Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_lower` /
`..._upper`) thanks to the two integrability hypotheses `h0` (which kills a non-zero limit at `0⁺`
because `1/t` is not integrable there) and `hinf` (same at `∞`).

The first derivative of `radGreen` is taken from the existing
`Work.FTS.ClassC.radGreen_deriv1_form`,
`z·∂_z(radGreen α m c) z = K·(p·rgG2 - q·rgG1) = K·(p·z^p·rgB - q·z^{-q}·rgA)`, and the right-hand
side is unfolded with `Work.FTS.EllExist.radGreen_eq`; the two integration-by-parts identities
(`Work.FTS.ClassCHon.Zpz.radGreen_ibp_lower` / `..._upper`) then turn the two sides into the same
expression.
-/

theorem radGreen_Dz {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1))
    (hd0 : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.PhiStar.Radial.radGreen α m (fun t => t * deriv c t) z := by
  intro z hz
  have hcont : ContinuousOn c (Set.Ioi 0) :=
    fun t ht => (hcd t ht).continuousAt.continuousWithinAt
  have hliml := rpow_mul_tendsto_zero_lower (q := Work.FTS.EllExist.rgQ α m)
    (c := c) hcd h0 hd0
  have hlimu := rpow_mul_tendsto_zero_upper (p := Work.FTS.EllExist.rgP α m)
    (c := c) hcd hinf hdinf
  have hlow := radGreen_ibp_lower (α := α) (c := c)
    hα m hcd hliml h0 hd0 hdinf z hz
  have hup := radGreen_ibp_upper (α := α) (c := c)
    hα m hcd hlimu hinf hd0 hdinf z hz
  have hL := Work.FTS.ClassC.radGreen_deriv1_form (α := α) (c := c)
    hα m hcont h0 hinf z hz
  have hR := Work.FTS.EllExist.radGreen_eq α m (fun t => t * deriv c t) z
  rw [hL, hR]
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]
  rw [hlow, hup]
  have hzq : z ^ (-(Work.FTS.EllExist.rgQ α m)) * z ^ (Work.FTS.EllExist.rgQ α m) = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have hzp : z ^ (Work.FTS.EllExist.rgP α m) * z ^ (-(Work.FTS.EllExist.rgP α m)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  have h1 : z ^ (-(Work.FTS.EllExist.rgQ α m)) * (c z * z ^ (Work.FTS.EllExist.rgQ α m))
      = c z := by
    rw [show z ^ (-(Work.FTS.EllExist.rgQ α m)) * (c z * z ^ (Work.FTS.EllExist.rgQ α m))
        = c z * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * z ^ (Work.FTS.EllExist.rgQ α m))
        from by ring, hzq, mul_one]
  have h2 : z ^ (Work.FTS.EllExist.rgP α m) * (c z * z ^ (-(Work.FTS.EllExist.rgP α m)))
      = c z := by
    rw [show z ^ (Work.FTS.EllExist.rgP α m) * (c z * z ^ (-(Work.FTS.EllExist.rgP α m)))
        = c z * (z ^ (Work.FTS.EllExist.rgP α m) * z ^ (-(Work.FTS.EllExist.rgP α m)))
        from by ring, hzp, mul_one]
  have hgoal :
      Work.FTS.EllExist.rgP α m * (z ^ (Work.FTS.EllExist.rgP α m)
            * Work.FTS.EllExist.rgB α m c z)
          - Work.FTS.EllExist.rgQ α m * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * Work.FTS.EllExist.rgA α m c z)
        = z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (c z * z ^ (Work.FTS.EllExist.rgQ α m)
              - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgA α m c z)
          + z ^ (Work.FTS.EllExist.rgP α m) * (-(c z * z ^ (-(Work.FTS.EllExist.rgP α m)))
              + Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgB α m c z) := by
    rw [mul_sub, mul_add, mul_neg, h1, h2]
    ring
  rw [hgoal]
  ring

end Work.FTS.ClassCHon.Zpz
