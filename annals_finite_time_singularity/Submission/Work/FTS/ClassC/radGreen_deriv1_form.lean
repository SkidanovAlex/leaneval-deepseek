import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- The first derivative of `radGreen`, written with the named pieces of
`Work.FTS.EllExist.RadGreenDefs`: for `z > 0`,

  `z · ∂_z radGreen α m c z = rgK α m · (rgP α m · rgG2 α m c z - rgQ α m · rgG1 α m c z)`.

The explicit first derivative `rgiD1` of the sibling `radGreenI` (`PhiStar.Series`) is
`rgK α m · (-(rgQ α m) · z^{-(rgQ α m) - 1} · rgA z + rgP α m · z^{rgP α m - 1} · rgB z)`,
and multiplying by `z` combines the powers `z^{-(rgQ)-1}·z = z^{-(rgQ)}` and
`z^{rgP-1}·z = z^{rgP}` (`Real.rpow_add`), leaving exactly
`rgP · z^{rgP} rgB - rgQ · z^{-(rgQ)} rgA = rgP · rgG2 - rgQ · rgG1`. -/
theorem radGreen_deriv1_form {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.EllExist.rgK α m
          * (Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgG2 α m c z
            - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgG1 α m c z) := by
  intro z hz
  -- `HasDerivAt` for `radGreen` (definitionally the same function as `radGreenI`).
  have hAt : HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (Work.FTS.PhiStar.Series.rgiD1 α m c z) z :=
    Work.FTS.PhiStar.Series.hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf z hz
  -- hence `deriv radGreen z = rgD1 α m c z`
  have hderiv : deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = Work.FTS.EllExist.rgD1 α m c z := by
    rw [hAt.deriv]
    simp only [Work.FTS.PhiStar.Series.rgiD1, Work.FTS.EllExist.rgD1,
      Work.FTS.PhiStar.Series.rgiK, Work.FTS.EllExist.rgK,
      Work.FTS.PhiStar.Series.rgiSn, Work.FTS.PhiStar.Series.rgiSp,
      Work.FTS.EllExist.rgQ, Work.FTS.EllExist.rgP,
      Work.FTS.PhiStar.Series.rgiA, Work.FTS.PhiStar.Series.rgiB,
      Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgB,
      Work.FTS.PhiStar.Series.rgiF1, Work.FTS.PhiStar.Series.rgiF2,
      Work.FTS.EllExist.rgF1, Work.FTS.EllExist.rgF2, neg_div]
  rw [hderiv]
  simp only [Work.FTS.EllExist.rgD1, Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]
  -- the two `rpow` combination identities
  have hz1 : z ^ (-(Work.FTS.EllExist.rgQ α m) - 1) * z = z ^ (-(Work.FTS.EllExist.rgQ α m)) := by
    rw [← Real.rpow_add_one (ne_of_gt hz) (-(Work.FTS.EllExist.rgQ α m) - 1),
      show -(Work.FTS.EllExist.rgQ α m) - 1 + 1
      = -(Work.FTS.EllExist.rgQ α m) from by ring]
  have hz2 : z ^ (Work.FTS.EllExist.rgP α m - 1) * z = z ^ (Work.FTS.EllExist.rgP α m) := by
    rw [← Real.rpow_add_one (ne_of_gt hz) (Work.FTS.EllExist.rgP α m - 1),
      show Work.FTS.EllExist.rgP α m - 1 + 1
      = Work.FTS.EllExist.rgP α m from by ring]
  rw [show z * (Work.FTS.EllExist.rgK α m
        * (-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1)
              * Work.FTS.EllExist.rgA α m c z
          + Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
              * Work.FTS.EllExist.rgB α m c z))
      = Work.FTS.EllExist.rgK α m
        * (-(Work.FTS.EllExist.rgQ α m) * (z ^ (-(Work.FTS.EllExist.rgQ α m) - 1) * z)
              * Work.FTS.EllExist.rgA α m c z
          + Work.FTS.EllExist.rgP α m * (z ^ (Work.FTS.EllExist.rgP α m - 1) * z)
              * Work.FTS.EllExist.rgB α m c z) from by ring]
  rw [hz1, hz2]
  ring

end Work.FTS.ClassC
