import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-- The `k = 0` "hard" summand of the transport pairing, in its angular slice.  For `g`
smooth on a neighbourhood of the closed quadrant and `z ≥ 0`, the function
`θ ↦ ∂_z(D_z⁴ g)(z,θ) · D_z⁴ g(z,θ) · w(z)² · sin(2θ)^{-η}` is integrable on `Iθ`.

Here `w(z) = (1+z)²/z²` is a constant in `θ` and `η = 99/100 < 1`, so the only singular
factor is `sin(2θ)^{-η}`, integrable at both endpoints.  Both `θ ↦ ∂_z(D_z⁴ g)(z,θ)` and
`θ ↦ D_z⁴ g(z,θ)` are continuous on the compact `Iθ`
(`Work.FTS.H2.continuousOn_slice` applied to `SmoothNbhd.pz (SmoothNbhd.DzIter hsmg 4)`
resp. `SmoothNbhd.DzIter hsmg 4`), hence bounded in absolute value by constants
(`Work.FTS.H2.exists_nonneg_bound_abs`).  The integrand is therefore dominated by
`K · sin(2θ)^{-η}`, integrable on `Iθ` by `Work.Spaces.sin_two_rpow (-η)` (hypothesis
`-1 < -η` from `Work.Spaces.eta_lt_one`) up to a constant factor; conclude with
`Integrable.mono'` and a.e. strong measurability of the integrand. -/
theorem HardSummandZero (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ * Work.Spaces.DzIter 4 g z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  -- The two `θ`-dependent factors are continuous, hence bounded, on the compact `Iθ`.
  have hcontA : ContinuousOn (fun θ => Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ)
      Work.Spaces.Iθ :=
    Work.FTS.H2.continuousOn_slice
      (Work.Spaces.SmoothNbhd.pz (Work.Spaces.SmoothNbhd.DzIter hsmg 4)) hz
  have hcontB : ContinuousOn (fun θ => Work.Spaces.DzIter 4 g z θ) Work.Spaces.Iθ :=
    Work.FTS.H2.continuousOn_slice (Work.Spaces.SmoothNbhd.DzIter hsmg 4) hz
  obtain ⟨C1, _hC1nn, hC1⟩ := Work.FTS.H2.exists_nonneg_bound_abs hcontA
  obtain ⟨C2, _hC2nn, hC2⟩ := Work.FTS.H2.exists_nonneg_bound_abs hcontB
  -- The majorant `C1 * C2 * w(z)^2 * sin(2θ)^{-η}` is integrable on `Iθ`.
  have hsin_int : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
  have hmaj : IntegrableOn
      (fun θ : ℝ => C1 * C2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hsin_int.const_mul _
  -- Strong measurability of the integrand w.r.t. the restricted measure.
  have hmeas : AEStronglyMeasurable
      (fun θ => Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ * Work.Spaces.DzIter 4 g z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (((hcontA.aestronglyMeasurable measurableSet_Icc).mul
        (hcontB.aestronglyMeasurable measurableSet_Icc)).mul_const _).mul
      ((Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id))
        (-(Work.Spaces.eta))).aestronglyMeasurable)
  refine hmaj.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _
  have hc2 : |(Work.Spaces.w z) ^ 2| = (Work.Spaces.w z) ^ 2 := abs_of_nonneg (sq_nonneg _)
  have hsabs : |(Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))|
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := abs_of_nonneg hsnn
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, hc2, hsabs]
  gcongr
  · exact hC1 θ hθ
  · exact hC2 θ hθ

end Work.FTS.H2
