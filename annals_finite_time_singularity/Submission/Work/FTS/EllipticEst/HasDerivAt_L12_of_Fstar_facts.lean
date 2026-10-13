import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Topology

/-- **The derivative of the singular term `L₁₂`.**  If the angular moment `F_*(r) = Fstar F r`
is smooth on `(0,∞)` and `r ↦ F_*(r)/r` is integrable there, then
`L₁₂(F)(z) = 3 ∫_z^∞ F_*(r)/r dr` is differentiable at every `z > 0`, with derivative
`-3 F_*(z)/z` (the fundamental theorem of calculus for the improper integral `∫_z^∞`). -/
theorem HasDerivAt_L12_of_Fstar_facts (F : ℝ → ℝ → ℝ)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  set g : ℝ → ℝ := fun r => Work.Elliptic.Fstar F r / r with hg
  -- the density `g` is continuous on `(0,∞)`, hence at `z` (where `z ≠ 0`)
  have hgcontOn : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    rw [hg]
    exact ((hFsm 0).continuousOn).div continuousOn_id (fun x hx => ne_of_gt hx)
  have hgcont : ContinuousAt g z := hgcontOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hgmeas : StronglyMeasurableAtFilter g (𝓝 z) MeasureTheory.volume :=
    hgcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  have hInt0 : MeasureTheory.IntegrableOn g (Set.Ioi 0) := hFint
  have hInt : IntervalIntegrable g MeasureTheory.volume 0 z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le]
    exact hInt0.mono_set (fun x hx => hx.1)
  -- fundamental theorem of calculus for the interval integral `u ↦ ∫_0^u g`
  have hFTC : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, g r) (g z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hgmeas hgcont
  have hC : HasDerivAt (fun u => (∫ r in Set.Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..u, g r)
      (-(g z)) z := by
    have h := hFTC.const_sub (∫ r in Set.Ioi (0 : ℝ), g r)
    simpa using h
  -- on `(0,∞)` (a neighbourhood of `z`), `∫_u^∞ g = ∫_0^∞ g - ∫_0^u g`
  have heq : (fun u => ∫ r in Set.Ioi u, g r)
      =ᶠ[𝓝 z] (fun u => (∫ r in Set.Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..u, g r) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    have hIntu : MeasureTheory.IntegrableOn g (Set.Ioi u) :=
      hInt0.mono_set (Set.Ioi_subset_Ioi hu.le)
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (f := g) (a := (0 : ℝ)) (b := u) hInt0 hIntu
    linarith [h]
  have hcore : HasDerivAt (fun u => ∫ r in Set.Ioi u, g r) (-(g z)) z :=
    hC.congr_of_eventuallyEq heq
  -- `L12rad F u = ∫_u^∞ F_*(r)/r dr` is literally this function
  have hrad : HasDerivAt (Work.Elliptic.L12rad F) (-(Work.Elliptic.Fstar F z / z)) z := by
    rw [hg] at hcore
    exact hcore
  have h3 : HasDerivAt (fun u => 3 * Work.Elliptic.L12rad F u)
      (3 * (-(Work.Elliptic.Fstar F z / z))) z :=
    hrad.const_mul 3
  have hL12eq : Work.Elliptic.L12 F = fun u => 3 * Work.Elliptic.L12rad F u :=
    funext (Work.Elliptic.L12_eq_radial F)
  rw [hL12eq]
  exact h3.congr_deriv (by ring)

end Work.FTS.EllipticEst
