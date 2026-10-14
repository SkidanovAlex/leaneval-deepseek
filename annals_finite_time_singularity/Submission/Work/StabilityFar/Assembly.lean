import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.StabilityFar.FarDerivLipschitz
import Submission.Work.StabilityFar.St4
import Submission.Work.StabilityFar.St4Refine
import Submission.Work.StabilityFar.St5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar


/-- **The input package of the assembly.**  Every field is a precisely named statement about the
constructed solution; `NOTES.md` records, for each, which area delivers it. -/
structure AssemblyInputs (α : NNReal) where
  /-- the maximal time `T*` of the constructed solution -/
  T : ℝ
  /-- `T* > 0` -/
  hT : 0 < T
  /-- the support radius of the vorticity -/
  R : ℝ
  /-- `R > 0` -/
  hR : 0 < R
  /-- the `L^∞` bound for `ω` -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the `L^∞` bound for `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the time-Hölder constant of `ω` on the support ball -/
  H : ℝ
  /-- `H ≥ 0` -/
  hH : 0 ≤ H
  /-- the time-Hölder constant of `∂ₜω` on the support ball -/
  H₁ : ℝ
  /-- `H₁ ≥ 0` -/
  hH₁ : 0 ≤ H₁
  /-- the constant of the `St5` lower bound for the vorticity sup-norm -/
  c : ℝ
  /-- `c > 0` -/
  hc : 0 < c
  /-- the initial datum -/
  u₀ : R3 → R3
  /-- the pressure -/
  p : R3 → ℝ → ℝ
  /-- the velocity -/
  u : R3 → ℝ → R3
  /-- the vorticity -/
  ω : R3 → ℝ → R3
  /-- the datum is divergence-free -/
  div_u₀ : div u₀ = 0
  /-- the datum is odd -/
  odd_u₀ : IsOdd u₀
  /-- the datum is `C^{1,α}` -/
  cdh_u₀ : IsContDiffHolder ℝ α u₀
  /-- the vorticity of the datum decays like `‖x‖^{-α}` -/
  vortDecay_u₀ : ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)
  /-- `(p,u)` solves the Euler equation on `[0,T*)` -/
  sol : IsLocalEulerEquationSolution p u₀ T u
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Set.Ico 0 T, IsOdd (u · t)
  /-- the solution is `C¹` near the (two-sided) window — from the construction -/
  smooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo (-1) (T + 1))
  /-- **the core regularity** of the construction (`St0`–`St3`): joint `C^{1,α}` on the ball of
  radius `2R+6` (the far-field argument supplies everything outside `2R+5`) -/
  core : ∀ S ∈ Set.Ioo 0 T,
    IsContDiffHolderOn ℝ α u.uncurry (coreRegion (st4Radius R + 1) ×ˢ Set.Icc 0 S)
  /-- `u(·,t) = BS(ω(·,t))` -/
  bsSlice : IsBiotSavartSlice u ω T
  /-- `∂ₜu(·,t) = BS(∂ₜω(·,t))` (differentiation under the Biot–Savart integral) -/
  bsTimeSlice : IsTimeBiotSavartSlice u ω T
  /-- the vorticity is supported in `B(0,R)` -/
  supp : SlicesSupported ω R T
  /-- the vorticity is bounded by `M` -/
  bdd : SlicesBounded ω M T
  /-- `∂ₜω` is bounded by `M₁` -/
  bddDt : SlicesBounded (timeDeriv ω) M₁ T
  /-- `ω` is measurable slicewise -/
  meas : SlicesMeasurable ω T
  /-- `∂ₜω` is measurable slicewise -/
  measDt : SlicesMeasurable (timeDeriv ω) T
  /-- `ω` is `α`-Hölder in time on the support ball -/
  th : TimeHolderOnBall (α : ℝ) ω R T H
  /-- `∂ₜω` is `α`-Hölder in time on the support ball -/
  thDt : TimeHolderOnBall (α : ℝ) (timeDeriv ω) R T H₁
  /-- **`St5`'s input**: `‖ω(·,t)‖_∞ ≥ c/(T*-t)` -/
  linfLower : VortLinfLower u T c
  /-- the interval-integrability needed by the BKM comparison -/
  bkmIntegrable : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t

variable {α : NNReal}






end Work.StabilityFar
