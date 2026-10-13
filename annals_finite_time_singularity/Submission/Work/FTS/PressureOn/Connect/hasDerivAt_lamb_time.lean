/-
# `Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time`

The Lamb vector `lamb u ω x t = u x t × ω x t` is differentiable in the time variable `t`
whenever `u (·,·)` and `ω (·,·)` are, and its `t`-derivative is the product rule

  `∂ₜ(u × ω) = (∂ₜu) × ω + u × (∂ₜω)`.

Since the requested statement asks for the derivative to be the *canonical* one,
`timeDeriv (lamb u ω) y t = deriv (fun s => lamb u ω y s) t` (this is the definition of
`timeDeriv`, up to `β`-reduction), it is enough to establish *differentiability* of the time
slice `s ↦ lamb u ω y s`, which we then feed into `DifferentiableAt.hasDerivAt`.

The differentiability is the classical product rule for a bilinear map: the cross product of `ℝ³`
is realised as a continuous bilinear map `Work.FTS.BSSwirl.crossBilin` (from
`Submission.Work.FTS.BSSwirl.CrossAux`), whose Fréchet derivative is itself
(`ContinuousLinearMap.hasFDerivAt`); composing the first factor and applying
`HasFDerivAt.clm_apply` to the second gives the claim.  The final step rewrites the two
`HasDerivAt` hypotheses into `HasFDerivAt` via `HasDerivAt.hasFDerivAt`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.BSSwirl.CrossAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

/-- **The time derivative of the Lamb vector.**  If the time slices `s ↦ u y s` and `s ↦ ω y s` are
differentiable at `t`, then so is the time slice of the Lamb vector `s ↦ u y s × ω y s`, with
derivative its canonical `deriv` — i.e. `timeDeriv (lamb u ω) y t`. -/
theorem hasDerivAt_lamb_time {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {t : ℝ}
    (hu : HasDerivAt (fun s => u y s) (FiniteTimeSingularity.timeDeriv u y t) t)
    (hω : HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t) :
    HasDerivAt (fun s => Work.FTS.PressureOn.lamb u ω y s)
      (FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.lamb u ω) y t) t := by
  -- `lamb u ω y s` is the cross product `u y s × ω y s` (definitionally).
  have hfeq : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  -- The cross product, as a continuous bilinear map, is its own derivative; compose the first
  -- factor with the curve `s ↦ u y s`.
  have hc : HasFDerivAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      (Work.FTS.BSSwirl.crossBilin.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (FiniteTimeSingularity.timeDeriv u y t))) t :=
    Work.FTS.BSSwirl.crossBilin.hasFDerivAt.comp t hu.hasFDerivAt
  -- Apply the second factor (`HasFDerivAt.clm_apply`: product rule for a bilinear map).
  have hmain := hc.clm_apply hω.hasFDerivAt
  -- Only differentiability is needed: the requested derivative is the canonical `deriv`.
  have hdiff : DifferentiableAt ℝ (fun s => Work.FTS.PressureOn.lamb u ω y s) t := by
    rw [← hfeq]
    exact hmain.differentiableAt
  exact hdiff.hasDerivAt

/-- **The value of the time derivative of the Lamb vector** (the explicit product rule).  This is
the companion of `hasDerivAt_lamb_time`: it identifies the derivative that the latter only names
as `timeDeriv (lamb u ω) y t`. -/
theorem timeDeriv_lamb {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {t : ℝ}
    (hu : HasDerivAt (fun s => u y s) (FiniteTimeSingularity.timeDeriv u y t) t)
    (hω : HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t) :
    FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.lamb u ω) y t
      = Work.FTS.PressureOn.crossVec (FiniteTimeSingularity.timeDeriv u y t) (ω y t)
        + Work.FTS.PressureOn.crossVec (u y t) (FiniteTimeSingularity.timeDeriv ω y t) := by
  have hfeq : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  have hc : HasFDerivAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      (Work.FTS.BSSwirl.crossBilin.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (FiniteTimeSingularity.timeDeriv u y t))) t :=
    Work.FTS.BSSwirl.crossBilin.hasFDerivAt.comp t hu.hasFDerivAt
  have hmain := hc.clm_apply hω.hasFDerivAt
  -- `deriv` of a differentiable function is the value of its Fréchet derivative at `1`.
  rw [show FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.lamb u ω) y t
      = deriv (fun s => Work.FTS.PressureOn.lamb u ω y s) t from rfl]
  rw [← hfeq, hmain.hasDerivAt.deriv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [add_comm]
  rfl

end Work.FTS.PressureOn.Connect
