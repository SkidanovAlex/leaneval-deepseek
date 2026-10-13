/-
# `Work.FTS.BSSwirl.contDiff_div_and_support`

The divergence `div Ψ x = trace (fderiv ℝ Ψ x)` of a compactly supported smooth vector field
`Ψ : ℝ³ → ℝ³` is again smooth and compactly supported.  This is the regularity/support input for
the divergence half of the Biot–Savart law of the `BSSwirl` area (item 7a of
`FTS_PHYS_BRIDGE.md` §1): together with its curl twin `contDiff_vorticity_and_support` it shows
that the fields appearing in `∇ × (BS ω) = ω`, `div (BS ω) = 0` have the required regularity.

The two ingredients:

* `div` is the trace of the Fréchet derivative, and the trace is a *continuous* linear functional
  `divTrCLM` on `ℝ³ →L[ℝ] ℝ³`; composing a `C^n` map with a continuous linear map preserves `C^n`,
  and `fderiv` loses one order of differentiability (`ContDiff.fderiv_right`).
* A point outside the topological support `tsupport Ψ` has a neighbourhood on which `Ψ` vanishes
  identically, so the derivative vanishes there as well; hence
  `support (div Ψ) ⊆ tsupport Ψ` and compactness of `tsupport Ψ` passes to `div Ψ`
  (`HasCompactSupport.mono'`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- The trace as a linear functional on the endomorphisms of `ℝ³`, i.e. the linear map
`A ↦ trace A` underlying `FiniteTimeSingularity.div`. -/
noncomputable def divTrLin : (R3 →L[ℝ] R3) →ₗ[ℝ] ℝ :=
  (LinearMap.trace ℝ R3).comp (ContinuousLinearMap.coeLM ℝ)

/-- **The trace as a continuous linear functional on `ℝ³ →L[ℝ] ℝ³`.**  The space `ℝ³ →L[ℝ] ℝ³` is
finite-dimensional, so every linear functional on it is continuous. -/
noncomputable def divTrCLM : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap divTrLin

/-- The defining value of `divTrCLM`: it is the trace. -/
theorem divTrCLM_apply (A : R3 →L[ℝ] R3) : divTrCLM A = A.trace ℝ R3 := rfl

/-- `div` is the continuous linear functional `divTrCLM` applied to the derivative. -/
theorem div_eq_divTrCLM (Ψ : R3 → R3) (x : R3) :
    FiniteTimeSingularity.div Ψ x = divTrCLM (fderiv ℝ Ψ x) := rfl

/-- **The derivative vanishes off the (topological) support.**  If `x` is outside `tsupport Ψ` then
`Ψ` vanishes on a whole neighbourhood of `x`, hence is differentiable there with derivative `0`. -/
theorem fderiv_eq_zero_of_notMem_tsupport {Ψ : R3 → R3} {x : R3} (hx : x ∉ tsupport Ψ) :
    fderiv ℝ Ψ x = 0 := by
  have hmem : (tsupport Ψ)ᶜ ∈ 𝓝 x := (isClosed_tsupport Ψ).isOpen_compl.mem_nhds hx
  have hev : Ψ =ᶠ[𝓝 x] fun _ : R3 => 0 := by
    filter_upwards [hmem] with y hy
    by_contra h
    exact hy (subset_tsupport Ψ (Function.mem_support.mpr h))
  rw [hev.fderiv_eq, fderiv_const_apply (0 : R3)]

theorem contDiff_div_and_support {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hc : HasCompactSupport Ψ) :
    (∀ n : ℕ, ContDiff ℝ n (fun x => FiniteTimeSingularity.div Ψ x)) ∧
      HasCompactSupport (fun x => FiniteTimeSingularity.div Ψ x) := by
  have hdiv : (fun x => FiniteTimeSingularity.div Ψ x)
      = fun x => divTrCLM (fderiv ℝ Ψ x) := by
    funext x
    exact div_eq_divTrCLM Ψ x
  constructor
  · intro n
    rw [hdiv]
    have hf : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ Ψ) :=
      (hΨ (n + 1)).fderiv_right (by simp)
    exact (ContinuousLinearMap.contDiff divTrCLM).comp hf
  · rw [hdiv]
    refine hc.mono' ?_
    intro x hx
    by_contra hx'
    exact (Function.mem_support.mp hx) (by rw [fderiv_eq_zero_of_notMem_tsupport hx']; simp)

end

end Work.FTS.BSSwirl
