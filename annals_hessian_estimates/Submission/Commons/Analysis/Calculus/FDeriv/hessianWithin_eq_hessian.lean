import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.InnerProductSpace.Dual

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology in
theorem hessianWithin_eq_hessian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {s : Set E} {u : E → ℝ} {x : E} (hx : s ∈ 𝓝 x) :
    InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ u s) s x) =
      InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x) := by
  -- `s` is a neighbourhood of every point of `interior s`, hence of every point near `x`.
  have hm : ∀ᶠ y in 𝓝 x, s ∈ 𝓝 y := by
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hx)] with y hy
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
  -- Near `x`, the derivative within `s` agrees with the full derivative.
  have hderiv : fderivWithin ℝ u s =ᶠ[𝓝 x] fderiv ℝ u := by
    filter_upwards [hm] with y hy
    exact fderivWithin_of_mem_nhds hy
  -- Hence the second derivatives coincide.
  have hsecond : fderivWithin ℝ (fderivWithin ℝ u s) s x = fderiv ℝ (fderiv ℝ u) x := by
    rw [hderiv.fderivWithin_eq_of_nhds, fderivWithin_of_mem_nhds hx]
  exact congrArg InnerProductSpace.continuousLinearMapOfBilin hsecond

end Commons.Analysis.Calculus.FDeriv