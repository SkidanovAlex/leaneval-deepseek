import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The right tail of the truncation integral vanishes

`Work.FTS.EllSol.ShiftFT.Gc N b u t θ = chi N t * u t θ
 + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`; the integral is the primitive of the
truncation error.  Here we record the elementary fact that for `2N ≤ t` this integral
vanishes: the integrand carries the factor `deriv (chi N) s`, and `chi N s = tk (s/N)`
is identically `0` for `2N < |s|`, so its derivative vanishes on the (strict) window
`(2N, ∞)`; the interval `t..(2N)` therefore consists entirely of such points (it is a
subset of `Ioc (2N) t`, on which `2N < s` strictly).
-/

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- Off the strict window `|s| ≤ 2N` the cutoff `chi N` is locally constant `0`, hence its
derivative vanishes: `deriv (chi N) s = 0` for `2N < s`. -/
theorem deriv_chi_eq_zero_of_two_mul_lt {N s : ℝ} (hN : 0 < N) (hs : 2 * N < s) :
    deriv (Work.FTS.EllSol.Trunc.chi N) s = 0 := by
  have hmem : s ∈ {x : ℝ | 2 * N < |x|} := by
    show 2 * N < |s|
    rw [abs_of_pos (by linarith)]
    exact hs
  have hopen : IsOpen {x : ℝ | 2 * N < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : Work.FTS.EllSol.Trunc.chi N =ᶠ[𝓝 s] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hmem] with x hx
    exact Work.FTS.EllSol.Trunc.chi_eq_zero hN (le_of_lt hx)
  rw [hev.deriv_eq, deriv_const]

set_option linter.unusedVariables false in
theorem gcIntTailZero (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ, 2 * N ≤ t →
      (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) = 0 := by
  intro θ hθ t ht
  -- on `(2N, t]` the factor `deriv (chi N)` vanishes, so the whole integrand is `0`
  have hzero : ∀ s ∈ Set.Ioc (2 * N) t,
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ = 0 := by
    intro s hs
    rw [deriv_chi_eq_zero_of_two_mul_lt hN hs.1]
    ring
  rw [intervalIntegral.integral_of_ge ht,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hzero]
  simp

end

end Work.FTS.EllSol.ShiftFT.Aux2
