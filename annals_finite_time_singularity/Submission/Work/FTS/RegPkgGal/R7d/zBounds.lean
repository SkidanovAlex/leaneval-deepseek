import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

/-- Two-sided bounds for the solution of the linear ODE `z' = -(z · V)` on `[0,T]`, where
`0 ≤ V ≤ a` and `z ≥ 0` on the open interval.

* the **upper** bound `z x ≤ z₀` is simply the antitonicity of `z`: `z' = -z·V ≤ 0`;
* the **lower** bound `z₀·exp (-(a·x)) ≤ z x` is the integrating-factor argument for
  `u x = z x · exp (a·x)`: `u' = z·(a - V)·exp (a·x) ≥ 0`, so `u` is monotone and
  `z₀ = u 0 ≤ u x = z x · exp (a·x)`.

The degenerate case `T ≤ 0` gives `Set.Icc 0 T = ∅` (or `{0}` when `T = 0`). -/
theorem zBounds {z V : ℝ → ℝ} {a z₀ T : ℝ} (hzc : ContinuousOn z (Set.Icc 0 T)) (hz0 : z 0 = z₀) (hderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt z (-(z x * V x)) x) (hV0 : ∀ x ∈ Set.Ioo 0 T, 0 ≤ V x) (hVa : ∀ x ∈ Set.Ioo 0 T, V x ≤ a) (hzpos : ∀ x ∈ Set.Ioo 0 T, 0 ≤ z x) : ∀ x ∈ Set.Icc 0 T, z₀ * Real.exp (-(a * x)) ≤ z x ∧ z x ≤ z₀ := by
  rcases le_or_gt T 0 with hTle | hT
  · -- degenerate case: `x ∈ Set.Icc 0 T` forces `x = 0` and `T = 0`
    intro x hx
    have hx0 : x = 0 := le_antisymm (le_trans hx.2 hTle) hx.1
    rw [hx0, hz0]
    constructor <;> simp
  · have hD : Convex ℝ (Set.Icc 0 T) := convex_Icc 0 T
    have hIcc : interior (Set.Icc 0 T) = Set.Ioo 0 T := interior_Icc
    have h0D : (0:ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hT.le⟩
    -- the integrating factor `u x = z x · exp (a·x)` and its derivative
    have hlin : ContinuousOn (fun x : ℝ => a * x) (Set.Icc 0 T) :=
      continuousOn_const.mul continuousOn_id
    have hexp_cont : ContinuousOn (fun x : ℝ => Real.exp (a * x)) (Set.Icc 0 T) :=
      Real.continuous_exp.comp_continuousOn hlin
    have hu_cont : ContinuousOn (fun x : ℝ => z x * Real.exp (a * x)) (Set.Icc 0 T) :=
      hzc.mul hexp_cont
    have hu_deriv : ∀ x ∈ interior (Set.Icc 0 T),
        HasDerivWithinAt (fun y : ℝ => z y * Real.exp (a * y))
          ((z x * (a - V x)) * Real.exp (a * x)) (interior (Set.Icc 0 T)) x := by
      intro x hx
      rw [hIcc] at hx ⊢
      have hz' : HasDerivAt z (-(z x * V x)) x := hderiv x hx
      have hlin' : HasDerivAt (fun y : ℝ => a * y) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      have hexp' : HasDerivAt (fun y : ℝ => Real.exp (a * y)) (Real.exp (a * x) * a) x :=
        hlin'.exp
      have hprod := hz'.mul hexp'
      have hval : -(z x * V x) * Real.exp (a * x) + z x * (Real.exp (a * x) * a)
          = (z x * (a - V x)) * Real.exp (a * x) := by ring
      exact (hprod.congr_deriv hval).hasDerivWithinAt
    have hu_nn : ∀ x ∈ interior (Set.Icc 0 T), 0 ≤ (z x * (a - V x)) * Real.exp (a * x) := by
      intro x hx
      rw [hIcc] at hx
      exact mul_nonneg (mul_nonneg (hzpos x hx) (sub_nonneg.mpr (hVa x hx))) (Real.exp_pos _).le
    have hu_mono : MonotoneOn (fun y : ℝ => z y * Real.exp (a * y)) (Set.Icc 0 T) :=
      monotoneOn_of_hasDerivWithinAt_nonneg hD hu_cont hu_deriv hu_nn
    -- antitonicity of `z` itself
    have hz_deriv : ∀ x ∈ interior (Set.Icc 0 T),
        HasDerivWithinAt z (-(z x * V x)) (interior (Set.Icc 0 T)) x := by
      intro x hx
      rw [hIcc] at hx ⊢
      exact (hderiv x hx).hasDerivWithinAt
    have hz_np : ∀ x ∈ interior (Set.Icc 0 T), -(z x * V x) ≤ 0 := by
      intro x hx
      rw [hIcc] at hx
      have := mul_nonneg (hzpos x hx) (hV0 x hx)
      linarith
    have hz_anti : AntitoneOn z (Set.Icc 0 T) :=
      antitoneOn_of_hasDerivWithinAt_nonpos hD hzc hz_deriv hz_np
    intro x hx
    constructor
    · -- lower bound from the monotonicity of the integrating factor
      have hle := hu_mono h0D hx hx.1
      change z 0 * Real.exp (a * 0) ≤ z x * Real.exp (a * x) at hle
      rw [hz0, mul_zero, Real.exp_zero, mul_one] at hle
      have hgoal : z₀ * Real.exp (-(a * x)) = z₀ / Real.exp (a * x) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      rw [hgoal]
      exact (div_le_iff₀ (Real.exp_pos _)).mpr hle
    · -- upper bound
      have hle := hz_anti h0D hx hx.1
      rw [hz0] at hle
      exact hle

end Work.FTS.RegPkgGal.R7d
