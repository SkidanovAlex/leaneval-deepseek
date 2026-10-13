import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

/-- **The `z`-difference quotient of an honest pair tends to `z∂_zΨ`.**

For `(F,Ψ)` in the honest class (in particular `Ψ` is `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)`) and every interior point `(z,θ)`, the right-sided difference quotient in the
radial variable converges to the radial partial derivative:

`(Ψ z θ - Ψ (z - hh) θ) / hh → ∂_zΨ (z,θ) = pz Ψ z θ` as `hh → 0⁺`.

This is the differentiability half of the mean-value bound `HonDifQuotBound`.  The only input is
that the `z`-slice `z' ↦ Ψ z' θ` is differentiable at `z`, which is `CurrySmooth`'s
`differentiableAt_curry_left` applied to the `C¹`-smoothness (`h.sm 1`) on the open quadrant,
together with the standard `HasDerivAt`-to-slope limit. -/
theorem HonDifQuotTendsto (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun hh : ℝ => (Ψ z θ - Ψ (z - hh) θ) / hh)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Work.Spaces.pz Ψ z θ)) := by
  intro z hz θ hθ0 hθ1
  -- the open quadrant is a neighbourhood of the interior point `(z,θ)`
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hp : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hz, hθ0, hθ1⟩
  -- the `z`-slice is differentiable at `z`, with derivative `pz Ψ z θ`
  have hd : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      (((h.sm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp))
  have hderiv : HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z := by
    simpa [Work.Spaces.pz] using hd.hasDerivAt
  have hderiv' : HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ z θ) (z - 0) := by
    simpa using hderiv
  -- hence the reflected slice `t ↦ Ψ (z - t) θ` has derivative `-pz Ψ z θ` at `0`
  have h1 : HasDerivAt (fun t : ℝ => z - t) (-1) 0 := by
    simpa [id_eq] using (hasDerivAt_id (0 : ℝ)).const_sub z
  have h2 := hderiv'.comp 0 h1
  have hg : HasDerivAt (fun t : ℝ => Ψ (z - t) θ) (-(Work.Spaces.pz Ψ z θ)) 0 := by
    convert h2 using 1
    · ext t; rfl
    · ring
  -- the slope of the reflected slice tends to `-pz Ψ z θ` from the right
  have hlim := hg.tendsto_slope_zero_right
  -- which, after changing the sign, is exactly the difference quotient of the statement
  have hpt : ∀ t : ℝ,
      -(t⁻¹ • (Ψ (z - (0 + t)) θ - Ψ (z - 0) θ)) = (Ψ z θ - Ψ (z - t) θ) / t := by
    intro t
    simp only [zero_add, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  exact Filter.Tendsto.congr hpt (by simpa only [neg_neg] using hlim.neg)

end Work.FTS.EllipticEst.Honest
