import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.ConstructionInstance.AxiNoSwirlSymm
import Submission.Work.Cyl.norm_angularVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

/-- **The `s`-derivative of the rotation about the `x₃`-axis is the angular vector field.**

Coordinatewise, `rotLE s x` is
`(cos s · x₀ - sin s · x₁, sin s · x₀ + cos s · x₁, x₂)`, whose `s`-derivative at `t` is
`(-sin t · x₀ - cos t · x₁, cos t · x₀ - sin t · x₁, 0)`.  At the rotated point
`y = rotLE t x` the angular vector is
`angularVec y = (-y₁, y₀, 0) = (-(sin t · x₀ + cos t · x₁), cos t · x₀ - sin t · x₁, 0)`,
which is the same vector.  This is the elementary instance of the identity
`d/dt (rotLE t) = J · rotLE t` (`J` = rotation by `π/2` in the `(x₀,x₁)`-plane) used to
transport the Biot–Savart law to the rotating frame. -/
theorem hasDerivAt_rotLE (t : ℝ) (x : Work.FTS.BSSwirl.R3) :
    HasDerivAt (fun s : ℝ => Work.ConstructionInstance.rotLE s x)
      (Work.Cyl.angularVec (Work.ConstructionInstance.rotLE t x)) t := by
  -- The coordinate vector `s ↦ rotCoord s x.ofLp` has the announced derivative componentwise.
  have hF : HasDerivAt (fun s : ℝ => Work.ConstructionInstance.rotCoord s x.ofLp)
      (fun i : Fin 3 =>
        (Work.Cyl.angularVec (Work.ConstructionInstance.rotLE t x)).ofLp i) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · show HasDerivAt (fun s : ℝ => Real.cos s * x.ofLp 0 - Real.sin s * x.ofLp 1)
          (-(Real.sin t * x.ofLp 0 + Real.cos t * x.ofLp 1)) t
      have h1 := (Real.hasDerivAt_cos t).mul_const (x.ofLp 0)
      have h2 := (Real.hasDerivAt_sin t).mul_const (x.ofLp 1)
      convert h1.sub h2 using 1
      ring
    · show HasDerivAt (fun s : ℝ => Real.sin s * x.ofLp 0 + Real.cos s * x.ofLp 1)
          (Real.cos t * x.ofLp 0 - Real.sin t * x.ofLp 1) t
      have h1 := (Real.hasDerivAt_sin t).mul_const (x.ofLp 0)
      have h2 := (Real.hasDerivAt_cos t).mul_const (x.ofLp 1)
      convert h1.add h2 using 1
      ring
    · show HasDerivAt (fun _ : ℝ => x.ofLp 2) 0 t
      exact hasDerivAt_const t (x.ofLp 2)
  -- Push the derivative through `WithLp.toLp` (a continuous linear equivalence).
  have hto := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (E := fun _ : Fin 3 => ℝ)
      (Work.ConstructionInstance.rotCoord t x.ofLp)).comp_hasDerivAt t hF
  simpa [Function.comp_def, Work.ConstructionInstance.rotLE_apply,
    PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp_ofLp] using hto

end Work.FTS.BSSwirl
