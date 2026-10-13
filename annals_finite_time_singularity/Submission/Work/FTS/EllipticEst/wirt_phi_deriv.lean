import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst

/-- Elementary product/chain-rule computation: for `u` differentiable at `x` with
`sin (r * (x - a)) ≠ 0`,

`d/dy [ r * u y ^ 2 * (cos (r * (y-a)) / sin (r * (y-a))) ] (x)`
`  = (deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2`
`      - ((deriv u x * sin (r * (x-a)) - u x * (r * cos (r * (x-a)))) / sin (r * (x-a))) ^ 2`.

This is the Wirtinger-type identity for the function `φ(y) = ln (tan (r (y-a))) '`-weighted
`u ^ 2`; it is a purely pointwise identity in `u x`, `deriv u x` and the trigonometric
values at `x`. -/
theorem wirt_phi_deriv {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) :
    ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y => r * (u y) ^ 2 * (Real.cos (r * (y - a)) / Real.sin (r * (y - a))))
        ((deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2
          - ((deriv u x * Real.sin (r * (x - a)) - u x * (r * Real.cos (r * (x - a))))
              / Real.sin (r * (x - a))) ^ 2) x := by
  intro x hx
  -- `x` lies in the interior of `Icc a b`, hence `u` is differentiable there
  have hxint : x ∈ interior (Set.Icc a b) := by
    rw [interior_Icc]; exact hx
  have hns : Set.Icc a b ∈ nhds x := mem_interior_iff_mem_nhds.mp hxint
  have hdiff : DifferentiableAt ℝ u x :=
    (hu.differentiableOn (by decide)).differentiableAt hns
  have hd : HasDerivAt u (deriv u x) x := hdiff.hasDerivAt
  -- `sin (r (x - a))` is positive on the open interval, since `0 < r (x-a) < π`
  have hsin_pos : 0 < Real.sin (r * (x - a)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hr (sub_pos.mpr hx.1)
    · calc r * (x - a) < r * (b - a) :=
            mul_lt_mul_of_pos_left (by linarith [hx.2]) hr
        _ = π := hrb
  have hsin_ne : Real.sin (r * (x - a)) ≠ 0 := ne_of_gt hsin_pos
  -- the chain rule for the trigonometric factors
  have hlin : HasDerivAt (fun y : ℝ => r * (y - a)) r x := by
    simpa using (((hasDerivAt_id x).sub_const a).const_mul r)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (r * (y - a))) (-Real.sin (r * (x - a)) * r) x :=
    hlin.cos
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (r * (y - a))) (Real.cos (r * (x - a)) * r) x :=
    hlin.sin
  have hquot : HasDerivAt (fun y : ℝ => Real.cos (r * (y - a)) / Real.sin (r * (y - a)))
      ((-Real.sin (r * (x - a)) * r * Real.sin (r * (x - a))
          - Real.cos (r * (x - a)) * (Real.cos (r * (x - a)) * r))
        / Real.sin (r * (x - a)) ^ 2) x :=
    hcos.div hsin hsin_ne
  have hsq : HasDerivAt (fun y : ℝ => (u y) ^ 2) (2 * u x ^ (2 - 1) * deriv u x) x := hd.pow 2
  have hmain : HasDerivAt
      (fun y : ℝ => r * (u y) ^ 2 * (Real.cos (r * (y - a)) / Real.sin (r * (y - a))))
      ((r * (2 * u x ^ (2 - 1) * deriv u x)) * (Real.cos (r * (x - a)) / Real.sin (r * (x - a)))
        + (r * u x ^ 2) * ((-Real.sin (r * (x - a)) * r * Real.sin (r * (x - a))
            - Real.cos (r * (x - a)) * (Real.cos (r * (x - a)) * r))
          / Real.sin (r * (x - a)) ^ 2)) x := by
    have h2 := (hsq.const_mul r).mul hquot
    rw [show (fun y : ℝ => r * u y ^ 2 * (Real.cos (r * (y - a)) / Real.sin (r * (y - a))))
        = ((fun y : ℝ => r * u y ^ 2)
            * (fun y : ℝ => Real.cos (r * (y - a)) / Real.sin (r * (y - a)))) from by
      funext y; simp [Pi.mul_apply]]
    exact h2
  -- reduce to the pointwise algebraic identity in `u x`, `deriv u x`, `sin`, `cos`,
  -- which follows from `sin ^ 2 + cos ^ 2 = 1`
  refine hmain.congr_deriv ?_
  field_simp
  ring_nf

end Work.FTS.EllipticEst
