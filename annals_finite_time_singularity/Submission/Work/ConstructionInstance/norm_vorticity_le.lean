/-
# `Work.ConstructionInstance.norm_vorticity_le` — the curl is bounded by `3 ‖Du‖`

`FiniteTimeSingularity.vorticity u x = WithLp.toLp 2 (∑ i, e i ⨯₃ (fderiv ℝ u x (e i)))` is a
fixed bounded linear function of the derivative `Tu := fderiv ℝ u x`: writing the `L²`
Euclidean vector as the sum of the three coordinate cross products, the triangle inequality and
`‖e i × v‖ ≤ ‖e i‖ ‖v‖ = ‖v‖ ≤ ‖Tu‖` give

  `‖vorticity u x‖ ≤ 3 ‖Du x‖`,

the factor `3 = card (Fin 3)` being the price of the three-term curl.  This is the pointwise
estimate behind `Work.LWP.isBoundedFun_vorticity` and `Work.LWP.holder_vorticity` (see the
docstring of `Work.LWP.VorticityAPI`); it is recorded here for the construction instantiation.

Nothing is assumed of `u`: the estimate needs no differentiability hypothesis, since Lean's
`fderiv` is the junk value `0` at the points where `u` is not differentiable, and at such points
`vorticity u x = 0` as well.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.LWP.VorticityAPI

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The standard basis vectors `e i` of `ℝ³` are unit vectors. -/
private lemma norm_e (i : Fin 3) : ‖FiniteTimeSingularity.e i‖ = (1 : ℝ) := by
  simp [FiniteTimeSingularity.e]

/-- The Euclidean norm of a coordinate cross product: `‖a × b‖ ≤ ‖a‖ ‖b‖`.

`crossProduct` (`⨯₃`) is Mathlib's bilinear form on `Fin 3 → ℝ`, and
`InnerProductGeometry.norm_ofLp_crossProduct` computes `‖a × b‖ = ‖a‖ ‖b‖ sin∠(a,b)`. -/
private lemma norm_toLp_cross_le (a b : R3) :
    ‖WithLp.toLp 2 (crossProduct a b)‖ ≤ ‖a‖ * ‖b‖ := by
  rw [InnerProductGeometry.norm_ofLp_crossProduct a b]
  calc ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b)
      ≤ ‖a‖ * ‖b‖ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
    _ = ‖a‖ * ‖b‖ := by ring

theorem norm_vorticity_le (u : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3)
    (x : Work.ConstructionInstance.R3) :
    ‖FiniteTimeSingularity.vorticity u x‖ ≤ 3 * ‖fderiv ℝ u x‖ := by
  -- Bring the `WithLp.toLp` inside the sum, so that the triangle inequality applies termwise.
  have hsplit : FiniteTimeSingularity.vorticity u x
      = ∑ i : Fin 3,
          WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
            (fderiv ℝ u x (FiniteTimeSingularity.e i))) := by
    rw [show FiniteTimeSingularity.vorticity u x
        = WithLp.toLp 2 (∑ i : Fin 3,
            crossProduct (FiniteTimeSingularity.e i)
              (fderiv ℝ u x (FiniteTimeSingularity.e i))) from rfl]
    exact WithLp.toLp_sum 2 (Fin 3 → ℝ) Finset.univ _
  rw [hsplit]
  calc ‖∑ i : Fin 3, WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖
      ≤ ∑ i : Fin 3, ‖WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖ :=
        Finset.sum_le_sum (fun i _ => norm_toLp_cross_le _ _)
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ u x‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u x) (FiniteTimeSingularity.e i)
        rw [norm_e i, mul_one] at h
        calc ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖
            ≤ 1 * (‖fderiv ℝ u x‖ * 1) :=
              mul_le_mul (le_of_eq (norm_e i)) (by simpa using h) (norm_nonneg _) (by norm_num)
          _ = ‖fderiv ℝ u x‖ := by ring
    _ = 3 * ‖fderiv ℝ u x‖ := by simp

end Work.ConstructionInstance
