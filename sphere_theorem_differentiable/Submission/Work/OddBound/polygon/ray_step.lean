import Mathlib
import Submission.Work.OddBound.polygon.segmentDomain_endpoint_revVelocity

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygon

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

/-- **The two rays through the endpoints of a short geodesic coincide.**

Let `y = GExp x u` be a point of the ray of `x` with `u ≠ 0`, with `‖u‖ < R` and with the
exponential map at `y` injective on the ball of radius `R`.  If `v` is a vector at `y` with
`GExp y (-v) = x` and `‖v‖ = ‖u‖`, then `v` is exactly the velocity of the ray of `u` at time one,
scaled by `‖u‖`; consequently the ray of `u` from `x` and the ray of `v` from `y` are the same
geodesic, run in opposite directions:

`GExp x (s • u) = GExp y ((s - 1) • v)` for all `s`.

The proof: `u = ‖u‖ • ξ` with `ξ` the unit vector in the direction of `u`, and `w` the velocity of
the unit ray `s ↦ GExp x (s • ξ)` at time `‖u‖`.  The reversal identity
(`GExp_neg_velocity_of_ray_all`) shows `GExp y (‖u‖ • (-w)) = x`, and `‖‖u‖ • (-w)‖ = ‖u‖ < R`;
since also `GExp y (-v) = x` and `‖-v‖ = ‖u‖ < R`, injectivity of `GExp y` on the ball of radius `R`
forces `-v = ‖u‖ • (-w)`, i.e. `v = ‖u‖ • w`.  Translating the reversal identity by the parameter
`(1 - s) ‖u‖` then gives the claim for every real `s` (in particular on `[1, T + 1]`). -/
theorem ray_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y : M} {u : TangentSpace I x} {v : TangentSpace I y} {R T : ℝ}
    (hu : u ≠ 0) (hxy : Submission.GlobalExp.GExp (cov := cov) hmet x u = y)
    (hR : ‖u‖ < R)
    (hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet y R)
    (hyx : Submission.GlobalExp.GExp (cov := cov) hmet y (-v) = x)
    (hvn : ‖v‖ = ‖u‖) (hT : 0 ≤ T) :
    ∀ s ∈ Set.Icc (1:ℝ) (T + 1),
      Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)
        = Submission.GlobalExp.GExp (cov := cov) hmet y ((s - 1) • v) := by
  classical
  -- the length `m = ‖u‖` and the unit direction `ξ = u/‖u‖` of the first ray
  have hmn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set m : ℝ := ‖u‖ with hmdef
  set ξ : TangentSpace I x := Submission.GlobalExp.unitOf u hu with hξdef
  have hξn : ‖ξ‖ = 1 := Submission.GlobalExp.unitOf_norm u hu
  have huξ : u = m • ξ := by
    rw [hξdef, hmdef, Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
  have hym : Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ) = y := by
    rw [← huξ]; exact hxy
  -- move the base point to the endpoint of the ray, so that the velocity below lives at `y`
  subst hym
  -- the velocity of the unit ray at time `m` (a unit vector at `y`)
  set w := Submission.Geodesic.curveVelocity (I := I)
    (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m with hwdef
  have hw1 : ‖w‖ = 1 := norm_curveVelocity_GExp_ray_eq_one (cov := cov) hmet hξn hmn
  -- the reversed ray from `y` returns to `x` after time `m`
  have hback : Submission.GlobalExp.GExp (cov := cov) hmet
      (Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ)) (m • (-w)) = x := by
    have h := GExp_neg_velocity_of_ray_all (cov := cov) hmet htor hξn hmn m
    rw [show m - m = 0 from by ring, zero_smul, Submission.GlobalExp.GExp_zero] at h
    exact h
  -- both `-v` and `m • (-w)` are short and exponentiate to `x`, so they are equal
  have hnv : ‖(-v)‖ < R := by
    rw [Submission.InjRadiusCut.norm_neg_tangent, hvn]; exact hR
  have hnw : ‖m • (-w)‖ < R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmn,
      Submission.InjRadiusCut.norm_neg_tangent, hw1, mul_one]
    exact hR
  have hneg : -v = m • (-w) :=
    hinj (-v) (m • (-w)) hnv hnw (by rw [hyx, hback])
  have hvw : v = m • w := by
    have h := congrArg Neg.neg hneg
    simp only [neg_neg, smul_neg] at h
    exact h
  -- the reversal identity, translated to any parameter
  intro s _
  have key := GExp_neg_velocity_of_ray_all (cov := cov) hmet htor hξn hmn (m - s * m)
  calc Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)
      = Submission.GlobalExp.GExp (cov := cov) hmet x ((s * m) • ξ) := by rw [huξ, smul_smul]
    _ = Submission.GlobalExp.GExp (cov := cov) hmet x ((m - (m - s * m)) • ξ) := by
          rw [show m - (m - s * m) = s * m from by ring]
    _ = Submission.GlobalExp.GExp (cov := cov) hmet
          (Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ)) ((m - s * m) • (-w)) :=
          key.symm
    _ = Submission.GlobalExp.GExp (cov := cov) hmet
          (Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ)) (((s - 1) * m) • w) := by
          rw [show m - s * m = -((s - 1) * m) from by ring, neg_smul, smul_neg, neg_neg]
    _ = Submission.GlobalExp.GExp (cov := cov) hmet
          (Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ)) ((s - 1) • v) := by
          rw [hvw, smul_smul]

end Work.OddBound.polygon
