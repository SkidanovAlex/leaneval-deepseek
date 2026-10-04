import Mathlib
import Submission.Work.Diff.GE.Gest.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Submission.Diff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Product rule for `mvfderiv` of a pointwise product of two smooth real functions:
`d(uv) Z = u · d v Z + v · d u Z` at every point.  This is the manifold form of the Leibniz
rule, obtained from Mathlib's `mvfderiv_mul` (which is stated for continuous linear maps) by
evaluating at `Z`. -/
theorem mvfderiv_mul_apply (u v : M → ℝ) (hu : CMDiff ∞ u) (hv : CMDiff ∞ v)
    (y : M) (Z : TangentSpace I y) :
    mvfderiv I (fun z => u z * v z) y Z
      = u y * mvfderiv I v y Z + v y * mvfderiv I u y Z := by
  have hy1 : MDiffAt u y := hu.contMDiffAt.mdifferentiableAt (by simp)
  have hy2 : MDiffAt v y := hv.contMDiffAt.mdifferentiableAt (by simp)
  have h := mvfderiv_mul (I := I) (M := M) hy1 hy2
  have h2 := congrArg (fun (L : TangentSpace I y →L[ℝ] ℝ) => L Z) h
  change ((d% (u * v) : M → TangentSpace I y →L[ℝ] ℝ) y) Z = _
  simpa [smul_apply, smul_eq_mul] using h2

/-- Product rule for the Hessian-type second derivative along a smooth field `W`:
`W(W(uv)) - (∇_W W)(uv) = u·(W W v - (∇_W W)v) + v·(W W u - (∇_W W)u) + 2 (Wu)(Wv)`,
where `W f` denotes `mvfderiv I f y (W y)`. -/
theorem hess_mul_field
    (g : SMet I M) (u v : M → ℝ) (hu : CMDiff ∞ u) (hv : CMDiff ∞ v)
    (W : Π y : M, TangentSpace I y) (hW : CMDiff ∞ (T% W)) (x : M) :
    (mvfderiv I (fun y => mvfderiv I (fun y => u y * v y) y (W y)) x (W x)
        - mvfderiv I (fun y => u y * v y) x (lcOf g W x (W x)))
      = u x * (mvfderiv I (fun y => mvfderiv I v y (W y)) x (W x)
          - mvfderiv I v x (lcOf g W x (W x)))
        + v x * (mvfderiv I (fun y => mvfderiv I u y (W y)) x (W x)
          - mvfderiv I u x (lcOf g W x (W x)))
        + 2 * mvfderiv I u x (W x) * mvfderiv I v x (W x) := by
  set Z : TangentSpace I x := lcOf g W x (W x)
  -- differentiability at `x` of the functions involved
  have huD : MDiffAt u x := hu.contMDiffAt.mdifferentiableAt (by simp)
  have hvD : MDiffAt v x := hv.contMDiffAt.mdifferentiableAt (by simp)
  have huW : CMDiff ∞ (fun y => mvfderiv I u y (W y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hu hW
  have hvW : CMDiff ∞ (fun y => mvfderiv I v y (W y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hv hW
  have huWD : MDiffAt (fun y => mvfderiv I u y (W y)) x :=
    huW.contMDiffAt.mdifferentiableAt (by simp)
  have hvWD : MDiffAt (fun y => mvfderiv I v y (W y)) x :=
    hvW.contMDiffAt.mdifferentiableAt (by simp)
  have hB : MDiffAt (fun y => u y * mvfderiv I v y (W y)) x := huD.mul hvWD
  have hC : MDiffAt (fun y => v y * mvfderiv I u y (W y)) x := hvD.mul huWD
  -- the Leibniz rule for `uv`, pointwise, rewritten as an equality of functions
  have hpt : ∀ y : M, mvfderiv I (fun z => u z * v z) y (W y)
      = u y * mvfderiv I v y (W y) + v y * mvfderiv I u y (W y) :=
    fun y => mvfderiv_mul_apply u v hu hv y (W y)
  have hA : (fun y => mvfderiv I (fun z => u z * v z) y (W y))
      = (fun y => u y * mvfderiv I v y (W y))
        + (fun y => v y * mvfderiv I u y (W y)) := by
    funext y; exact hpt y
  -- the second derivative splits as a sum
  have h1 : mvfderiv I (fun y => mvfderiv I (fun z => u z * v z) y (W y)) x (W x)
      = mvfderiv I (fun y => u y * mvfderiv I v y (W y)) x (W x)
        + mvfderiv I (fun y => v y * mvfderiv I u y (W y)) x (W x) := by
    rw [hA, mvfderiv_add hB hC, add_apply]
  -- Leibniz rule for each of the two summands, at `x` along `W x`
  have hmulB : mvfderiv I (fun y => u y * mvfderiv I v y (W y)) x (W x)
      = u x * mvfderiv I (fun y => mvfderiv I v y (W y)) x (W x)
        + mvfderiv I v x (W x) * mvfderiv I u x (W x) := by
    have h := mvfderiv_mul (I := I) (M := M) huD hvWD
    have h2 := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L (W x)) h
    change ((d% (u * (fun y => mvfderiv I v y (W y))) :
      M → TangentSpace I x →L[ℝ] ℝ) x) (W x) = _
    simpa [smul_apply, smul_eq_mul] using h2
  have hmulC : mvfderiv I (fun y => v y * mvfderiv I u y (W y)) x (W x)
      = v x * mvfderiv I (fun y => mvfderiv I u y (W y)) x (W x)
        + mvfderiv I u x (W x) * mvfderiv I v x (W x) := by
    have h := mvfderiv_mul (I := I) (M := M) hvD huWD
    have h2 := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L (W x)) h
    change ((d% (v * (fun y => mvfderiv I u y (W y))) :
      M → TangentSpace I x →L[ℝ] ℝ) x) (W x) = _
    simpa [smul_apply, smul_eq_mul] using h2
  -- the first order term `d(uv)(Z)`
  have hfirst : mvfderiv I (fun y => u y * v y) x Z
      = u x * mvfderiv I v x Z + v x * mvfderiv I u x Z :=
    mvfderiv_mul_apply u v hu hv x Z
  rw [h1, hmulB, hmulC, hfirst]
  ring

end Work.Diff.GE.Gest
