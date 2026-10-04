import Mathlib
import Submission.Work.Diff.STE.Lead.coordBound
import Submission.Work.Diff.STE.deTurck.posDef_gmat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart matrix of a positive definite section of bilinear forms is invertible

This file proves `Work.Diff.STE.Lead.det_chartMatOf_ne_zero`: at a point `x` in the source of the
chart at `x₀`, the determinant of the chart matrix

`(Matrix.of (D.chartMatOf h x₀ ((extChartAt I x₀) x)))`

of a section `h` of the bundle of bilinear forms is non-zero, provided `h x` is symmetric and
bounded below by a positive multiple `lam > 0` of a Riemannian metric `g₀`.

The mathematical content is the standard fact that a symmetric positive definite bilinear form has
a non-zero determinant in any basis — here the coordinate frame
`eᵢ = frameVector I x₀ x (bB i)` of the chart at `x₀`, which is a basis of `TangentSpace I x` because
it is the image of the canonical basis under the tangent-bundle trivialisation at `x₀` (valid on the
chart source).

The main auxiliary input is `Work.Diff.STE.deTurck.posDef_gram_of_injective`, which turns the
injectivity of `symmL` into positive definiteness of the matrix in the *canonical* basis of the model
space; the passage from the canonical basis to the coordinate frame is the definition of
`Submission.Geodesic.frameVector`.

Note that, unlike `Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef`, no `T2Space M` and no
`I.Boundaryless` hypotheses are needed: only the pointwise data at `x` is used.  This is what makes
the lemma applicable to the compactness argument on the source of a chart.
-/

namespace Work.Diff.STE.Lead

/-- **The chart matrix of a symmetric, positive definite (at a single point) section has non-zero
determinant.**  The hypotheses are the pointwise symmetry and positive definiteness of `h` at `x`,
which is the only point at which the chart matrix is evaluated. -/
theorem det_chartMatOf_ne_zero_of_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) {x : M}
    (hx : x ∈ (extChartAt I x₀).source)
    (hsym : ∀ (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < h x v v) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀
      ((extChartAt I x₀) x))).det ≠ 0 := by
  classical
  -- `x` lies in the base set of the tangent-bundle trivialisation at `x₀`.
  have hbase : x ∈ (FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa using hx
  -- The coordinate map `c ↦ symmL c` is injective, its left inverse being `continuousLinearMapAt`.
  have hL : Function.Injective
      ((FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x).toLinearMap := by
    intro a b hab
    have hab' : (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x a
        = (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x b := hab
    have h1 := congrArg
      ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x) hab'
    simpa only [Bundle.Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hbase a,
      Bundle.Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hbase b] using h1
  -- Positive definiteness of the Gram matrix in the *canonical* basis `bB` of the model space.
  have h2 := Work.Diff.STE.deTurck.posDef_gram_of_injective
    (((FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x).toLinearMap) hL (h x)
    (fun u v => hsym u v) (fun v hv => hpos v hv)
  -- The same matrix, written in the coordinate frame of the chart.
  have hpd : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      h x (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) j)))).PosDef := h2
  -- The chart matrix is that matrix.
  have hmat : (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀
        ((extChartAt I x₀) x)))
      = (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        h x (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) j)))) := by
    ext i j
    simp only [Matrix.of_apply, Work.Diff.STE.D.chartMatOf]
    rw [PartialEquiv.left_inv (extChartAt I x₀) hx]
  rw [hmat]
  exact ne_of_gt (Matrix.PosDef.det_pos hpd)

theorem det_chartMatOf_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {g₀ : Submission.Diff.SMet I M}
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) {x : M}
    (hx : x ∈ (extChartAt I x₀).source)
    (hsym : ∀ (u v : TangentSpace I x), h x u v = h x v u)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ v : TangentSpace I x, lam * g₀.inner x v v ≤ h x v v) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀
      ((extChartAt I x₀) x))).det ≠ 0 :=
  det_chartMatOf_ne_zero_of_posDef (I := I) (M := M) h x₀ hx hsym
    (fun v hv => lt_of_lt_of_le (mul_pos hlam (g₀.pos x v hv)) (hell v))

end Work.Diff.STE.Lead
