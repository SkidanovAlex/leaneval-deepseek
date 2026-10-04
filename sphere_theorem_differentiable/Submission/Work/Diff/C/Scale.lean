import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Curvature

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Scaling the metric: `pinchedFor_scale`

If `g' = c · g` (`c > 0`) and `cov` is `(κ, Λ]`-pinched for `g`, then `cov` is `(κ/c, Λ/c]`-pinched
for `g'`.  The connection and the curvature vector are unchanged; the pairing and the normalisation
rescale by `c` (and `√c`).

Used to normalise the pinching constant to `κ = 1` before applying the Hessian-comparison inputs
`Work.Diff.C.hess_upper` / `hess_lower` / `dist_eikonal2`, which are stated for `(1, 1+η]`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The fibre pairing of a metric is bilinear. -/
theorem metric_inner_smul_smul (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (x : M) (a b : ℝ) (v w : TangentSpace I x) :
    g.inner x (a • v) (b • w) = a * b * g.inner x v w := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Pinching survives scaling of the metric by a positive constant.** -/
theorem pinchedFor_scale
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {g g' : RiemannianMetric (fun x : M ↦ TangentSpace I x)} {c κ Λ : ℝ} (hc : 0 < c)
    (hinner : ∀ (x : M) (v w : TangentSpace I x), g'.inner x v w = c * g.inner x v w)
    (h : PinchedFor g cov κ Λ) :
    PinchedFor g' cov (κ / c) (Λ / c) := by
  have hsq : Real.sqrt c * Real.sqrt c = c := by rw [← sq, Real.sq_sqrt hc.le]
  intro X Y hX hY x hXX hYY hXY
  let a : M → ℝ := fun _ => Real.sqrt c
  have ha : CMDiff ∞ a := contMDiff_const
  have hax : a x = Real.sqrt c := rfl
  have hpt : ∀ Z : Π y : M, TangentSpace I y, (a • Z) x = a x • Z x := fun Z => rfl
  have hXc : CMDiff ∞ (T% (a • X)) := hX.const_smul_section (a := Real.sqrt c)
  have hYc : CMDiff ∞ (T% (a • Y)) := hY.const_smul_section (a := Real.sqrt c)
  have hXX'' : c * g.inner x (X x) (X x) = 1 := (hinner x (X x) (X x)).symm.trans hXX
  have hYY'' : c * g.inner x (Y x) (Y x) = 1 := (hinner x (Y x) (Y x)).symm.trans hYY
  have hXY'' : c * g.inner x (X x) (Y x) = 0 := (hinner x (X x) (Y x)).symm.trans hXY
  have hXu : g.inner x (X x) (X x) = 1 / c := by
    rw [eq_div_iff hc.ne']; linarith
  have hYv : g.inner x (Y x) (Y x) = 1 / c := by
    rw [eq_div_iff hc.ne']; linarith
  have hXYv : g.inner x (X x) (Y x) = 0 := by
    rcases mul_eq_zero.mp hXY'' with h | h
    · exact absurd h hc.ne'
    · exact h
  have hXu' : g.inner x ((a • X) x) ((a • X) x) = 1 := by
    rw [hpt X, metric_inner_smul_smul, hXu, hax, hsq, mul_one_div, div_self hc.ne']
  have hYv' : g.inner x ((a • Y) x) ((a • Y) x) = 1 := by
    rw [hpt Y, metric_inner_smul_smul, hYv, hax, hsq, mul_one_div, div_self hc.ne']
  have hXY' : g.inner x ((a • X) x) ((a • Y) x) = 0 := by
    rw [hpt X, hpt Y, metric_inner_smul_smul, hXYv, mul_zero]
  obtain ⟨hlow, hup⟩ := h (a • X) (a • Y) hXc hYc x hXu' hYv' hXY'
  -- tensoriality of `curv` in the three field slots, with the constant function `a = √c`
  have hscaled : curv cov (a • X) (a • Y) (a • Y) x
      = (a x * a x * a x) • curv cov X Y Y x := by
    rw [curv_smul_left cov ‹ContMDiffCovariantDerivative cov ∞› a X (a • Y) (a • Y) x ha hX hYc
        hYc,
      curv_smul_middle cov ‹ContMDiffCovariantDerivative cov ∞› a X Y (a • Y) x ha hX hY hYc,
      curv_smul_right cov ‹ContMDiffCovariantDerivative cov ∞› a X Y Y x ha hX hY hY]
    module
  have hval : g.inner x (curv cov (a • X) (a • Y) (a • Y) x) ((a • X) x)
      = c ^ 2 * g.inner x (curv cov X Y Y x) (X x) := by
    rw [hscaled, hpt X, metric_inner_smul_smul]
    have h4 : (a x * a x * a x) * (a x) = c ^ 2 := by
      rw [hax]
      rw [show Real.sqrt c * Real.sqrt c * Real.sqrt c * Real.sqrt c
          = (Real.sqrt c * Real.sqrt c) * (Real.sqrt c * Real.sqrt c) by ring, hsq]
      ring
    rw [h4]
  have hQlo : κ < c ^ 2 * g.inner x (curv cov X Y Y x) (X x) := hval ▸ hlow
  have hQup : c ^ 2 * g.inner x (curv cov X Y Y x) (X x) ≤ Λ := hval ▸ hup
  have hgoal : g'.inner x (curv cov X Y Y x) (X x) = c * g.inner x (curv cov X Y Y x) (X x) :=
    hinner x (curv cov X Y Y x) (X x)
  rw [hgoal]
  constructor
  · rw [div_lt_iff₀ hc]
    nlinarith [hQlo]
  · rw [le_div_iff₀ hc]
    nlinarith [hQup]

end Work.Diff.C
