import Submission.Work.RiemLib.CurveField
import Submission.Work.RiemLib.ChartCurv
import Submission.Work.RiemLib.CornerCut

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The covariant derivative along a curve

This file defines the covariant derivative of a field along a curve, using the section-extension
lemma `Submission.CurveField.exists_contMDiff_section_eventuallyEq_of_contDiffOn`: any `C^∞` field
along a curve with non-vanishing velocity agrees, near a time, with a *globally smooth section* of
the tangent bundle, and `∇_{γ'}η` only depends on that germ.

## Contents

* `fieldExt`: a chosen globally smooth section agreeing near `t₀` with the field whose chart
  coordinates at `γ t₀` are `α`;
* `curveCovDeriv`: the covariant derivative along a curve, `∇_{γ'(t₀)}η`;
* **`cov_eq_of_eventuallyEq_along_curve`**: `∇_{γ'}Z` at `t₀` only depends on the germ of `Z` along the
  curve near `t₀` — proved from the explicit chart formula
  `cov_eq_frameVector_coordFun` together with the chain rule for the coordinate function along `γ`;
* **`curveCovDeriv_eq`**: the characterisation of `curveCovDeriv` by an arbitrary global extension;
* `curveCovDeriv_coordFun`: the special case of a globally smooth section (the restriction of `Z` to
  `γ`), which is the form used for parallel transport and for the Jacobi equation;
* **`curveCovDeriv_chart`**: the explicit chart formula
  `∇_{γ'}η = σ_{deriv α t₀ + Γ(α t₀)(γ')}`;
* `curveCovDeriv_add` and `curveCovDeriv_const_smul`: additivity and `ℝ`-homogeneity in the field.

### Still to come

* the **Leibniz rule** `∇_{γ'}(f • η) = f(t₀) • ∇_{γ'}η + (deriv f t₀) • η(t₀)`, which needs a
  smooth *function* on `M` agreeing with `f` along `γ` near `t₀` (the same flow-box argument as in
  `Submission/CurveField.lean` produces it);
* the **field-level** derivative `t ↦ ∇_{γ'(t)}η`, needed to write `∇_t∇_tJ + R(J,γ')γ' = 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartCurv
open Submission.CornerCut

namespace Submission.CurveCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-! ## The germ lemma -/

/-- **`∇_{γ'}Z` at `t₀` only depends on the germ of `Z` along `γ` at `t₀`.**

Both sides are rewritten through the explicit chart formula `cov_eq_frameVector_coordFun` in the
chart at `γ t₀`: the two terms are `deriv ((coordFun x₀ Z) ∘ γ) t₀` (by the chain rule
`mvfderiv_comp_curve`) and `chrB cov x₀ (γ t₀) (coordFun x₀ Z (γ t₀)) _`. -/
theorem cov_eq_of_eventuallyEq_along_curve
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {t₀ : ℝ}
    {Z Z' : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z)) (hZ' : CMDiff ∞ (T% Z'))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    (hev : ∀ᶠ t in 𝓝 t₀, Z (γ t) = Z' (γ t)) :
    cov Z (γ t₀) (curveVelocity (I := I) γ t₀)
      = cov Z' (γ t₀) (curveVelocity (I := I) γ t₀) := by
  classical
  set x₀ : M := γ t₀ with hx₀
  have hsrc : γ t₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  set vv : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀)
    (curveVelocity (I := I) γ t₀) with hvdef
  have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hsrc
  have hv : frameVector (I := I) x₀ (γ t₀) vv = curveVelocity (I := I) γ t₀ := by
    rw [hvdef]
    exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt E (TangentSpace I) x₀) (R := ℝ) hbase (curveVelocity (I := I) γ t₀)
  have key : ∀ W : Π x : M, TangentSpace I x, CMDiff ∞ (T% W) →
      cov W (γ t₀) (curveVelocity (I := I) γ t₀)
        = frameVector (I := I) x₀ (γ t₀)
            (deriv (fun t => coordFun x₀ W (γ t)) t₀
              + chrB cov x₀ (γ t₀) (coordFun x₀ W (γ t₀)) vv) := by
    intro W hW
    conv_lhs => rw [← hv]
    rw [cov_eq_frameVector_coordFun (cov := cov) x₀ hW hsrc (v := vv)]
    have hcomp : mvfderiv I (coordFun x₀ W) (γ t₀) (frameVector (I := I) x₀ (γ t₀) vv)
        = deriv (fun t => coordFun x₀ W (γ t)) t₀ := by
      rw [hv]
      exact Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := coordFun x₀ W)
        (γ := γ) (t := t₀)
        ((contMDiffAt_coordFun (x₀ := x₀) hW hsrc).mdifferentiableAt (by simp)) hγmd
    rw [hcomp]
  rw [key Z hZ, key Z' hZ']
  have heq : (fun t => coordFun x₀ Z (γ t)) =ᶠ[𝓝 t₀] (fun t => coordFun x₀ Z' (γ t)) := by
    filter_upwards [hev] with t ht
    simp only [coordFun_apply, ht]
  rw [heq.deriv_eq, heq.eq_of_nhds]


/-! ## The covariant derivative along a curve -/

/-- A chosen globally smooth section agreeing near `t₀` with the field along `γ` whose chart
coordinates at `γ t₀` are `α`. -/
noncomputable def fieldExt (γ : ℝ → M) {V : Set ℝ} (hV : IsOpen V) (t₀ : ℝ) (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    (α : ℝ → E) (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) :
    Π x : M, TangentSpace I x :=
  Classical.choose (Submission.CurveField.exists_contMDiff_section_eventuallyEq_of_contDiffOn
    (I := I) hV ht₀ hγ hne hα)

/-- The chosen section is globally smooth. -/
lemma fieldExt_contMDiff (γ : ℝ → M) {V : Set ℝ} (hV : IsOpen V) (t₀ : ℝ) (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    (α : ℝ → E) (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) :
    CMDiff ∞ (T% (fieldExt γ hV t₀ ht₀ hγ hne α hα)) :=
  (Classical.choose_spec (Submission.CurveField.exists_contMDiff_section_eventuallyEq_of_contDiffOn
    (I := I) hV ht₀ hγ hne hα)).1

/-- The chosen section agrees near `t₀` with the field. -/
lemma fieldExt_eventuallyEq (γ : ℝ → M) {V : Set ℝ} (hV : IsOpen V) (t₀ : ℝ) (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    (α : ℝ → E) (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) :
    ∀ᶠ t in 𝓝 t₀, (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t)
      = frameVector (I := I) (γ t₀) (γ t) (α t) :=
  (Classical.choose_spec (Submission.CurveField.exists_contMDiff_section_eventuallyEq_of_contDiffOn
    (I := I) hV ht₀ hγ hne hα)).2

/-- **The covariant derivative along a curve**: `∇_{γ'(t₀)} η`, where `η` is the field along `γ`
whose chart coordinates in the chart at `γ t₀` are `α`. -/
noncomputable def curveCovDeriv (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) {V : Set ℝ} (hV : IsOpen V) (t₀ : ℝ) (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    (α : ℝ → E) (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) :
    TangentSpace I (γ t₀) :=
  cov (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t₀) (curveVelocity (I := I) γ t₀)

/-- **Characterisation of the covariant derivative along a curve**: it equals
`cov Z (γ t₀) (γ'(t₀))` for *any* globally smooth section `Z` agreeing with the field near `t₀`. -/
theorem curveCovDeriv_eq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {α : ℝ → E} (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    {Z : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    (hev : ∀ᶠ t in 𝓝 t₀, Z (γ t) = frameVector (I := I) (γ t₀) (γ t) (α t)) :
    curveCovDeriv cov γ hV t₀ ht₀ hγ hne α hα
      = cov Z (γ t₀) (curveVelocity (I := I) γ t₀) :=
  cov_eq_of_eventuallyEq_along_curve (fieldExt_contMDiff γ hV t₀ ht₀ hγ hne α hα) hZ hγmd
    ((fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α hα).and hev |>.mono
      (fun _ ht => ht.1.trans ht.2.symm))


/-- **`∇_{γ'}` is additive in the field.** -/
theorem curveCovDeriv_add (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {α₁ α₂ : ℝ → E}
    (hα₁ : ContDiffOn ℝ ∞ α₁ (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    (hα₂ : ContDiffOn ℝ ∞ α₂ (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀) :
    curveCovDeriv cov γ hV t₀ ht₀ hγ hne (fun t => α₁ t + α₂ t) (hα₁.add hα₂)
      = curveCovDeriv cov γ hV t₀ ht₀ hγ hne α₁ hα₁
        + curveCovDeriv cov γ hV t₀ ht₀ hγ hne α₂ hα₂ := by
  have hZ₁ := fieldExt_contMDiff γ hV t₀ ht₀ hγ hne α₁ hα₁
  have hZ₂ := fieldExt_contMDiff γ hV t₀ ht₀ hγ hne α₂ hα₂
  have hev : ∀ᶠ t in 𝓝 t₀,
      (fieldExt γ hV t₀ ht₀ hγ hne α₁ hα₁ + fieldExt γ hV t₀ ht₀ hγ hne α₂ hα₂) (γ t)
        = frameVector (I := I) (γ t₀) (γ t) (α₁ t + α₂ t) := by
    filter_upwards [fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α₁ hα₁,
      fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α₂ hα₂] with t h₁ h₂
    rw [Pi.add_apply, h₁, h₂, frameVector_add]
  rw [curveCovDeriv_eq cov hV ht₀ hγ hne (hα₁.add hα₂) (hZ₁.add_section hZ₂) hγmd hev,
    curveCovDeriv_eq cov hV ht₀ hγ hne hα₁ hZ₁ hγmd
      (fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α₁ hα₁),
    curveCovDeriv_eq cov hV ht₀ hγ hne hα₂ hZ₂ hγmd
      (fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α₂ hα₂),
    cov.isCovariantDerivativeOn.add ((hZ₁ (γ t₀)).mdifferentiableAt (by simp))
      ((hZ₂ (γ t₀)).mdifferentiableAt (by simp))]
  rfl

/-- **`∇_{γ'}` is `ℝ`-homogeneous in the field.** -/
theorem curveCovDeriv_const_smul (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {α : ℝ → E} (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) (c : ℝ)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀) :
    curveCovDeriv cov γ hV t₀ ht₀ hγ hne (fun t => c • α t) (hα.const_smul c)
      = c • curveCovDeriv cov γ hV t₀ ht₀ hγ hne α hα := by
  have hZ := fieldExt_contMDiff γ hV t₀ ht₀ hγ hne α hα
  have hev : ∀ᶠ t in 𝓝 t₀, (fun q : M => c • fieldExt γ hV t₀ ht₀ hγ hne α hα q) (γ t)
      = frameVector (I := I) (γ t₀) (γ t) ((fun t => c • α t) t) := by
    filter_upwards [fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α hα] with t h
    rw [h]
    exact (frameVector_smul (I := I) (γ t₀) (γ t) c (α t)).symm
  rw [curveCovDeriv_eq cov hV ht₀ hγ hne (hα.const_smul c) (hZ.const_smul_section (a := c)) hγmd hev,
    curveCovDeriv_eq cov hV ht₀ hγ hne hα hZ hγmd
      (fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α hα),
    cov.isCovariantDerivativeOn.smul_const c ((hZ (γ t₀)).mdifferentiableAt (by simp))]
  rfl


/-- **The covariant derivative of the restriction of a global smooth section**: for a globally
smooth `Z`, the field along `γ` with coordinates `t ↦ coordFun (γ t₀) Z (γ t)` has covariant
derivative `∇_{γ'(t₀)}Z`. -/
theorem curveCovDeriv_coordFun (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {Z : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    (hα : ContDiffOn ℝ ∞ (fun t => coordFun (γ t₀) Z (γ t))
      (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) :
    curveCovDeriv cov γ hV t₀ ht₀ hγ hne (fun t => coordFun (γ t₀) Z (γ t)) hα
      = cov Z (γ t₀) (curveVelocity (I := I) γ t₀) :=
  curveCovDeriv_eq cov hV ht₀ hγ hne hα hZ hγmd (by
    filter_upwards [(hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto
      ((chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀)))] with t ht
    exact (frameVector_coordFun_eq (x₀ := γ t₀) ht).symm)


/-- **The chart formula for the covariant derivative along a curve.**  In the chart at `γ t₀` the
covariant derivative of the field with coordinates `α` is
`σ_{deriv α t₀ + Γ(α t₀)(γ')}`, where `γ'` is written in the coordinates of that chart. -/
theorem curveCovDeriv_chart (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {α : ℝ → E} (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀) :
    curveCovDeriv cov γ hV t₀ ht₀ hγ hne α hα
      = frameVector (I := I) (γ t₀) (γ t₀)
          (deriv α t₀ + chrB cov (γ t₀) (γ t₀) (α t₀)
            ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀)
              (curveVelocity (I := I) γ t₀))) := by
  classical
  set x₀ : M := γ t₀ with hx₀
  have hsrc : γ t₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  set vv : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀)
    (curveVelocity (I := I) γ t₀) with hvdef
  have hv : frameVector (I := I) x₀ (γ t₀) vv = curveVelocity (I := I) γ t₀ :=
    frameVector_continuousLinearMapAt (I := I) x₀ (curveVelocity (I := I) γ t₀)
  have hW := fieldExt_contMDiff γ hV t₀ ht₀ hγ hne α hα
  have hkey : cov (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t₀) (curveVelocity (I := I) γ t₀)
      = frameVector (I := I) x₀ (γ t₀)
          (deriv (fun t => coordFun x₀ (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t)) t₀
            + chrB cov x₀ (γ t₀) (coordFun x₀ (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t₀)) vv) := by
    conv_lhs => rw [← hv]
    rw [cov_eq_frameVector_coordFun (cov := cov) x₀ hW hsrc (v := vv)]
    have hcomp : mvfderiv I (coordFun x₀ (fieldExt γ hV t₀ ht₀ hγ hne α hα)) (γ t₀)
        (frameVector (I := I) x₀ (γ t₀) vv)
        = deriv (fun t => coordFun x₀ (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t)) t₀ := by
      rw [hv]
      exact Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
        (g := coordFun x₀ (fieldExt γ hV t₀ ht₀ hγ hne α hα)) (γ := γ) (t := t₀)
        ((contMDiffAt_coordFun (x₀ := x₀) hW hsrc).mdifferentiableAt (by simp)) hγmd
    rw [hcomp]
  have hcoord : (fun t => coordFun x₀ (fieldExt γ hV t₀ ht₀ hγ hne α hα) (γ t))
      =ᶠ[𝓝 t₀] α := by
    filter_upwards [fieldExt_eventuallyEq γ hV t₀ ht₀ hγ hne α hα,
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto
        ((chartAt H x₀).open_source.mem_nhds hsrc)] with t h1 h2
    rw [coordFun_apply, h1]
    exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) x₀)
      (R := ℝ) (by simpa using h2) (α t)
  rw [curveCovDeriv, hkey, hcoord.deriv_eq, hcoord.eq_of_nhds]

/-- **The chart formula for `∇_{γ'}Z` in a fixed chart.**  If the globally smooth section `Z` agrees,
near `t₀`, with the field `t ↦ frameVector x₀ (γ t) (y t)` (i.e. its coordinates in the chart at `x₀`
along `γ` are `y`), then

`∇_{γ'(t₀)}Z = σ_{y'(t₀) + Γ(y(t₀))(γ')}`,

the coordinates of `γ'` being taken in the chart at `x₀`.  Unlike `curveCovDeriv_chart` the chart
centre does not move with `t`, which is what makes it possible to glue computations over a
decomposition of the curve into chart pieces. -/
theorem cov_eq_frameVector_chartCoord
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {γ : ℝ → M} {t₀ : ℝ} (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    (hsrc : γ t₀ ∈ (chartAt H x₀).source)
    {y : ℝ → E} {Z : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z))
    (hev : ∀ᶠ t in 𝓝 t₀, Z (γ t) = frameVector (I := I) x₀ (γ t) (y t)) :
    cov Z (γ t₀) (curveVelocity (I := I) γ t₀)
      = frameVector (I := I) x₀ (γ t₀)
          (deriv y t₀ + chrB cov x₀ (γ t₀) (y t₀)
            ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀)
              (curveVelocity (I := I) γ t₀))) := by
  set vv : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀)
    (curveVelocity (I := I) γ t₀) with hvdef
  have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hsrc
  have hv : frameVector (I := I) x₀ (γ t₀) vv = curveVelocity (I := I) γ t₀ := by
    rw [hvdef]
    exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt E (TangentSpace I) x₀) (R := ℝ) hbase (curveVelocity (I := I) γ t₀)
  conv_lhs => rw [← hv]
  rw [cov_eq_frameVector_coordFun (cov := cov) x₀ hZ hsrc (v := vv)]
  have hcomp : mvfderiv I (coordFun x₀ Z) (γ t₀) (frameVector (I := I) x₀ (γ t₀) vv)
      = deriv (fun t => coordFun x₀ Z (γ t)) t₀ := by
    rw [hv]
    exact Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := coordFun x₀ Z)
      (γ := γ) (t := t₀)
      ((contMDiffAt_coordFun (x₀ := x₀) hZ hsrc).mdifferentiableAt (by simp)) hγmd
  rw [hcomp]
  have hcoord : (fun t => coordFun x₀ Z (γ t)) =ᶠ[𝓝 t₀] y := by
    filter_upwards [hev,
      (hγmd.continuousAt).tendsto ((chartAt H x₀).open_source.mem_nhds hsrc)] with t h1 h2
    rw [coordFun_apply, h1]
    exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) x₀)
      (R := ℝ) (by simpa using h2) (y t)
  rw [hcoord.deriv_eq, hcoord.eq_of_nhds]

/-- **The covariant derivative along a curve of a field given by coordinates in a fixed chart.** -/
theorem exists_section_and_cov_eq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hsrcV : ∀ t ∈ V, γ t ∈ (chartAt H x₀).source)
    (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {y : ℝ → E} (hy : ContDiffOn ℝ ∞ y (V ∩ γ ⁻¹' (chartAt H x₀).source)) :
    ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      (∀ᶠ t in 𝓝 t₀, Z (γ t) = frameVector (I := I) x₀ (γ t) (y t)) ∧
      cov Z (γ t₀) (curveVelocity (I := I) γ t₀)
        = frameVector (I := I) x₀ (γ t₀)
            (deriv y t₀ + chrB cov x₀ (γ t₀) (y t₀)
              ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀)
                (curveVelocity (I := I) γ t₀))) := by
  obtain ⟨Z, hZ, hev⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_of_contDiffOn_chart
      (I := I) x₀ hV ht₀ hγ hsrcV hne hy
  exact ⟨Z, hZ, hev, cov_eq_frameVector_chartCoord (cov := cov)
    ((hγ.contMDiffAt (hV.mem_nhds ht₀)).mdifferentiableAt (by simp))
    (hsrcV t₀ ht₀) hZ hev⟩

/-- **The Leibniz rule for the covariant derivative along a curve**:
`∇_{γ'}(f • η) = f(t₀) • ∇_{γ'}η + f'(t₀) • η(t₀)`. -/
theorem curveCovDeriv_smul_fun (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {α : ℝ → E} (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    (hsmul : ContDiffOn ℝ ∞ (fun t => f t • α t) (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀) :
    curveCovDeriv cov γ hV t₀ ht₀ hγ hne (fun t => f t • α t) hsmul
      = f t₀ • curveCovDeriv cov γ hV t₀ ht₀ hγ hne α hα
        + deriv f t₀ • frameVector (I := I) (γ t₀) (γ t₀) (α t₀) := by
  have hsrc : γ t₀ ∈ (chartAt H (γ t₀)).source := mem_chart_source H (γ t₀)
  have hnb : V ∩ γ ⁻¹' (chartAt H (γ t₀)).source ∈ 𝓝 t₀ :=
    Filter.inter_mem (hV.mem_nhds ht₀)
      ((hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).preimage_mem_nhds
        ((chartAt H (γ t₀)).open_source.mem_nhds hsrc))
  have hdf : HasDerivAt f (deriv f t₀) t₀ :=
    ((hf.contDiffAt hnb).differentiableAt (by simp)).hasDerivAt
  have hdα : HasDerivAt α (deriv α t₀) t₀ :=
    ((hα.contDiffAt hnb).differentiableAt (by simp)).hasDerivAt
  have hfun : (f • α) = fun t => f t • α t := funext fun t => rfl
  have hder : deriv (fun t => f t • α t) t₀ = f t₀ • deriv α t₀ + deriv f t₀ • α t₀ := by
    rw [← hfun]
    exact (hdf.smul hdα).deriv
  have hC : chrB cov (γ t₀) (γ t₀) (f t₀ • α t₀)
      ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀)
        (curveVelocity (I := I) γ t₀))
      = f t₀ • chrB cov (γ t₀) (γ t₀) (α t₀)
          ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀)
            (curveVelocity (I := I) γ t₀)) :=
    chrB_smul_fst (γ t₀) (γ t₀) (f t₀) (α t₀) _ hsrc
  rw [curveCovDeriv_chart cov hV ht₀ hγ hne hsmul hγmd,
      curveCovDeriv_chart cov hV ht₀ hγ hne hα hγmd, hder, hC]
  rw [← frameVector_smul, ← frameVector_smul, ← frameVector_add]
  congr 1
  rw [smul_add]
  abel

end

end Submission.CurveCov
