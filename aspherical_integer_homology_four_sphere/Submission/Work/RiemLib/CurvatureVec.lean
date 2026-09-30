import Submission.Work.RiemLib.Curvature
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The curvature tensor on tangent vectors

`Submission/Curvature.lean` develops the curvature `curv cov X Y Z` of *smooth vector fields* and the
sectional-curvature numerator `curvForm cov X Y x = ⟪R(X,Y)Y, X⟫`, together with the fact
(`curv_eq_of_apply_eq`) that `curv` at a point depends only on the *values* of `X`, `Y`, `Z` there.
This module packages the curvature as an honest tensor on tangent vectors,

`curvVec cov x u v w : TangentSpace I x`,

obtained by extending `u`, `v`, `w` to globally smooth sections (using
`Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq`) and evaluating `curv`.
This is the object appearing in the **Jacobi equation** `D²J/dt² + R(J, γ')γ' = 0`, which is the
starting point of the second-variation/Rauch comparison chapter of the project.

## Main results

* `curvVec_eq`: `curvVec` agrees with `curv cov X Y Z x` for any smooth extensions;
* `inner_curvVec_self`: `⟪curvVec x u v v, u⟫ = curvFormVec x u v` (compatibility with the
  sectional-curvature numerator of `Curvature.lean`);
* `curvVec_add_left/middle/right`, `curvVec_smul_left/middle/right`, `curvVec_zero_left/middle/right`:
  multilinearity in the three vector slots;
* `curvVec_antisymm`: `R(u,v)w = -R(v,u)w`;
* `inner_curvVec_skew`: `⟪R(u,v)w, z⟫ = -⟪w, R(u,v)z⟫`.
-/
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature

namespace Submission.CurvatureVec

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-- **The curvature tensor on tangent vectors**, `R(u,v)w`, obtained by extending `u`, `v`, `w` to
globally smooth sections and evaluating `curv`.  The value does not depend on the extensions
(`curvVec_eq`). -/
noncomputable def curvVec (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (u v w : TangentSpace I x) : TangentSpace I x :=
  curv cov
    (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) u))
    (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) v))
    (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) w)) x

/-- `curvVec` agrees with `curv` for any choice of smooth extensions. -/
lemma curvVec_eq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {x : M} {u v w : TangentSpace I x} {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hux : X x = u) (hvy : Y x = v) (hwz : Z x = w) :
    curvVec cov x u v w = curv cov X Y Z x := by
  unfold curvVec
  have h1 : (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) u)) x = X x :=
    (Classical.choose_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) u)).2.trans hux.symm
  have h2 : (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) v)) x = Y x :=
    (Classical.choose_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) v)).2.trans hvy.symm
  have h3 : (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) w)) x = Z x :=
    (Classical.choose_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) w)).2.trans hwz.symm
  exact curv_eq_of_apply_eq cov hcov
    (Classical.choose_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) u)).1 hX
    (Classical.choose_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) v)).1 hY
    (Classical.choose_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) w)).1 hZ
    h1 h2 h3

/-- Sum of two smooth sections is smooth. -/
private lemma add_section' {X Y : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) : CMDiff ∞ (T% (X + Y)) :=
  hX.add_section hY

/-- Constant scalar multiple of a smooth section is smooth. -/
private lemma smul_section_const' {X : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (c : ℝ) : CMDiff ∞ (T% (c • X)) := by
  simpa using (contMDiff_const (c := c)).smul_section hX

/-- **Compatibility with the sectional-curvature numerator**: `⟪R(u,v)v, u⟫ = curvFormVec x u v`. -/
lemma inner_curvVec_self (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v : TangentSpace I x) :
    inner ℝ (curvVec cov x u v v) u = curvFormVec cov x u v := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  rw [curvVec_eq cov hcov hX hY hY hXx hYx hYx,
    curvFormVec_eq cov hcov hX hY hXx hYx, ← hXx]
  rfl

/-- Multilinearity of `curvVec` in the first slot. -/
lemma curvVec_add_left (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u₁ u₂ v w : TangentSpace I x) :
    curvVec cov x (u₁ + u₂) v w = curvVec cov x u₁ v w + curvVec cov x u₂ v w := by
  obtain ⟨X₁, hX₁, hX₁x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u₁
  obtain ⟨X₂, hX₂, hX₂x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u₂
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  have hsum : CMDiff ∞ (T% (X₁ + X₂)) := add_section' hX₁ hX₂
  have hval : (X₁ + X₂) x = u₁ + u₂ := by
    simp only [Pi.add_apply, hX₁x, hX₂x]
  rw [curvVec_eq cov hcov hsum hY hZ hval hYx hZx,
    curvVec_eq cov hcov hX₁ hY hZ hX₁x hYx hZx,
    curvVec_eq cov hcov hX₂ hY hZ hX₂x hYx hZx]
  exact congrFun (curv_add_left cov hcov X₁ X₂ Y Z hX₁ hX₂ hY hZ) x

/-- Multilinearity of `curvVec` in the middle slot. -/
lemma curvVec_add_middle (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v₁ v₂ w : TangentSpace I x) :
    curvVec cov x u (v₁ + v₂) w = curvVec cov x u v₁ w + curvVec cov x u v₂ w := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y₁, hY₁, hY₁x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v₁
  obtain ⟨Y₂, hY₂, hY₂x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v₂
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  have hsum : CMDiff ∞ (T% (Y₁ + Y₂)) := add_section' hY₁ hY₂
  have hval : (Y₁ + Y₂) x = v₁ + v₂ := by
    simp only [Pi.add_apply, hY₁x, hY₂x]
  rw [curvVec_eq cov hcov hX hsum hZ hXx hval hZx,
    curvVec_eq cov hcov hX hY₁ hZ hXx hY₁x hZx,
    curvVec_eq cov hcov hX hY₂ hZ hXx hY₂x hZx]
  exact congrFun (curv_add_middle cov hcov X Y₁ Y₂ Z hX hY₁ hY₂ hZ) x

/-- Multilinearity of `curvVec` in the last slot. -/
lemma curvVec_add_right (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v w₁ w₂ : TangentSpace I x) :
    curvVec cov x u v (w₁ + w₂) = curvVec cov x u v w₁ + curvVec cov x u v w₂ := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z₁, hZ₁, hZ₁x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w₁
  obtain ⟨Z₂, hZ₂, hZ₂x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w₂
  have hsum : CMDiff ∞ (T% (Z₁ + Z₂)) := add_section' hZ₁ hZ₂
  have hval : (Z₁ + Z₂) x = w₁ + w₂ := by
    simp only [Pi.add_apply, hZ₁x, hZ₂x]
  rw [curvVec_eq cov hcov hX hY hsum hXx hYx hval,
    curvVec_eq cov hcov hX hY hZ₁ hXx hYx hZ₁x,
    curvVec_eq cov hcov hX hY hZ₂ hXx hYx hZ₂x]
  exact congrFun (curv_add_right cov hcov X Y Z₁ Z₂ hX hY hZ₁ hZ₂) x

/-- `curvVec` is linear over scalars in the first slot. -/
lemma curvVec_smul_left (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v w : TangentSpace I x) :
    curvVec cov x (c • u) v w = c • curvVec cov x u v w := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  have hsm : CMDiff ∞ (T% (c • X)) := smul_section_const' hX c
  have hval : (c • X) x = c • u := by simp only [Pi.smul_apply, hXx]
  rw [curvVec_eq cov hcov hsm hY hZ hval hYx hZx,
    curvVec_eq cov hcov hX hY hZ hXx hYx hZx]
  exact curv_smul_left cov hcov (fun _ : M => c) X Y Z x (contMDiff_const) hX hY hZ

/-- `curvVec` is linear over scalars in the middle slot. -/
lemma curvVec_smul_middle (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v w : TangentSpace I x) :
    curvVec cov x u (c • v) w = c • curvVec cov x u v w := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  have hsm : CMDiff ∞ (T% (c • Y)) := smul_section_const' hY c
  have hval : (c • Y) x = c • v := by simp only [Pi.smul_apply, hYx]
  rw [curvVec_eq cov hcov hX hsm hZ hXx hval hZx,
    curvVec_eq cov hcov hX hY hZ hXx hYx hZx]
  exact curv_smul_middle cov hcov (fun _ : M => c) X Y Z x contMDiff_const hX hY hZ

/-- `curvVec` is linear over scalars in the last slot. -/
lemma curvVec_smul_right (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v w : TangentSpace I x) :
    curvVec cov x u v (c • w) = c • curvVec cov x u v w := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  have hsm : CMDiff ∞ (T% (c • Z)) := smul_section_const' hZ c
  have hval : (c • Z) x = c • w := by simp only [Pi.smul_apply, hZx]
  rw [curvVec_eq cov hcov hX hY hsm hXx hYx hval,
    curvVec_eq cov hcov hX hY hZ hXx hYx hZx]
  exact curv_smul_right cov hcov (fun _ : M => c) X Y Z x contMDiff_const hX hY hZ

/-- `curvVec` vanishes when the first vector vanishes. -/
lemma curvVec_zero_left (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (v w : TangentSpace I x) :
    curvVec cov x 0 v w = 0 := by
  simpa using curvVec_smul_left cov hcov x (0 : ℝ) (0 : TangentSpace I x) v w

/-- `curvVec` vanishes when the middle vector vanishes. -/
lemma curvVec_zero_middle (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u w : TangentSpace I x) :
    curvVec cov x u 0 w = 0 := by
  simpa using curvVec_smul_middle cov hcov x (0 : ℝ) u (0 : TangentSpace I x) w

/-- `curvVec` vanishes when the last vector vanishes. -/
lemma curvVec_zero_right (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v : TangentSpace I x) :
    curvVec cov x u v 0 = 0 := by
  simpa using curvVec_smul_right cov hcov x (0 : ℝ) u v (0 : TangentSpace I x)

/-- The curvature on tangent vectors is antisymmetric in its first two arguments. -/
lemma curvVec_antisymm (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v w : TangentSpace I x) :
    curvVec cov x u v w = -curvVec cov x v u w := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  rw [curvVec_eq cov hcov hX hY hZ hXx hYx hZx,
    curvVec_eq cov hcov hY hX hZ hYx hXx hZx]
  exact curv_antisymm_apply cov X Y Z x

/-- Skew-symmetry of the curvature in its last two arguments. -/
lemma inner_curvVec_skew (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (x : M) (u v w z : TangentSpace I x) :
    inner ℝ (curvVec cov x u v w) z = -inner ℝ w (curvVec cov x u v z) := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  obtain ⟨W, hW, hWx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) z
  rw [curvVec_eq cov hcov hX hY hZ hXx hYx hZx,
    curvVec_eq cov hcov hX hY hW hXx hYx hWx]
  rw [← hWx, ← hZx, curv_inner_skew cov hcov hmet hX hY hZ hW]

end

end Submission.CurvatureVec
