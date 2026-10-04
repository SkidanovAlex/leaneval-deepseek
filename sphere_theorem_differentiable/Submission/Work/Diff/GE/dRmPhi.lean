import Mathlib
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `covRm` as a function of four vector fields

The frozen definition `Submission.Diff.covRm` of the components of `∇Rm` is

`covRm g x v a b c d = mvfderiv (fun y ↦ rmP g y (smoothExt x a y) … (smoothExt x d y)) x v − …`

i.e. it is the evaluation at the `Classical.epsilon`-chosen extensions `smoothExt x ·` of a
`C^∞(M)`-multilinear operation on sections of the tangent bundle.  This module introduces that
operation as an honest function `dRmPhi` of four sections, together with:

* `covRm_eq_dRmPhi`: `covRm` is `dRmPhi` evaluated on the chosen extensions;
* the elementary pointwise additivity/homogeneity of `rmP` in each of its four vector slots
  (`rmP_add_*`, `rmP_smul_*` are in `Work.Diff.GE.NablaRm`); here we only add the finite-sum forms
  `rmP_sum_*` used to expand a section that vanishes at a point in a local frame.

This is the base module for the proof that `covRm` is multilinear in its five arguments, which is
what makes `dRmNormSq` independent of the orthonormal frame.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField
open Submission.CurvatureVec

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The four-argument operation on sections whose value on the chosen extensions is `covRm`:
the derivative of `rmP` along `v` with the four connection corrections that make it tensorial. -/
noncomputable def dRmPhi (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y) : ℝ :=
  mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v
    - rmP g x (lcOf g A x v) (B x) (C x) (D x)
    - rmP g x (A x) (lcOf g B x v) (C x) (D x)
    - rmP g x (A x) (B x) (lcOf g C x v) (D x)
    - rmP g x (A x) (B x) (C x) (lcOf g D x v)

/-- `covRm` is `dRmPhi` evaluated on the chosen extensions `smoothExt x ·`. -/
theorem covRm_eq_dRmPhi (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    covRm g x v a b c d
      = dRmPhi g x v (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) := by
  simp only [dRmPhi, covRm, smoothExt_apply]

/-! ## Finite-sum forms of the multilinearity of `rmP` -/

/-- `rmP` is additive and homogeneous in its first slot, finite-sum form. -/
theorem rmP_sum_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a : ι → TangentSpace I x) (b cd dd : TangentSpace I x) :
    rmP g x (∑ i ∈ s, c i • a i) b cd dd = ∑ i ∈ s, c i * rmP g x (a i) b cd dd := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rmP_smul_fst g hLC x 0 (0 : TangentSpace I x) b cd dd)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmP_add_fst g hLC x, rmP_smul_fst g hLC x, ih]

/-- `rmP` is additive and homogeneous in its second slot, finite-sum form. -/
theorem rmP_sum_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (b : ι → TangentSpace I x) (a cd dd : TangentSpace I x) :
    rmP g x a (∑ i ∈ s, c i • b i) cd dd = ∑ i ∈ s, c i * rmP g x a (b i) cd dd := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rmP_smul_snd g hLC x 0 a (0 : TangentSpace I x) cd dd)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmP_add_snd g hLC x, rmP_smul_snd g hLC x, ih]

/-- `rmP` is additive and homogeneous in its third slot, finite-sum form. -/
theorem rmP_sum_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (cc : ι → TangentSpace I x) (a b dd : TangentSpace I x) :
    rmP g x a b (∑ i ∈ s, c i • cc i) dd = ∑ i ∈ s, c i * rmP g x a b (cc i) dd := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rmP_smul_thd g hLC x 0 a b (0 : TangentSpace I x) dd)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmP_add_thd g hLC x, rmP_smul_thd g hLC x, ih]

/-- `rmP` is additive and homogeneous in its fourth slot, finite-sum form. -/
theorem rmP_sum_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (dd : ι → TangentSpace I x) (a b cc : TangentSpace I x) :
    rmP g x a b cc (∑ i ∈ s, c i • dd i) = ∑ i ∈ s, c i * rmP g x a b cc (dd i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rmP_smul_fth g hLC x 0 a b cc (0 : TangentSpace I x))
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmP_add_fth g hLC x, rmP_smul_fth g hLC x, ih]


/-- `mvfderiv` depends only on the germ of the function (any target normed space). -/
theorem mvfderiv_congr_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f₁ f₂ : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv I f₁ x = mvfderiv I f₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-! ## Smoothness of `rmP` on smooth fields -/

/-- The pairing `y ↦ rmP g y (A y) (B y) (C y) (D y)` is `C^∞` when `A, B, C, D` are `C^∞` sections
of the tangent bundle.  The chosen extensions inside `rmP` are irrelevant: pointwise
`rmP g y (A y) (B y) (C y) (D y) = ⟪curv (lcOf g) A B D y, C y⟫`. -/
theorem rmP_fields_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (D y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov⟩ := (hLC g).1
  have hpt : ∀ y : M, rmP g y (A y) (B y) (C y) (D y)
      = inner ℝ (curv (lcOf g) A B D y) (C y) := by
    intro y
    show g.inner y (rmVec (lcOf g) y (A y) (B y) (D y)) (C y)
      = inner ℝ (curv (lcOf g) A B D y) (C y)
    rw [show inner ℝ (curv (lcOf g) A B D y) (C y)
        = g.inner y (curv (lcOf g) A B D y) (C y) from rfl]
    have hrv : rmVec (lcOf g) y (A y) (B y) (D y) = curv (lcOf g) A B D y := by
      rw [show rmVec (lcOf g) y (A y) (B y) (D y)
          = curv (lcOf g) (smoothExt y (A y)) (smoothExt y (B y)) (smoothExt y (D y)) y from rfl]
      exact Submission.Curvature.curv_eq_of_apply_eq (lcOf g) hcov (smoothExt_cmdiff y (A y)) hA
        (smoothExt_cmdiff y (B y)) hB (smoothExt_cmdiff y (D y)) hD
        (smoothExt_apply y (A y)) (smoothExt_apply y (B y)) (smoothExt_apply y (D y))
    rw [hrv]
  have hbody : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => inner ℝ (curv (lcOf g) A B D y) (C y) := funext hpt
  rw [hbody]
  have hV : CMDiff ∞ (T% (fun y : M => curv (lcOf g) A B D y)) := by
    have hDB : CMDiff ∞ (T% (fun z : M => lcOf g D z (B z))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hD hB
    have hDA : CMDiff ∞ (T% (fun z : M => lcOf g D z (A z))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hD hA
    have h1 : CMDiff ∞ (T% (fun y : M => lcOf g (fun z : M => lcOf g D z (B z)) y (A y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov (Z := fun z : M => lcOf g D z (B z)) (Y := A) hDB hA
    have h2 : CMDiff ∞ (T% (fun y : M => lcOf g (fun z : M => lcOf g D z (A z)) y (B y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov (Z := fun z : M => lcOf g D z (A z)) (Y := B) hDA hB
    haveI : IsManifold I (minSmoothness ℝ 2) M :=
      IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    haveI : IsManifold I (∞ + 1) M := ‹IsManifold I ∞ M›
    have hbr : CMDiff ∞ (T% (mlieBracket I A B)) :=
      ContDiff.mlieBracket_vectorField (m := ⊤) (n := ⊤) hA hB (by simp)
    have h3 : CMDiff ∞ (T% (fun y : M => lcOf g D y (mlieBracket I A B y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hD hbr
    have h123 := (h1.sub_section h2).sub_section h3
    exact h123
  exact ContMDiff.inner_bundle (v := fun y : M => curv (lcOf g) A B D y) (w := C) hV hC

end Work.Diff.GE
