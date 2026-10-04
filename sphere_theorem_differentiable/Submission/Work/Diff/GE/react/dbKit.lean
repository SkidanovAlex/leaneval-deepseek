/-
# Kit for the differential (second) Bianchi identity, importable from every area

`Submission.Diff.covRm` is the frozen component `(∇_v Rm)(a,b,c,d) = (∇_v R)(a,b)d` paired with `c`
of the covariant derivative of the curvature of a smooth metric `g : SMet I M`.

This module is the common foundation for proving the differential Bianchi identity

`covRm g x v a b c d + covRm g x a b v c d + covRm g x b v a c d = 0`

**without** importing either of the two mutually incompatible families of the workspace:
`Submission.Work.Diff.GE.bianchi_kato_defs` / `dRSec_bianchi` / `Evol.CBDefs` (which declare
`Work.Diff.GE.exists_isONFrame`, `Work.Diff.GE.rmVec_eq_curvVec`, `Work.Diff.GE.smoothExt_spec`, …)
and `Submission.Work.Diff.GE.curvbasic` / `Frame` / `NablaRm` (which declare the same names again).
Importing both families into one environment is a hard error, so the proofs below are *copies* of
the corresponding declarations of those families, in the namespace `Work.Diff.GE.react.db`, resting
only on the modules of the seeded library that both families have in common
(`Submission.Diff.Grad`, `Submission.Curvature`, `Submission.CurvatureVec` and the `Commons` lemmas).

Contents:

* `smoothExt_spec`/`smoothExt_cmdiff`/`smoothExt_apply`: the chosen extension of a tangent vector;
* `rmVec_eq_curvVec`, `rmP_eq`: the frozen `rmVec`/`rmP` are the extension-independent tensor
  `curvVec` of `Submission.CurvatureVec`;
* `contMDiff_curv_fields`, `rmP_fields_smooth`: `y ↦ R(X,Y)Z(y)` and `y ↦ rmP g y (A y) … (D y)` are
  smooth for smooth fields;
* `dRmPhi`, `covRm_eq_dRmPhi`: `covRm` as a function of four sections;
* `covD`, `covDir`, `dRSecCov`, `dRSec`: `∇_U σ` and `(∇_U R)(X,Y)Z` as sections, for an arbitrary
  covariant derivative and for `lcOf g`;
* the elementary algebraic and regularity lemmas about them that the proof of the second Bianchi
  identity (`Work.Diff.GE.react.dbBianchi`) and the identification of `covRm` with the pairing of
  `dRSec` (`Work.Diff.GE.react.dbCovRmEq`) need.
-/
import Mathlib
import Submission.Diff.Grad
import Submission.Curvature
import Submission.CurvatureVec
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Commons.Geometry.Manifold.VectorField.mlieBracket_cyclic_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.GE.react.db

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- `A` is a `C^∞` section of the tangent bundle (notation-free so that statements using it
elaborate without any `open scoped` line). -/
abbrev SmoothFld (A : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% A)

/-! ## The chosen smooth extension -/

/-- The chosen extension `smoothExt x u` is a smooth field with value `u` at `x`. -/
theorem smoothExt_spec (x : M) (u : TangentSpace I x) :
    CMDiff ∞ (T% (smoothExt x u)) ∧ smoothExt x u x = u := by
  have hex : ∃ X : Π y : M, TangentSpace I y, CMDiff ∞ (T% X) ∧ X x = u :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  exact Classical.epsilon_spec hex

theorem smoothExt_cmdiff (x : M) (u : TangentSpace I x) : CMDiff ∞ (T% (smoothExt x u)) :=
  (smoothExt_spec (I := I) (M := M) x u).1

theorem smoothExt_apply (x : M) (u : TangentSpace I x) : smoothExt x u x = u :=
  (smoothExt_spec (I := I) (M := M) x u).2

/-! ## `∇_U σ` and `(∇_U R)(X,Y)Z` as sections -/

/-- `∇_U σ`, the covariant derivative of the section `σ` in the direction of the field `U`
(connection-generic). -/
noncomputable def covD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U S : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun p => cov S p (U p)

theorem covD_apply (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U S : Π y : M, TangentSpace I y) (p : M) : covD cov U S p = cov S p (U p) := rfl

/-- `(∇_U R)(X,Y)Z = ∇_U(R(X,Y)Z) - R(∇_UX,Y)Z - R(X,∇_UY)Z - R(X,Y)∇_UZ` for an arbitrary
covariant derivative, as a section. -/
noncomputable def dRSecCov (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U X Y Z : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun p => covD cov U (curv cov X Y Z) p - curv cov (covD cov U X) Y Z p
    - curv cov X (covD cov U Y) Z p - curv cov X Y (covD cov U Z) p

/-- The curvature in terms of `covD`: `R(X,Y)Z = D_X D_Y Z - D_Y D_X Z - D_{[X,Y]} Z`. -/
theorem curv_eq_covD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π y : M, TangentSpace I y) :
    curv cov X Y Z = covD cov X (covD cov Y Z) - covD cov Y (covD cov X Z)
      - covD cov (mlieBracket I X Y) Z := rfl

/-- `∇_U σ` of the Levi-Civita connection of `g`. -/
noncomputable def covDir (g : SMet I M) (U σ : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace I y :=
  fun p => lcOf g σ p (U p)

theorem covDir_eq_covD (g : SMet I M) (U σ : Π y : M, TangentSpace I y) :
    covDir g U σ = covD (lcOf g) U σ := rfl

/-- `(∇_U R)(X,Y)Z` for the Levi-Civita connection of `g`, as a section. -/
noncomputable def dRSec (g : SMet I M) (U X Y Z : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace I y :=
  fun p => lcOf g (curv (lcOf g) X Y Z) p (U p)
    - curv (lcOf g) (covDir g U X) Y Z p
    - curv (lcOf g) X (covDir g U Y) Z p
    - curv (lcOf g) X Y (covDir g U Z) p

/-- `dRSec` is `dRSecCov` of the Levi-Civita connection of `g`. -/
theorem dRSec_eq_dRSecCov (g : SMet I M) (U X Y Z : Π y : M, TangentSpace I y) :
    dRSec g U X Y Z = dRSecCov (lcOf g) U X Y Z := rfl

/-! ## Elementary algebra of `covD` -/

theorem covD_add (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {A S₁ S₂ : Π y : M, TangentSpace I y} {x : M}
    (h₁ : MDiffAt (T% S₁) x) (h₂ : MDiffAt (T% S₂) x) :
    covD cov A (S₁ + S₂) x = covD cov A S₁ x + covD cov A S₂ x := by
  rw [covD_apply, covD_apply, covD_apply, cov.isCovariantDerivativeOn.add h₁ h₂, add_apply]

theorem covD_sub (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {A S₁ S₂ : Π y : M, TangentSpace I y} {x : M}
    (h₁ : MDiffAt (T% S₁) x) (h₂ : MDiffAt (T% S₂) x) :
    covD cov A (S₁ - S₂) x = covD cov A S₁ x - covD cov A S₂ x := by
  have hS : S₁ - S₂ = S₁ + (-1 : ℝ) • S₂ := by
    funext y
    simp [sub_eq_add_neg]
  have h₂' : MDiffAt (T% ((-1 : ℝ) • S₂)) x :=
    (mdifferentiableAt_const (c := (-1 : ℝ))).smul_section h₂
  rw [hS, covD_apply, covD_apply, covD_apply, cov.isCovariantDerivativeOn.add h₁ h₂',
    cov.isCovariantDerivativeOn.smul_const (-1) h₂, add_apply, smul_apply, neg_one_smul,
    sub_eq_add_neg]

theorem covD_sub_sub (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {A S₁ S₂ S₃ : Π y : M, TangentSpace I y} {x : M}
    (h₁ : MDiffAt (T% S₁) x) (h₂ : MDiffAt (T% S₂) x) (h₃ : MDiffAt (T% S₃) x) :
    covD cov A (S₁ - S₂ - S₃) x = covD cov A S₁ x - covD cov A S₂ x - covD cov A S₃ x := by
  rw [covD_sub cov (mdifferentiableAt_sub_section h₁ h₂) h₃, covD_sub cov h₁ h₂]

theorem covD_add_dir (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {A B S : Π y : M, TangentSpace I y} {x : M} :
    covD cov (A + B) S x = covD cov A S x + covD cov B S x := by
  rw [covD_apply, covD_apply, covD_apply, Pi.add_apply, map_add]

theorem covD_sub_dir (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {A B S : Π y : M, TangentSpace I y} {x : M} :
    covD cov (A - B) S x = covD cov A S x - covD cov B S x := by
  rw [covD_apply, covD_apply, covD_apply, Pi.sub_apply, map_sub]

/-- The operator identity `[D_A,D_B]Z = R(A,B)Z + D_{[A,B]}Z`. -/
theorem covD_commutator (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (A B Z : Π y : M, TangentSpace I y) :
    covD cov A (covD cov B Z) - covD cov B (covD cov A Z)
      = curv cov A B Z + covD cov (mlieBracket I A B) Z := by
  rw [curv_eq_covD]
  abel

/-- The operator Jacobi identity `[D_A,[D_B,D_C]]Z + [D_B,[D_C,D_A]]Z + [D_C,[D_A,D_B]]Z = 0`. -/
theorem covD_jacobi (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (A B C Z : Π y : M, TangentSpace I y) :
    (covD cov A (covD cov B (covD cov C Z)) - covD cov A (covD cov C (covD cov B Z))
      - covD cov B (covD cov C (covD cov A Z)) + covD cov C (covD cov B (covD cov A Z)))
    + (covD cov B (covD cov C (covD cov A Z)) - covD cov B (covD cov A (covD cov C Z))
      - covD cov C (covD cov A (covD cov B Z)) + covD cov A (covD cov C (covD cov B Z)))
    + (covD cov C (covD cov A (covD cov B Z)) - covD cov C (covD cov B (covD cov A Z))
      - covD cov A (covD cov B (covD cov C Z)) + covD cov B (covD cov A (covD cov C Z)))
    = 0 := by
  unfold covD
  abel

/-! ## Regularity of `covD` and of the Lie bracket -/

/-- `∇_U σ` of smooth sections is smooth. -/
theorem cmd_covD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) {A S : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hS : CMDiff ∞ (T% S)) : CMDiff ∞ (T% (covD cov A S)) :=
  Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (E := E) (H := H) (I := I) (M := M) cov hcov hS hA

/-- The Lie bracket of smooth vector fields is smooth. -/
theorem cmd_mlieBracket {A B : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) : CMDiff ∞ (T% (mlieBracket I A B)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  intro y
  exact (hA y).mlieBracket_vectorField (hB y) (by simp)

theorem mdiffAt_of_cmd {S : Π y : M, TangentSpace I y} (hS : CMDiff ∞ (T% S)) (x : M) :
    MDiffAt (T% S) x := (hS x).mdifferentiableAt (by simp)

/-! ## `rmVec`/`rmP` versus the seeded tensor `curvVec` -/

/-- The `Classical.epsilon`-defined curvature `rmVec` agrees with the extension-independent tensor
`Submission.CurvatureVec.curvVec`. -/
theorem rmVec_eq_curvVec
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v w : TangentSpace I x) :
    rmVec cov x u v w = Submission.CurvatureVec.curvVec cov x u v w := by
  rw [Submission.CurvatureVec.curvVec_eq cov hcov (smoothExt_cmdiff x u) (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x w) (smoothExt_apply x u) (smoothExt_apply x v) (smoothExt_apply x w)]
  rfl

/-- `rmP` is the curvature tensor paired with its last two arguments. -/
theorem rmP_eq (g : SMet I M) (hcov : ContMDiffCovariantDerivative (lcOf g) ∞)
    (x : M) (a b c d : TangentSpace I x) :
    rmP g x a b c d = g.inner x (Submission.CurvatureVec.curvVec (lcOf g) x a b d) c := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rw [show rmP g x a b c d = g.inner x (rmVec (lcOf g) x a b d) c from rfl,
    rmVec_eq_curvVec (lcOf g) hcov x a b d]

/-! ## Smoothness of the curvature of smooth fields -/

/-- **The curvature of a smooth connection as a smooth section.**
If `cov` is a `C^∞` covariant derivative and `X, Y, Z` are smooth vector fields, then
`y ↦ R(X,Y)Z(y) = curv cov X Y Z y` is a smooth vector field. -/
theorem contMDiff_curv_fields
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (T% (fun y : M => curv cov X Y Z y)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  have hbr : CMDiff ∞ (T% (mlieBracket I X Y)) := by
    intro y
    exact (hX y).mlieBracket_vectorField (hY y) (by simp)
  have h1 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hY) hX
  have h2 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (X y')) y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hX) hY
  have h3 : CMDiff ∞ (T% (fun y : M => cov Z y (mlieBracket I X Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov hZ hbr
  change CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y)
      - cov (fun y' : M => cov Z y' (X y')) y (Y y) - cov Z y (mlieBracket I X Y y)))
  exact (h1.sub_section h2).sub_section h3

/-- `y ↦ rmP g y (A y) (B y) (C y) (D y)` is smooth for smooth fields `A, B, C, D`. -/
theorem rmP_fields_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (D y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  have hcurv : CMDiff ∞ (T% (fun y : M => curv (lcOf g) A B D y)) :=
    contMDiff_curv_fields (lcOf g) hcov hA hB hD
  have hfun : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => inner ℝ (curv (lcOf g) A B D y) (C y) := by
    funext y
    show (g.inner y (rmVec (lcOf g) y (A y) (B y) (D y))) (C y) = _
    rw [rmVec_eq_curvVec (lcOf g) hcov y (A y) (B y) (D y),
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl]
    rfl
  rw [hfun]
  exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => curv (lcOf g) A B D y)
    (w := C) hcurv hC

/-! ## `covRm` as a function of four sections -/

/-- The four-argument operation on sections whose value on the chosen extensions is `covRm`:
the derivative of `rmP` along `v` with the four connection corrections. -/
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

end Work.Diff.GE.react.db
