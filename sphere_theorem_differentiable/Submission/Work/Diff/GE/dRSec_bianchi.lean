import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Curvature

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `∇_U σ` as a section (the connection-generic version of `covDir`). -/
noncomputable def covD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U S : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun p => cov S p (U p)

theorem covD_apply (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U S : Π y : M, TangentSpace I y) (p : M) : covD cov U S p = cov S p (U p) := rfl

/-- `(∇_U R)(X,Y)Z` for an arbitrary covariant derivative (the `lcOf`-generic `dRSec`). -/
noncomputable def dRSecCov (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U X Y Z : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun p => covD cov U (curv cov X Y Z) p - curv cov (covD cov U X) Y Z p
    - curv cov X (covD cov U Y) Z p - curv cov X Y (covD cov U Z) p

/-- The curvature in terms of `covD`: `R(X,Y)Z = D_X D_Y Z - D_Y D_X Z - D_{[X,Y]} Z`. -/
theorem curv_eq_covD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π y : M, TangentSpace I y) :
    curv cov X Y Z = covD cov X (covD cov Y Z) - covD cov Y (covD cov X Z)
      - covD cov (mlieBracket I X Y) Z := rfl

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

section Instances

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Pointwise form of linearity of `curv` in its middle slot in the presence of subtraction. -/
theorem curv_sub_middle_pt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (X Y₁ Y₂ Z : Π y : M, TangentSpace I y) (x : M)
    (hX : CMDiff ∞ (T% X)) (hY₁ : CMDiff ∞ (T% Y₁)) (hY₂ : CMDiff ∞ (T% Y₂))
    (hZ : CMDiff ∞ (T% Z)) :
    curv cov X (Y₁ - Y₂) Z x = curv cov X Y₁ Z x - curv cov X Y₂ Z x := by
  have h : Y₁ - Y₂ = Y₁ + (-1 : ℝ) • Y₂ := by
    funext y
    simp [sub_eq_add_neg]
  rw [h, curv_add_middle cov hcov X Y₁ ((-1 : ℝ) • Y₂) Z hX hY₁
      (ContMDiff.const_smul_section (a := (-1 : ℝ)) hY₂) hZ,
    curv_const_smul_middle cov hcov (-1) hX hY₂ hZ, neg_one_smul]
  simp only [Pi.add_apply, Pi.neg_apply]
  abel

/-- The `ℝ`-linearity-in-the-middle-slot torsion identity
`R(U, ∇_X Y - ∇_Y X, Z) + R(∇_U X, Y, Z) + R(X, ∇_U Y, Z) + (the other two cyclic instances) = 0`,
i.e. the "curvature part" of the second Bianchi identity; torsion-freeness is used to replace the
Lie brackets `[X,Y]`, `[Y,U]`, `[U,X]` by covariant derivatives. -/
theorem curv_cyclic_torsion
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    {U X Y Z : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) :
    curv cov U (mlieBracket I X Y) Z x + curv cov X (mlieBracket I Y U) Z x
      + curv cov Y (mlieBracket I U X) Z x
      + curv cov (covD cov U X) Y Z x + curv cov (covD cov X Y) U Z x
      + curv cov (covD cov Y U) X Z x
      + curv cov X (covD cov U Y) Z x + curv cov Y (covD cov X U) Z x
      + curv cov U (covD cov Y X) Z x = 0 := by
  have hcXY : CMDiff ∞ (T% (covD cov X Y)) := cmd_covD cov hcov hX hY
  have hcYX : CMDiff ∞ (T% (covD cov Y X)) := cmd_covD cov hcov hY hX
  have hcYU : CMDiff ∞ (T% (covD cov Y U)) := cmd_covD cov hcov hY hU
  have hcUY : CMDiff ∞ (T% (covD cov U Y)) := cmd_covD cov hcov hU hY
  have hcUX : CMDiff ∞ (T% (covD cov U X)) := cmd_covD cov hcov hU hX
  have hcXU : CMDiff ∞ (T% (covD cov X U)) := cmd_covD cov hcov hX hU
  have tb1 : mlieBracket I X Y = covD cov X Y - covD cov Y X := by
    rw [← torsion_zero_bracket cov htor hX hY]
    rfl
  have tb2 : mlieBracket I Y U = covD cov Y U - covD cov U Y := by
    rw [← torsion_zero_bracket cov htor hY hU]
    rfl
  have tb3 : mlieBracket I U X = covD cov U X - covD cov X U := by
    rw [← torsion_zero_bracket cov htor hU hX]
    rfl
  have e1 : curv cov U (covD cov X Y - covD cov Y X) Z x
      = curv cov U (covD cov X Y) Z x - curv cov U (covD cov Y X) Z x :=
    curv_sub_middle_pt cov hcov U (covD cov X Y) (covD cov Y X) Z x hU hcXY hcYX hZ
  have e2 : curv cov X (covD cov Y U - covD cov U Y) Z x
      = curv cov X (covD cov Y U) Z x - curv cov X (covD cov U Y) Z x :=
    curv_sub_middle_pt cov hcov X (covD cov Y U) (covD cov U Y) Z x hX hcYU hcUY hZ
  have e3 : curv cov Y (covD cov U X - covD cov X U) Z x
      = curv cov Y (covD cov U X) Z x - curv cov Y (covD cov X U) Z x :=
    curv_sub_middle_pt cov hcov Y (covD cov U X) (covD cov X U) Z x hY hcUX hcXU hZ
  have e4 : curv cov U (covD cov X Y) Z x = - curv cov (covD cov X Y) U Z x :=
    curv_antisymm_apply cov U (covD cov X Y) Z x
  have e5 : curv cov X (covD cov Y U) Z x = - curv cov (covD cov Y U) X Z x :=
    curv_antisymm_apply cov X (covD cov Y U) Z x
  have e6 : curv cov Y (covD cov U X) Z x = - curv cov (covD cov U X) Y Z x :=
    curv_antisymm_apply cov Y (covD cov U X) Z x
  rw [tb1, tb2, tb3, e1, e2, e3, e4, e5, e6]
  abel

/-- Pointwise form of the operator Jacobi identity, in the "displayed atoms" shape used by
`dRSecCov_cyclic_expand`. -/
theorem covD_jacobi_pt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (A B C Z : Π y : M, TangentSpace I y) (x : M) :
    (covD cov A (covD cov B (covD cov C Z)) x - covD cov A (covD cov C (covD cov B Z)) x
      - covD cov B (covD cov C (covD cov A Z)) x + covD cov C (covD cov B (covD cov A Z)) x)
    + (covD cov B (covD cov C (covD cov A Z)) x - covD cov B (covD cov A (covD cov C Z)) x
      - covD cov C (covD cov A (covD cov B Z)) x + covD cov A (covD cov C (covD cov B Z)) x)
    + (covD cov C (covD cov A (covD cov B Z)) x - covD cov C (covD cov B (covD cov A Z)) x
      - covD cov A (covD cov B (covD cov C Z)) x + covD cov B (covD cov A (covD cov C Z)) x) = 0 := by
  have h := congrFun (covD_jacobi cov A B C Z) x
  simpa only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] using h

/-- Pointwise form of `[D_A,D_B]Z = R(A,B)Z + D_{[A,B]}Z`. -/
theorem covD_commutator_pt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (A B Z : Π y : M, TangentSpace I y) (x : M) :
    covD cov A (covD cov B Z) x - covD cov B (covD cov A Z) x
      = curv cov A B Z x + covD cov (mlieBracket I A B) Z x :=
  congrFun (covD_commutator cov A B Z) x

/-- **Expansion step for the second Bianchi identity.** The cyclic sum of `(∇_UR)(X,Y)Z` is the
negative of the "curvature part" of the second Bianchi identity:
it equals `-(Σ_cyc R(σ₁,[σ₂,σ₃]) + Σ_cyc R(∇_{σ₁}σ₂,σ₃) + Σ_cyc R(σ₂,∇_{σ₁}σ₃))`, displayed
explicitly. The proof expands `R` in terms of `D_A = ∇_A`, uses the operator Jacobi identity
`[D_A,[D_B,D_C]] + [D_B,[D_C,D_A]] + [D_C,[D_A,D_B]] = 0` (a pure reindexing cancellation), and
the operator identity `[D_A,D_B] = R(A,B) + D_{[A,B]}`, together with the Lie-bracket Jacobi
identity for the `D_{[σ₁,[σ₂,σ₃]]}` terms. -/
theorem dRSecCov_cyclic_expand
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {U X Y Z : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) :
    dRSecCov cov U X Y Z x + dRSecCov cov X Y U Z x + dRSecCov cov Y U X Z x
      = - (curv cov U (mlieBracket I X Y) Z x + curv cov X (mlieBracket I Y U) Z x
          + curv cov Y (mlieBracket I U X) Z x
          + curv cov (covD cov U X) Y Z x + curv cov (covD cov X Y) U Z x
          + curv cov (covD cov Y U) X Z x
          + curv cov X (covD cov U Y) Z x + curv cov Y (covD cov X U) Z x
          + curv cov U (covD cov Y X) Z x) := by
  have hcYZ : CMDiff ∞ (T% (covD cov Y Z)) := cmd_covD cov hcov hY hZ
  have hcXZ : CMDiff ∞ (T% (covD cov X Z)) := cmd_covD cov hcov hX hZ
  have hcUZ : CMDiff ∞ (T% (covD cov U Z)) := cmd_covD cov hcov hU hZ
  have hbXY : CMDiff ∞ (T% (mlieBracket I X Y)) := cmd_mlieBracket hX hY
  have hbYU : CMDiff ∞ (T% (mlieBracket I Y U)) := cmd_mlieBracket hY hU
  have hbUX : CMDiff ∞ (T% (mlieBracket I U X)) := cmd_mlieBracket hU hX
  -- the three "first term" rewrites: push `D_{σ₁}` past `curv σ₂ σ₃ Z`
  have hA : covD cov U (curv cov X Y Z) x
      = covD cov U (covD cov X (covD cov Y Z)) x - covD cov U (covD cov Y (covD cov X Z)) x
        - covD cov U (covD cov (mlieBracket I X Y) Z) x := by
    rw [curv_eq_covD, covD_sub_sub cov (mdiffAt_of_cmd (cmd_covD cov hcov hX hcYZ) x)
      (mdiffAt_of_cmd (cmd_covD cov hcov hY hcXZ) x)
      (mdiffAt_of_cmd (cmd_covD cov hcov hbXY hZ) x)]
  have hB : covD cov X (curv cov Y U Z) x
      = covD cov X (covD cov Y (covD cov U Z)) x - covD cov X (covD cov U (covD cov Y Z)) x
        - covD cov X (covD cov (mlieBracket I Y U) Z) x := by
    rw [curv_eq_covD, covD_sub_sub cov (mdiffAt_of_cmd (cmd_covD cov hcov hY hcUZ) x)
      (mdiffAt_of_cmd (cmd_covD cov hcov hU hcYZ) x)
      (mdiffAt_of_cmd (cmd_covD cov hcov hbYU hZ) x)]
  have hC : covD cov Y (curv cov U X Z) x
      = covD cov Y (covD cov U (covD cov X Z)) x - covD cov Y (covD cov X (covD cov U Z)) x
        - covD cov Y (covD cov (mlieBracket I U X) Z) x := by
    rw [curv_eq_covD, covD_sub_sub cov (mdiffAt_of_cmd (cmd_covD cov hcov hU hcXZ) x)
      (mdiffAt_of_cmd (cmd_covD cov hcov hX hcUZ) x)
      (mdiffAt_of_cmd (cmd_covD cov hcov hbUX hZ) x)]
  -- the three "last term" rewrites: expand `curv σ₂ σ₃ (D_{σ₁} Z)`
  have hA' : curv cov X Y (covD cov U Z) x
      = covD cov X (covD cov Y (covD cov U Z)) x - covD cov Y (covD cov X (covD cov U Z)) x
        - covD cov (mlieBracket I X Y) (covD cov U Z) x := by
    rw [curv_eq_covD]
    simp only [Pi.sub_apply]
  have hB' : curv cov Y U (covD cov X Z) x
      = covD cov Y (covD cov U (covD cov X Z)) x - covD cov U (covD cov Y (covD cov X Z)) x
        - covD cov (mlieBracket I Y U) (covD cov X Z) x := by
    rw [curv_eq_covD]
    simp only [Pi.sub_apply]
  have hC' : curv cov U X (covD cov Y Z) x
      = covD cov U (covD cov X (covD cov Y Z)) x - covD cov X (covD cov U (covD cov Y Z)) x
        - covD cov (mlieBracket I U X) (covD cov Y Z) x := by
    rw [curv_eq_covD]
    simp only [Pi.sub_apply]
  unfold dRSecCov
  rw [hA, hB, hC, hA', hB', hC']
  -- the third order part: the operator Jacobi identity
  have hJ : (covD cov U (covD cov X (covD cov Y Z)) x - covD cov U (covD cov Y (covD cov X Z)) x
      - covD cov X (covD cov Y (covD cov U Z)) x + covD cov Y (covD cov X (covD cov U Z)) x)
    + (covD cov X (covD cov Y (covD cov U Z)) x - covD cov X (covD cov U (covD cov Y Z)) x
      - covD cov Y (covD cov U (covD cov X Z)) x + covD cov U (covD cov Y (covD cov X Z)) x)
    + (covD cov Y (covD cov U (covD cov X Z)) x - covD cov Y (covD cov X (covD cov U Z)) x
      - covD cov U (covD cov X (covD cov Y Z)) x + covD cov X (covD cov U (covD cov Y Z)) x)
    = 0 := covD_jacobi_pt cov U X Y Z x
  -- the bracket part
  have hc1 : - covD cov U (covD cov (mlieBracket I X Y) Z) x
      + covD cov (mlieBracket I X Y) (covD cov U Z) x
      = - (curv cov U (mlieBracket I X Y) Z x
          + covD cov (mlieBracket I U (mlieBracket I X Y)) Z x) := by
    rw [← covD_commutator_pt cov U (mlieBracket I X Y) Z x]
    abel
  have hc2 : - covD cov X (covD cov (mlieBracket I Y U) Z) x
      + covD cov (mlieBracket I Y U) (covD cov X Z) x
      = - (curv cov X (mlieBracket I Y U) Z x
          + covD cov (mlieBracket I X (mlieBracket I Y U)) Z x) := by
    rw [← covD_commutator_pt cov X (mlieBracket I Y U) Z x]
    abel
  have hc3 : - covD cov Y (covD cov (mlieBracket I U X) Z) x
      + covD cov (mlieBracket I U X) (covD cov Y Z) x
      = - (curv cov Y (mlieBracket I U X) Z x
          + covD cov (mlieBracket I Y (mlieBracket I U X)) Z x) := by
    rw [← covD_commutator_pt cov Y (mlieBracket I U X) Z x]
    abel
  have hcyc : mlieBracket I U (mlieBracket I X Y) + mlieBracket I X (mlieBracket I Y U)
      + mlieBracket I Y (mlieBracket I U X) = 0 := by
    have hU2 : CMDiff (minSmoothness ℝ 2) (T% U) :=
      hU.of_le (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    have hX2 : CMDiff (minSmoothness ℝ 2) (T% X) :=
      hX.of_le (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    have hY2 : CMDiff (minSmoothness ℝ 2) (T% Y) :=
      hY.of_le (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    simpa only [Pi.add_apply, Pi.zero_apply] using
      Commons.Geometry.Manifold.VectorField.mlieBracket_cyclic_sum hU2 hX2 hY2
  have hJac : covD cov (mlieBracket I U (mlieBracket I X Y)) Z x
      + covD cov (mlieBracket I X (mlieBracket I Y U)) Z x
      + covD cov (mlieBracket I Y (mlieBracket I U X)) Z x = 0 := by
    rw [← covD_add_dir, ← covD_add_dir, hcyc, covD_apply]
    exact map_zero _
  linear_combination (norm := abel) hJ + hc1 + hc2 + hc3 - hJac

theorem dRSecCov_bianchi
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    {U X Y Z : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) :
    dRSecCov cov U X Y Z x + dRSecCov cov X Y U Z x + dRSecCov cov Y U X Z x = 0 := by
  have h1 := dRSecCov_cyclic_expand cov hcov hU hX hY hZ x
  have h2 := curv_cyclic_torsion cov hcov htor hU hX hY hZ x
  rw [h1, h2, neg_zero]


end Instances

/-- **Second Bianchi identity for the covariant derivative of the curvature.**
`dRSec g U X Y Z` is the section `(∇_U R)(X,Y)Z = ∇_U(R(X,Y)Z) − R(∇_UX,Y)Z − R(X,∇_UY)Z − R(X,Y)∇_UZ`
(definition in `Work.Diff.GE.bianchi_kato_defs`). For a torsion-free connection,
`(∇_U R)(X,Y)Z + (∇_X R)(Y,U)Z + (∇_Y R)(U,X)Z = 0` pointwise. The proof is the classical one:
use the definition of `curv` to write `R(X,Y)Z = ∇_X∇_YZ − ∇_Y∇_XZ − ∇_{[X,Y]}Z`, insert the
operator identity `[∇_U,∇_V]W = R(U,V)W + ∇_{[U,V]}W`, and cancel the resulting terms with the
Jacobi identities for the commutator and for the Lie bracket
(`Commons.Geometry.Manifold.VectorField.mlieBracket_cyclic_sum`) and with torsion-freeness
(`Submission.Curvature.torsion_zero_bracket`). -/
theorem dRSec_bianchi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (htor : (lcOf g).torsion = 0)
    {U X Y Z : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) :
    dRSec g U X Y Z x + dRSec g X Y U Z x + dRSec g Y U X Z x = 0 := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have h := dRSecCov_bianchi (cov := lcOf g) hcov htor hU hX hY hZ x
  show dRSecCov (lcOf g) U X Y Z x + dRSecCov (lcOf g) X Y U Z x + dRSecCov (lcOf g) Y U X Z x = 0
  exact h

end Work.Diff.GE
