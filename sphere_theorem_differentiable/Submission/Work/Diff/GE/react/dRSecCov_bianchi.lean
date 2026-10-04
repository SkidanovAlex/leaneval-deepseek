import Mathlib
import Submission.Work.Diff.GE.react.dbKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# The second (differential) Bianchi identity, importable next to either family

This module copies the proof of the second Bianchi identity
`(∇_U R)(X,Y)Z + (∇_X R)(Y,U)Z + (∇_Y R)(U,X)Z = 0` for an arbitrary torsion-free `C^∞`
covariant derivative, in the vocabulary of `Work.Diff.GE.react.dbKit` (so that the file rests
only on `Mathlib`, `Submission.Diff.Grad`, `Submission.Curvature`, `Submission.CurvatureVec`
and the two `Commons` lemmas imported by the kit).  The auxiliary declarations live in the
nested namespace `Work.Diff.GE.react.db.A`.
-/

namespace Work.Diff.GE.react

open scoped Bundle ContDiff Manifold Topology BigOperators
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Curvature
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace db

namespace A

section Aux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Pointwise form of linearity of `curv` in its middle slot in the presence of subtraction. -/
theorem curv_sub_middle_pt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (X Y₁ Y₂ Z : Π y : M, TangentSpace I y) (x : M)
    (hX : SmoothFld X) (hY₁ : SmoothFld Y₁) (hY₂ : SmoothFld Y₂)
    (hZ : SmoothFld Z) :
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
    (hU : SmoothFld U) (hX : SmoothFld X) (hY : SmoothFld Y) (hZ : SmoothFld Z)
    (x : M) :
    curv cov U (mlieBracket I X Y) Z x + curv cov X (mlieBracket I Y U) Z x
      + curv cov Y (mlieBracket I U X) Z x
      + curv cov (covD cov U X) Y Z x + curv cov (covD cov X Y) U Z x
      + curv cov (covD cov Y U) X Z x
      + curv cov X (covD cov U Y) Z x + curv cov Y (covD cov X U) Z x
      + curv cov U (covD cov Y X) Z x = 0 := by
  have hcXY : SmoothFld (covD cov X Y) := cmd_covD cov hcov hX hY
  have hcYX : SmoothFld (covD cov Y X) := cmd_covD cov hcov hY hX
  have hcYU : SmoothFld (covD cov Y U) := cmd_covD cov hcov hY hU
  have hcUY : SmoothFld (covD cov U Y) := cmd_covD cov hcov hU hY
  have hcUX : SmoothFld (covD cov U X) := cmd_covD cov hcov hU hX
  have hcXU : SmoothFld (covD cov X U) := cmd_covD cov hcov hX hU
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
    (hU : SmoothFld U) (hX : SmoothFld X) (hY : SmoothFld Y) (hZ : SmoothFld Z)
    (x : M) :
    dRSecCov cov U X Y Z x + dRSecCov cov X Y U Z x + dRSecCov cov Y U X Z x
      = - (curv cov U (mlieBracket I X Y) Z x + curv cov X (mlieBracket I Y U) Z x
          + curv cov Y (mlieBracket I U X) Z x
          + curv cov (covD cov U X) Y Z x + curv cov (covD cov X Y) U Z x
          + curv cov (covD cov Y U) X Z x
          + curv cov X (covD cov U Y) Z x + curv cov Y (covD cov X U) Z x
          + curv cov U (covD cov Y X) Z x) := by
  have hcYZ : SmoothFld (covD cov Y Z) := cmd_covD cov hcov hY hZ
  have hcXZ : SmoothFld (covD cov X Z) := cmd_covD cov hcov hX hZ
  have hcUZ : SmoothFld (covD cov U Z) := cmd_covD cov hcov hU hZ
  have hbXY : SmoothFld (mlieBracket I X Y) := cmd_mlieBracket hX hY
  have hbYU : SmoothFld (mlieBracket I Y U) := cmd_mlieBracket hY hU
  have hbUX : SmoothFld (mlieBracket I U X) := cmd_mlieBracket hU hX
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

end Aux

end A

/-- **Second (differential) Bianchi identity** for the covariant derivative of the curvature of an arbitrary torsion-free `C^∞` connection, at a point.

PROVER NOTES. Put this result in namespace `Work.Diff.GE.react.db` so that its full name is `Work.Diff.GE.react.db.dRSecCov_bianchi`, keep the `open scoped Bundle` line, and let the file rest on the modules in `depends_on` ONLY. Do NOT import `Submission.Work.Diff.GE.bianchi_kato_defs`, `Submission.Work.Diff.GE.dRSec_bianchi`, `Submission.Work.Diff.Evol.CBDefs`, nor `Submission.Work.Diff.GE.NablaRm` / `curvbasic` / `Frame`: those two families declare the same names (`Work.Diff.GE.exists_isONFrame`, `Work.Diff.GE.rmVec_eq_curvVec`, `Work.Diff.GE.smoothExt_spec`, ...) and importing both into one environment is a hard error; the point of the present module is to be importable next to either family. Instead COPY the script: a complete proof of exactly this statement, under exactly these instance hypotheses, is in `Submission/Work/Diff/GE/dRSec_bianchi.lean` inside `section Instances` (results `curv_sub_middle_pt`, `curv_cyclic_torsion`, `covD_jacobi_pt`, `covD_commutator_pt`, `dRSecCov_cyclic_expand`, `dRSecCov_bianchi`), where `dRSecCov` there is `Work.Diff.GE.react.db.dRSecCov` here. The auxiliary results `covD_add`, `covD_sub`, `covD_sub_sub`, `covD_add_dir`, `covD_sub_dir`, `covD_commutator`, `covD_jacobi`, `cmd_covD`, `cmd_mlieBracket`, `mdiffAt_of_cmd`, `curv_eq_covD`, `covD_apply` are already proved in `dbKit`; the results of `Submission.Curvature` (`curv_add_middle`, `curv_const_smul_middle`, `curv_antisymm_apply`, `torsion_zero_bracket`) and of `Commons` (`mlieBracket_cyclic_sum`, `contMDiff_cov_apply`) are available through the kit. Keep every auxiliary declaration you add in the nested namespace `Work.Diff.GE.react.db.A` (the sibling module `Work.Diff.GE.react.dRmPhi_eq_inner_dRSec` uses `Work.Diff.GE.react.db.B`). -/
theorem dRSecCov_bianchi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (⊤ : ℕ∞)) (htor : cov.torsion = 0)
    {U X Y Z : Π y : M, TangentSpace I y}
    (hU : Work.Diff.GE.react.db.SmoothFld U) (hX : Work.Diff.GE.react.db.SmoothFld X)
    (hY : Work.Diff.GE.react.db.SmoothFld Y) (hZ : Work.Diff.GE.react.db.SmoothFld Z)
    (x : M) :
    Work.Diff.GE.react.db.dRSecCov cov U X Y Z x + Work.Diff.GE.react.db.dRSecCov cov X Y U Z x
      + Work.Diff.GE.react.db.dRSecCov cov Y U X Z x = 0 := by
  have h1 := A.dRSecCov_cyclic_expand cov hcov hU hX hY hZ x
  have h2 := A.curv_cyclic_torsion cov hcov htor hU hX hY hZ x
  rw [h1, h2, neg_zero]

end db

/-- **Second (differential) Bianchi identity** for the covariant derivative of the curvature of an arbitrary torsion-free `C^∞` connection, at a point (same statement as `Work.Diff.GE.react.db.dRSecCov_bianchi`, also available under the shorter name). -/
theorem dRSecCov_bianchi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (⊤ : ℕ∞)) (htor : cov.torsion = 0)
    {U X Y Z : Π y : M, TangentSpace I y}
    (hU : Work.Diff.GE.react.db.SmoothFld U) (hX : Work.Diff.GE.react.db.SmoothFld X)
    (hY : Work.Diff.GE.react.db.SmoothFld Y) (hZ : Work.Diff.GE.react.db.SmoothFld Z)
    (x : M) :
    Work.Diff.GE.react.db.dRSecCov cov U X Y Z x + Work.Diff.GE.react.db.dRSecCov cov X Y U Z x
      + Work.Diff.GE.react.db.dRSecCov cov Y U X Z x = 0 :=
  db.dRSecCov_bianchi cov hcov htor hU hX hY hZ x

end Work.Diff.GE.react
