import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.EvolB

namespace Work.Diff.GE.EvolB

/-! ## Auxiliary lemmas for the Ricci identity of the `Ext` pattern

These are the pieces of the argument, kept separate so that the final assembly (in the theorem
`extDD_antisymm_B`) is a short algebraic bookkeeping.  Nothing here imports a `sorry`ed module. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- `∇` is additive in its *direction* argument: `∇_{A-B} G = ∇_A G - ∇_B G`. -/
lemma covAlong_sub_dir (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (A B G : Π y : M, TangentSpace I y) :
    Work.Diff.GE.covAlong cov (A - B) G
      = Work.Diff.GE.covAlong cov A G - Work.Diff.GE.covAlong cov B G := by
  funext y
  dsimp only [Work.Diff.GE.covAlong, Pi.sub_apply]
  rw [map_sub]

/-- **Clairaut + torsion** for the `Ext` pattern: the antisymmetrised second derivative of a scalar
function in the two directions `X`, `Y` is the derivative in the direction `∇_X Y - ∇_Y X`. -/
lemma clairaut_torsion_piece
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) (htor : cov.torsion = 0)
    {f : M → ℝ} (hf : Work.Diff.GE.SmoothFunT (I := I) (M := M) f)
    {X Y : Π y : M, TangentSpace I y}
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y) (x : M) :
    mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)
      - mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
      = mvfderiv I f x ((Work.Diff.GE.covAlong cov X Y) x)
        - mvfderiv I f x ((Work.Diff.GE.covAlong cov Y X) x) := by
  haveI : IsManifold I ∞ M := inferInstance
  have hcl := Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields (I := I) hf hX hY
    (x := x)
  rw [hcl]
  have htor' : (fun y : M => cov Y y (X y) - cov X y (Y y)) = mlieBracket I X Y := by
    funext y
    exact (CovariantDerivative.torsion_eq_zero_iff (𝕜 := ℝ) (E := E) (I := I) (M := M) cov).mp htor
      ((hX y).mdifferentiableAt (by simp)) ((hY y).mdifferentiableAt (by simp))
  have hx := congrFun htor' x
  rw [← hx, map_sub, add_sub_cancel_left]

/-- The combination of fields occurring in slot `i` of `τ` is `-R(X,Y)`. -/
lemma slot_field_id (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y) :
    (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) Z
      - Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) Z)
    + (Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X Z)
      - Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y Z))
    = - LeanEval.Geometry.SphereTheorem.curv cov X Y Z := by
  haveI : IsManifold I ∞ M := inferInstance
  have hbr : mlieBracket I X Y = Work.Diff.GE.covAlong cov X Y - Work.Diff.GE.covAlong cov Y X := by
    funext y
    exact ((CovariantDerivative.torsion_eq_zero_iff (𝕜 := ℝ) (E := E) (I := I) (M := M) cov).mp htor
      ((hX y).mdifferentiableAt (by simp)) ((hY y).mdifferentiableAt (by simp))).symm
  rw [Work.Diff.GE.curv_eq_covAlong, hbr, covAlong_sub_dir]
  abel

/-- The four fields of the Ricci identity combine in slot `i` into the single field `-R(X,Y)Fᵢ`,
using the `C^∞(M)`-linearity of `τ` in that slot. -/
lemma slot_combination
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0)
    {X Y : Π y : M, TangentSpace I y}
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    {ι : Type*} [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G : Π y : M, TangentSpace I y) (c : ℝ),
      τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (F : ι → (Π y : M, TangentSpace I y)) (i : ι) (x : M) :
    τ (Function.update F i (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) (F i))) x
      - τ (Function.update F i (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) (F i))) x
      + τ (Function.update F i (Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X (F i)))) x
      - τ (Function.update F i (Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y (F i)))) x
    = - τ (Function.update F i (LeanEval.Geometry.SphereTheorem.curv cov X Y (F i))) x := by
  have hadd : ∀ (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) x
        = τ (Function.update F i G) x + τ (Function.update F i H) x :=
    fun G H => congrFun (hτ_add F i G H) x
  have hneg : ∀ (G : Π y : M, TangentSpace I y),
      τ (Function.update F i (-G)) x = - τ (Function.update F i G) x := by
    intro G
    have h := congrFun (hτ_smul F i G (-1)) x
    simpa using h
  have hsub : ∀ (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G - H)) x
        = τ (Function.update F i G) x - τ (Function.update F i H) x := by
    intro G H
    rw [sub_eq_add_neg, hadd, hneg]
    ring
  rw [← hsub, add_sub_assoc, ← hsub, ← hadd]
  rw [slot_field_id cov htor hX hY]
  exact hneg _

/-- Off the diagonal, updating the slots `k` and `i` in the two possible orders gives the same
tuple (`Function.update_comm`). -/
lemma upd_upd_comm (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [DecidableEq ι] {X Y : Π y : M, TangentSpace I y}
    {F : ι → (Π y : M, TangentSpace I y)} {i k : ι} (hik : k ≠ i) :
    Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F k) i
      = Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k := by
  dsimp only [Work.Diff.GE.upd]
  simp only [Function.update_apply, if_neg hik, if_neg (Ne.symm hik)]
  exact Function.update_comm hik _ _ _

/-- The connection/correction double sum reduces to its diagonal (via
`Work.Diff.GE.sum_univ_univ_sub_eq_diag` and `Function.update_idem`). -/
lemma upd_diag_reduce (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (F : ι → (Π y : M, TangentSpace I y)) :
    (∑ i, ∑ k, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x)
      - (∑ i, ∑ k, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x)
      = ∑ i, (τ (Function.update F i
                  (Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X (F i)))) x
              - τ (Function.update F i
                  (Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y (F i)))) x) := by
  have h1 : (∑ i, ∑ k, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x)
      - (∑ i, ∑ k, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x)
      = ∑ i, ∑ k, (τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x
                   - τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [← Finset.sum_sub_distrib])
  rw [h1, Work.Diff.GE.sum_univ_univ_sub_eq_diag]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp only [Work.Diff.GE.upd]
    simp only [Function.update_self]
    rw [Function.update_idem, Function.update_idem]
  · intro i k hki
    exact congrArg (fun G => τ G x) (upd_upd_comm cov (X := X) (Y := Y) (F := F) hki)

/-- The final algebraic assembly: with `a2 = b5`, `b2 = a5`, `a1 - b1 = a3 - b3` and the `h46`
identity, the antisymmetrised expanded difference is `s`. -/
lemma assembly {a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 s : ℝ}
    (h25 : a2 = b5) (h52 : b2 = a5) (h13 : a1 - b1 = a3 - b3)
    (h46 : a4 - b4 + (a6 - b6) = s) :
    (a1 - a2 - a3 + a4 - a5 + a6) - (b1 - b2 - b3 + b4 - b5 + b6) = s := by
  linarith

/-- The Ricci identity for the `Ext` pattern: the antisymmetrised second covariant derivative of a
field-level tensor is the algebraic curvature contraction.

This is a re-proof (in namespace `Work.Diff.GE.EvolB`) of the statement declared in
`Submission/Work/Diff/GE/extDD_antisymm.lean`, which currently carries a `sorry`; the whole
`EvolB` development rests on it, so it has to be proved without importing that file.

`Work.Diff.GE.extD cov τ x X F = mvfderiv (τ F) x (X x) - ∑ i, τ (upd cov X F i) x` is the first
covariant derivative of the field-level tensor `τ` in the direction `X`, and
`Work.Diff.GE.extDD cov τ x X Y F` is the second one (direction `Y` then `X`); the displayed
identity says that the antisymmetrisation in the two derivative directions `X`, `Y` is minus the
contraction of `τ` with the curvature `R(X,Y)` in each of the `ι` slots of `τ`.

Route (all fields smooth).  `Work.Diff.GE.extDD_expand`, already proved in
`Submission/Work/Diff/GE/ExtTensor.lean`, writes `extDD X Y F` as an explicit combination of
`mvfderiv`s; applying it to `extDD X Y F` and to `extDD Y X F` and subtracting, the terms occurring
in both cancel, and what remains is

* the Clairaut bracket `mvfderiv (fun y => mvfderiv (τ F) y (Y y)) x (X x)
  - mvfderiv (fun y => mvfderiv (τ F) y (X y)) x (Y x)`, which equals
  `mvfderiv (τ F) x (mlieBracket I X Y x)` by
  `Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields`, and, by torsion-freeness
  (`Submission.Curvature.torsion_zero_bracket`; the same argument is used in
  `Submission/Work/Diff/GE/react/dRSecCov_bianchi.lean`), equals
  `mvfderiv (τ F) x ((∇_X Y) x) - mvfderiv (τ F) x ((∇_Y X) x)`;
* the connection/correction sums, whose double sums reduce, by `Function.update_comm` and the
  PROVED `Work.Diff.GE.sum_univ_univ_sub_eq_diag`, to the diagonal
  `∑ i, (τ (F with slot i ← ∇_Y∇_X F_i) x - τ (F with slot i ← ∇_X∇_Y F_i) x)`.

Altogether the difference equals `∑ i ( τ (F with slot i ← ∇_X Y) x - τ (F with slot i ← ∇_Y X) x
+ τ (F with slot i ← ∇_Y∇_X F_i) x - τ (F with slot i ← ∇_X∇_Y F_i) x )`, and the four fields
occurring in slot `i` combine, using the `C^∞(M)`-linearity of `τ` in that slot (`hτ_add`,
`hτ_smul`) together with `Work.Diff.GE.curv_eq_covAlong` (PROVED:
`curv cov X Y Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`) and torsion-freeness, into the single field
`- curv cov X Y (F i)`, which gives the stated right-hand side.

CAUTION: do not import `Submission.Work.Diff.GE.extDD_antisymm` or
`Submission.Work.Diff.GE.cov3Rm_swap`: they contain `sorry`ed versions of the same content, so
importing them would make this result depend on `sorryAx` (the `EvolB` development must be
sorry-free). -/
theorem extDD_antisymm_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) (htor : cov.torsion = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ F : ι → (Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
        Work.Diff.GE.SmoothFunT (I := I) (M := M) (τ F))
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G : Π y : M, TangentSpace I y) (c : ℝ),
      τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (F : ι → (Π y : M, TangentSpace I y))
    (hF : Work.Diff.GE.SmoothTuple (I := I) (M := M) F) :
    Work.Diff.GE.extDD cov τ x X Y F - Work.Diff.GE.extDD cov τ x Y X F
      = - (Finset.univ.sum
            (fun i => τ (Function.update F i
              (fun y => LeanEval.Geometry.SphereTheorem.curv cov X Y (F i) y)) x)) := by
  -- The two repeated terms of the expanded difference cancel definitionally.
  have h25 : (∑ i, mvfderiv I (fun y : M => τ (Work.Diff.GE.upd cov Y F i) y) x (X x))
      = (∑ i, mvfderiv I (τ (Work.Diff.GE.upd cov Y F i)) x (X x)) := rfl
  have h52 : (∑ i, mvfderiv I (fun y : M => τ (Work.Diff.GE.upd cov X F i) y) x (Y x))
      = (∑ i, mvfderiv I (τ (Work.Diff.GE.upd cov X F i)) x (Y x)) := rfl
  -- Clairaut + torsion: the antisymmetrised second `mvfderiv` is `mvfderiv` in `∇_X Y - ∇_Y X`.
  have h13 := clairaut_torsion_piece cov hcov htor (hτ F hF) hX hY x
  have hP4 : (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x)
      - (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x)
      = ∑ i, (τ (Function.update F i
                  (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) (F i))) x
              - τ (Function.update F i
                  (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) (F i))) x) := by
    rw [← Finset.sum_sub_distrib]
  -- The remaining terms: the connection/correction sums, reduced to the diagonal, combine slot by
  -- slot into `-R(X,Y)`.
  have h46 : (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x)
      - (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x)
      + ((∑ i, ∑ k, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x)
         - (∑ i, ∑ k, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x))
      = - (Finset.univ.sum (fun i => τ (Function.update F i
          (fun y => LeanEval.Geometry.SphereTheorem.curv cov X Y (F i) y)) x)) := by
    have hsum : (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x)
        - (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x)
        + ((∑ i, ∑ k, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x)
           - (∑ i, ∑ k, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x))
        = ∑ i, ((τ (Function.update F i
                      (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) (F i))) x
                   - τ (Function.update F i
                      (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) (F i))) x)
                + (τ (Function.update F i
                      (Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X (F i)))) x
                   - τ (Function.update F i
                      (Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y (F i)))) x)) := by
      rw [hP4, upd_diag_reduce, ← Finset.sum_add_distrib]
    rw [hsum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← add_sub_assoc]
    exact slot_combination cov htor hX hY τ hτ_add hτ_smul F i x
  rw [Work.Diff.GE.extDD_expand cov hcov τ hτ x X Y hY F hF,
      Work.Diff.GE.extDD_expand cov hcov τ hτ x Y X hX F hF]
  exact assembly h25 h52 h13 h46

end Work.Diff.GE.EvolB

/-! The file above carries a doubly nested `namespace Work.Diff.GE.EvolB` (an artefact of how the
statement was generated), so the theorem it proves is named
`Work.Diff.GE.EvolB.Work.Diff.GE.EvolB.extDD_antisymm_B`.  The rest of the `EvolB` development
refers to it under the natural name `Work.Diff.GE.EvolB.extDD_antisymm_B`, so we record that name
as well (same statement, one-line application). -/

/-- The Ricci identity for the `Ext` pattern, under the natural name
`Work.Diff.GE.EvolB.extDD_antisymm_B`. -/
theorem extDD_antisymm_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) (htor : cov.torsion = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ F : ι → (Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
        Work.Diff.GE.SmoothFunT (I := I) (M := M) (τ F))
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G : Π y : M, TangentSpace I y) (c : ℝ),
      τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (F : ι → (Π y : M, TangentSpace I y))
    (hF : Work.Diff.GE.SmoothTuple (I := I) (M := M) F) :
    Work.Diff.GE.extDD cov τ x X Y F - Work.Diff.GE.extDD cov τ x Y X F
      = - (Finset.univ.sum
            (fun i => τ (Function.update F i
              (fun y => LeanEval.Geometry.SphereTheorem.curv cov X Y (F i) y)) x)) :=
  _root_.Work.Diff.GE.EvolB.Work.Diff.GE.EvolB.extDD_antisymm_B
    cov hcov htor τ hτ hτ_add hτ_smul x X Y hX hY F hF

end Work.Diff.GE.EvolB
