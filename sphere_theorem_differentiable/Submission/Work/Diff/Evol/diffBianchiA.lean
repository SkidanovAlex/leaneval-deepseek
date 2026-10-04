import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.react.dbKit
import Submission.Work.Diff.GE.react.dRSecCov_bianchi
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]

/-- **The `Ext` pattern of `∇Rm` is the pairing of `dRSec`** (chain-neutral version).

For arbitrary smooth fields `A, B, C, D`, the `Ext` pattern `dRmPhi g x v A B C D` of
`Work.Diff.GE.react.db` (the derivative of `y ↦ rmP g y (A y) (B y) (C y) (D y)` along `v`, with the
four connection corrections) equals `⟪(∇_v R)(A,B)D, C x⟫`, the pairing of the section
`Work.Diff.GE.react.db.dRSec g (smoothExt x v) A B D` with `C` at `x`. -/
theorem dRmPhiA_eq_inner_dRSec
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y)
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) :
    Work.Diff.GE.react.db.dRmPhi g x v A B C D
      = g.inner x (Work.Diff.GE.react.db.dRSec g (smoothExt x v) A B D x) (C x) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  obtain ⟨hVsm, hVx⟩ := Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x v
  have hcurvV : CMDiff ∞ (T% (curv (lcOf g) A B D)) :=
    Work.Diff.GE.react.db.contMDiff_curv_fields (lcOf g) hcov hA hB hD
  -- the integrand of the `Ext` pattern is the pairing of the curvature section with `C`
  have hbody : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => Inner.inner ℝ (curv (lcOf g) A B D y) (C y) := by
    funext y
    show Inner.inner ℝ (rmVec (lcOf g) y (A y) (B y) (D y)) (C y)
      = Inner.inner ℝ (curv (lcOf g) A B D y) (C y)
    rw [Work.Diff.GE.react.db.rmVec_eq_curvVec (lcOf g) hcov y (A y) (B y) (D y)]
    rw [Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl]
  -- metric compatibility splits the derivative
  have hmvf : mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v
      = Inner.inner ℝ (lcOf g (curv (lcOf g) A B D) x v) (C x)
        + Inner.inner ℝ (curv (lcOf g) A B D x) (lcOf g C x v) := by
    rw [hbody]
    exact hmet (curv (lcOf g) A B D) C hcurvV hC x v
  -- `covDir g (smoothExt x v) ·` at `x` is `∇_v ·`, and it is a smooth field
  have hdvA : Work.Diff.GE.react.db.covDir g (smoothExt x v) A x = lcOf g A x v := by
    show lcOf g A x (smoothExt x v x) = lcOf g A x v
    rw [hVx]
  have hdvB : Work.Diff.GE.react.db.covDir g (smoothExt x v) B x = lcOf g B x v := by
    show lcOf g B x (smoothExt x v x) = lcOf g B x v
    rw [hVx]
  have hdvD : Work.Diff.GE.react.db.covDir g (smoothExt x v) D x = lcOf g D x v := by
    show lcOf g D x (smoothExt x v x) = lcOf g D x v
    rw [hVx]
  have hCDA : CMDiff ∞ (T% (Work.Diff.GE.react.db.covDir g (smoothExt x v) A)) := by
    show CMDiff ∞ (T% (fun y : M => lcOf g A y (smoothExt x v y)))
    exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hA hVsm
  have hCDB : CMDiff ∞ (T% (Work.Diff.GE.react.db.covDir g (smoothExt x v) B)) := by
    show CMDiff ∞ (T% (fun y : M => lcOf g B y (smoothExt x v y)))
    exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hB hVsm
  have hCDD : CMDiff ∞ (T% (Work.Diff.GE.react.db.covDir g (smoothExt x v) D)) := by
    show CMDiff ∞ (T% (fun y : M => lcOf g D y (smoothExt x v y)))
    exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hD hVsm
  -- the four corrections, rewritten as pairings of `curv` terms
  have hC1 : rmP g x (lcOf g A x v) (B x) (C x) (D x)
      = Inner.inner ℝ (curv (lcOf g) (Work.Diff.GE.react.db.covDir g (smoothExt x v) A) B D x)
          (C x) := by
    show Inner.inner ℝ (rmVec (lcOf g) x (lcOf g A x v) (B x) (D x)) (C x) = _
    rw [Work.Diff.GE.react.db.rmVec_eq_curvVec (lcOf g) hcov x (lcOf g A x v) (B x) (D x)]
    rw [← Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hCDA hB hD hdvA rfl rfl]
  have hC2 : rmP g x (A x) (lcOf g B x v) (C x) (D x)
      = Inner.inner ℝ (curv (lcOf g) A (Work.Diff.GE.react.db.covDir g (smoothExt x v) B) D x)
          (C x) := by
    show Inner.inner ℝ (rmVec (lcOf g) x (A x) (lcOf g B x v) (D x)) (C x) = _
    rw [Work.Diff.GE.react.db.rmVec_eq_curvVec (lcOf g) hcov x (A x) (lcOf g B x v) (D x)]
    rw [← Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hCDB hD rfl hdvB rfl]
  have hC3 : rmP g x (A x) (B x) (lcOf g C x v) (D x)
      = Inner.inner ℝ (curv (lcOf g) A B D x) (lcOf g C x v) := by
    show Inner.inner ℝ (rmVec (lcOf g) x (A x) (B x) (D x)) (lcOf g C x v) = _
    rw [Work.Diff.GE.react.db.rmVec_eq_curvVec (lcOf g) hcov x (A x) (B x) (D x),
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl]
  have hC4 : rmP g x (A x) (B x) (C x) (lcOf g D x v)
      = Inner.inner ℝ (curv (lcOf g) A B (Work.Diff.GE.react.db.covDir g (smoothExt x v) D) x)
          (C x) := by
    show Inner.inner ℝ (rmVec (lcOf g) x (A x) (B x) (lcOf g D x v)) (C x) = _
    rw [Work.Diff.GE.react.db.rmVec_eq_curvVec (lcOf g) hcov x (A x) (B x) (lcOf g D x v)]
    rw [← Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hCDD rfl rfl hdvD]
  -- the section `dRSec` unfolds, and the pairing is additive in its first slot
  have hds : Inner.inner ℝ (Work.Diff.GE.react.db.dRSec g (smoothExt x v) A B D x) (C x)
      = Inner.inner ℝ (lcOf g (curv (lcOf g) A B D) x (smoothExt x v x)) (C x)
        - Inner.inner ℝ (curv (lcOf g) (Work.Diff.GE.react.db.covDir g (smoothExt x v) A) B D x)
            (C x)
        - Inner.inner ℝ (curv (lcOf g) A (Work.Diff.GE.react.db.covDir g (smoothExt x v) B) D x)
            (C x)
        - Inner.inner ℝ (curv (lcOf g) A B (Work.Diff.GE.react.db.covDir g (smoothExt x v) D) x)
            (C x) := by
    rw [Work.Diff.GE.react.db.dRSec]
    simp only [inner_sub_left]
  rw [Work.Diff.GE.react.db.dRmPhi, hmvf, hC1, hC2, hC3, hC4]
  rw [show g.inner x (Work.Diff.GE.react.db.dRSec g (smoothExt x v) A B D x) (C x)
      = Inner.inner ℝ (Work.Diff.GE.react.db.dRSec g (smoothExt x v) A B D x) (C x) from rfl]
  rw [hds, hVx]
  linarith

/-- **`covRm` is `⟪(∇_U R)(X,Y)D, C⟫`** (chain-neutral version).  Here
`Work.Diff.GE.react.db.dRSec g U X Y Z x` is the section
`(∇_U R)(X,Y)Z = ∇_U(R(X,Y)Z) − R(∇_U X,Y)Z − R(X,∇_U Y)Z − R(X,Y)∇_U Z` for the Levi-Civita
connection of `g`, so the statement says that the frozen `covRm g x v a b c d` (the component
`(∇_v Rm)(a,b,c,d)` of `∇Rm`, with `Rm(a,b,c,d) = ⟪R(a,b)d, c⟫`) is the pairing of `(∇_v R)(a,b)d`
with `c`. -/
theorem covRm_eq_dRSecA_smoothExt
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    covRm g x v a b c d
      = g.inner x
          (Work.Diff.GE.react.db.dRSec g (smoothExt x v) (smoothExt x a) (smoothExt x b)
            (smoothExt x d) x)
          (smoothExt x c x) := by
  rw [Work.Diff.GE.react.db.covRm_eq_dRmPhi g x v a b c d]
  exact dRmPhiA_eq_inner_dRSec hLC g x v (smoothExt x a) (smoothExt x b) (smoothExt x c)
    (smoothExt x d)
    (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x a).1
    (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x b).1
    (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x c).1
    (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x d).1

/-- **Second (differential) Bianchi identity, chain-A-compatible version.**
`(∇_v Rm)(a,b,c,d) + (∇_a Rm)(b,v,c,d) + (∇_b Rm)(v,a,c,d) = 0` for the Levi-Civita connection of a
smooth metric. -/
theorem diffBianchiA
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Submission.Diff.covRm g x v a b c d + Submission.Diff.covRm g x a b v c d
      + Submission.Diff.covRm g x b v a c d = 0 := by
  obtain ⟨hcov0, htor, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have key : ∀ v' a' b' c' d' : TangentSpace I x,
      covRm g x v' a' b' c' d'
        = g.inner x (Work.Diff.GE.react.db.dRSec g (smoothExt x v') (smoothExt x a')
            (smoothExt x b') (smoothExt x d') x) (smoothExt x c' x) :=
    fun v' a' b' c' d' => covRm_eq_dRSecA_smoothExt hLC g x v' a' b' c' d'
  rw [key v a b c d, key a b v c d, key b v a c d]
  have hsum : Work.Diff.GE.react.db.dRSec g (smoothExt x v) (smoothExt x a) (smoothExt x b)
        (smoothExt x d) x
      + Work.Diff.GE.react.db.dRSec g (smoothExt x a) (smoothExt x b) (smoothExt x v)
        (smoothExt x d) x
      + Work.Diff.GE.react.db.dRSec g (smoothExt x b) (smoothExt x v) (smoothExt x a)
        (smoothExt x d) x
      = 0 :=
    Work.Diff.GE.react.db.dRSecCov_bianchi (lcOf g) hcov htor
      (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x v).1
      (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x a).1
      (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x b).1
      (Work.Diff.GE.react.db.smoothExt_spec (I := I) (M := M) x d).1 x
  have hlin := congrArg (fun z : TangentSpace I x => g.inner x z (smoothExt x c x)) hsum
  simpa only [map_add, map_zero, add_apply, zero_apply] using hlin

end Work.Diff.Evol
