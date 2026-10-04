import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.GE.dRSec_bianchi
import Submission.Work.Diff.Evol.CBDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The differential (second) Bianchi identity for the curvature of a smooth metric

`Work.Diff.Evol.differential_bianchi` : for the Levi-Civita connection of a smooth metric `g`,
`(∇_v Rm)(a,b,c,d) + (∇_a Rm)(b,v,c,d) + (∇_b Rm)(v,a,c,d) = 0`, where `covRm` is the frozen
`(0,5)`-component `(∇_v Rm)(a,b,c,d)` of `∇Rm` (`Submission/Diff/Grad.lean`).

The proof is short once one knows that `covRm` is the pairing `⟪(∇_U R)(X,Y)D, C⟫` of the section
`Work.Diff.GE.dRSec` of `Submission/Work/Diff/GE/bianchi_kato_defs.lean`
(`covRm_eq_dRSec_smoothExt` below): the three terms become the cyclic sum of `dRSec`, which vanishes
by the second Bianchi identity `Work.Diff.GE.dRSec_bianchi` (proved in
`Submission/Work/Diff/GE/dRSec_bianchi.lean`), and the pairing is linear in its first slot.
-/

set_option linter.style.haveILetI false

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helper

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- **`covRm` is `⟪(∇_U R)(X,Y)D, C⟫`.**  The frozen `covRm g x v a b c d` (the component
`(∇_v Rm)(a,b,c,d)` of `∇Rm`, with `Rm(a,b,c,d) = ⟪R(a,b)d, c⟫`) is the pairing of `(∇_v R)(a,b)d`
with `c`, where `(∇_U R)(X,Y)Z` is the section `Work.Diff.GE.dRSec g U X Y Z` of the Levi-Civita
connection of `g`.

Proof: unfold `covRm`; rewrite the function under `mvfderiv` as `y ↦ ⟪R(A,B)D(y), C y⟫` with
`A = smoothExt x a`, `B = smoothExt x b`, `C = smoothExt x c`, `D = smoothExt x d`
(`Work.Diff.GE.rmVec_eq_curvVec_lcOf` + `Submission.CurvatureVec.curvVec_eq`, and
`Work.Diff.Evol.contMDiff_curv_fields` for the smoothness of `y ↦ R(A,B)D(y)`), use the frozen
metric compatibility `IsMetricCompatible (lcOf g)` to differentiate the pairing, cancel the
`⟪R(A,B)D, ∇_v C⟫` term against the third connection correction, and identify the remaining three
corrections with the three `curv` terms of `dRSec` (`conv_lhs` + `hSc.2` places the pairing slot in
the same normal form on both sides, after which the identity is a polynomial identity). -/
theorem covRm_eq_dRSec_smoothExt
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    covRm g x v a b c d
      = g.inner x
          (Work.Diff.GE.dRSec g (smoothExt x v) (smoothExt x a) (smoothExt x b)
            (smoothExt x d) x)
          (smoothExt x c x) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov0, -, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  have hSv := (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x v)
  have hSa := (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x a)
  have hSb := (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x b)
  have hSc := (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x c)
  have hSd := (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x d)
  -- `y ↦ R(A,B)D(y)` is a smooth section
  have hcurv : CMDiff ∞ (T% (fun y : M => curv (lcOf g) (smoothExt x a) (smoothExt x b)
      (smoothExt x d) y)) :=
    Work.Diff.Evol.contMDiff_curv_fields (lcOf g) hcov hSa.1 hSb.1 hSd.1
  -- the function under `mvfderiv` is the pairing of two smooth sections
  have hbody : (fun y : M => rmP g y ((smoothExt x a) y) ((smoothExt x b) y)
        ((smoothExt x c) y) ((smoothExt x d) y))
      = fun y : M => g.inner y (curv (lcOf g) (smoothExt x a) (smoothExt x b) (smoothExt x d) y)
          ((smoothExt x c) y) := by
    funext y
    show g.inner y (rmVec (lcOf g) y ((smoothExt x a) y) ((smoothExt x b) y) ((smoothExt x d) y))
        ((smoothExt x c) y) = _
    rw [Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov y ((smoothExt x a) y) ((smoothExt x b) y)
      ((smoothExt x d) y)]
    exact congrArg (fun z => g.inner y z ((smoothExt x c) y))
      (Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hSa.1 hSb.1 hSd.1 rfl rfl rfl)
  -- `y ↦ curv (lcOf g) A B D y` and `covDir g (smoothExt x v) ·` agree definitionally
  have hlam : (lcOf g (fun y : M => curv (lcOf g) (smoothExt x a) (smoothExt x b)
        (smoothExt x d) y) x v)
      = lcOf g (curv (lcOf g) (smoothExt x a) (smoothExt x b) (smoothExt x d)) x v := rfl
  -- the Leibniz rule for the pairing (metric compatibility)
  have hmvf : mvfderiv I (fun y : M => rmP g y ((smoothExt x a) y) ((smoothExt x b) y)
        ((smoothExt x c) y) ((smoothExt x d) y)) x v
      = g.inner x (lcOf g (fun y : M => curv (lcOf g) (smoothExt x a) (smoothExt x b)
            (smoothExt x d) y) x v) ((smoothExt x c) x)
        + g.inner x (curv (lcOf g) (smoothExt x a) (smoothExt x b) (smoothExt x d) x)
          (lcOf g (smoothExt x c) x v) := by
    rw [hbody]
    exact hmet (fun y : M => curv (lcOf g) (smoothExt x a) (smoothExt x b) (smoothExt x d) y)
      (smoothExt x c) hcurv hSc.1 x v
  -- smoothness of the three `∇_v (smoothExt x ·)` fields
  have hcd : CMDiff ∞ (T% (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x a))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply (lcOf g)
      hcov hSa.1 hSv.1
  have hcdb : CMDiff ∞ (T% (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x b))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply (lcOf g)
      hcov hSb.1 hSv.1
  have hcdd : CMDiff ∞ (T% (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x d))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply (lcOf g)
      hcov hSd.1 hSv.1
  -- correction 1 : `R(∇_v A, B)D`
  have key1 : rmP g x ((lcOf g) (smoothExt x a) x v) b c d
      = g.inner x (curv (lcOf g) (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x a))
          (smoothExt x b) (smoothExt x d) x) ((smoothExt x c) x) := by
    have hXx : (lcOf g) (smoothExt x a) x ((smoothExt x v) x) = (lcOf g) (smoothExt x a) x v := by
      rw [hSv.2]
    have hcv : Submission.CurvatureVec.curvVec (lcOf g) x ((lcOf g) (smoothExt x a) x v) b d
        = curv (lcOf g) (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x a))
            (smoothExt x b) (smoothExt x d) x :=
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hcd hSb.1 hSd.1 hXx hSb.2 hSd.2
    rw [Work.Diff.GE.rmP_eq g hcov x ((lcOf g) (smoothExt x a) x v) b c d, hcv]
    conv_lhs => rw [← hSc.2]
  -- correction 2 : `R(A, ∇_v B)D`
  have key2 : rmP g x a ((lcOf g) (smoothExt x b) x v) c d
      = g.inner x (curv (lcOf g) (smoothExt x a)
          (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x b))
          (smoothExt x d) x) ((smoothExt x c) x) := by
    have hXx : (lcOf g) (smoothExt x b) x ((smoothExt x v) x) = (lcOf g) (smoothExt x b) x v := by
      rw [hSv.2]
    have hcv : Submission.CurvatureVec.curvVec (lcOf g) x a ((lcOf g) (smoothExt x b) x v) d
        = curv (lcOf g) (smoothExt x a)
            (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x b)) (smoothExt x d) x :=
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hSa.1 hcdb hSd.1 hSa.2 hXx hSd.2
    rw [Work.Diff.GE.rmP_eq g hcov x a ((lcOf g) (smoothExt x b) x v) c d, hcv]
    conv_lhs => rw [← hSc.2]
  -- the cancellation of the pairing-slot term `⟪R(A,B)D, ∇_v C⟫`
  have keyd : g.inner x (curv (lcOf g) (smoothExt x a) (smoothExt x b) (smoothExt x d) x)
        ((lcOf g) (smoothExt x c) x v)
      = rmP g x a b ((lcOf g) (smoothExt x c) x v) d := by
    have hcv : Submission.CurvatureVec.curvVec (lcOf g) x a b d
        = curv (lcOf g) (smoothExt x a) (smoothExt x b) (smoothExt x d) x :=
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hSa.1 hSb.1 hSd.1 hSa.2 hSb.2 hSd.2
    rw [Work.Diff.GE.rmP_eq g hcov x a b ((lcOf g) (smoothExt x c) x v) d, hcv]
  -- correction 4 : `R(A,B)(∇_v D)`
  have key4 : rmP g x a b c ((lcOf g) (smoothExt x d) x v)
      = g.inner x (curv (lcOf g) (smoothExt x a) (smoothExt x b)
          (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x d)) x) ((smoothExt x c) x) := by
    have hXx : (lcOf g) (smoothExt x d) x ((smoothExt x v) x) = (lcOf g) (smoothExt x d) x v := by
      rw [hSv.2]
    have hcv : Submission.CurvatureVec.curvVec (lcOf g) x a b ((lcOf g) (smoothExt x d) x v)
        = curv (lcOf g) (smoothExt x a) (smoothExt x b)
            (Work.Diff.GE.covDir g (smoothExt x v) (smoothExt x d)) x :=
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hSa.1 hSb.1 hcdd hSa.2 hSb.2 hXx
    rw [Work.Diff.GE.rmP_eq g hcov x a b c ((lcOf g) (smoothExt x d) x v), hcv]
    conv_lhs => rw [← hSc.2]
  -- both sides are now polynomial identities in the same atoms
  simp only [covRm, Work.Diff.GE.dRSec]
  rw [hmvf, map_sub, sub_apply, map_sub, sub_apply, map_sub, sub_apply]
  rw [key1, key2, key4, keyd, hSv.2, hlam]
  ring

end Helper

/-- **Differential (second) Bianchi identity.**  For the Levi-Civita connection of a smooth metric,
`(∇_v Rm)(a,b,c,d) + (∇_a Rm)(b,v,c,d) + (∇_b Rm)(v,a,c,d) = 0`; this is the cyclic sum
`(∇_v R)(a,b) + (∇_a R)(b,v) + (∇_b R)(v,a) = 0` of the second Bianchi identity, paired with `c`
and evaluated on `d`. -/
theorem differential_bianchi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    covRm g x v a b c d + covRm g x a b v c d + covRm g x b v a c d = 0 := by
  obtain ⟨hcov0, htor, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  have key : ∀ v' a' b' c' d' : TangentSpace I x,
      covRm g x v' a' b' c' d'
        = g.inner x (Work.Diff.GE.dRSec g (smoothExt x v') (smoothExt x a') (smoothExt x b')
            (smoothExt x d') x) (smoothExt x c' x) :=
    fun v' a' b' c' d' => covRm_eq_dRSec_smoothExt hLC g x v' a' b' c' d'
  rw [key v a b c d, key a b v c d, key b v a c d]
  have hsum : Work.Diff.GE.dRSec g (smoothExt x v) (smoothExt x a) (smoothExt x b)
        (smoothExt x d) x
      + Work.Diff.GE.dRSec g (smoothExt x a) (smoothExt x b) (smoothExt x v) (smoothExt x d) x
      + Work.Diff.GE.dRSec g (smoothExt x b) (smoothExt x v) (smoothExt x a) (smoothExt x d) x
      = 0 :=
    Work.Diff.GE.dRSec_bianchi g hcov htor (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x v).1
      (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x a).1
      (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x b).1
      (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x d).1 x
  have hlin := congrArg (fun z : TangentSpace I x => g.inner x z (smoothExt x c x)) hsum
  simpa only [map_add, map_zero, add_apply, zero_apply] using hlin

end Work.Diff.Evol
