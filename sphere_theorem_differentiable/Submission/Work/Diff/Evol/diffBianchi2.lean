import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.Evol.Deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.Diff.Evol

/-- **Second-order form of the differential Bianchi identity.**  Given the differential Bianchi
identity `h1` *at every point* (quantified over all `y : M`; it is `Work.Diff.Evol.differential_bianchi`,
which is available in the other import family, so do not import it here — take it as a hypothesis),
conclude that `∇²Rm` is alternating in the triple (inner differentiation slot, first slot, second
slot): `cov2Rm g x v v a b c d + cov2Rm g x v a b v c d + cov2Rm g x v b v a c d = 0`.

Both reviewers verified the identity index-by-index; it is a true consequence of the differential
Bianchi identity and NOT of the algebraic symmetries alone.

PROOF: put `Φ y := covRm g y (V y)(A y)(B y)(C y)(D y) + covRm g y (A y)(B y)(V y)(C y)(D y) +
covRm g y (B y)(V y)(A y)(C y)(D y)` with `V := smoothExt x v`, `A := smoothExt x a`,
`B := smoothExt x b`, `C := smoothExt x c`, `D := smoothExt x d`.  `Φ y = 0` for every `y` by `h1`, so
`mvfderiv I Φ x v = 0` (`Work.Diff.GE.mvfderiv_congr_eventuallyEq` against the zero function,
`mvfderiv_const`; add the three pieces with `mvfderiv_add`, needing
`Work.Diff.GE.covRm_fields_smooth`).  Expand each summand with the definition of
`Work.Diff.GE.cov2RmExt` (`simp only [Work.Diff.GE.cov2RmExt]`: the five corrections match the five
arguments of `covRm`), and cancel the resulting 15 correction terms, grouped by the differentiated
field: for each field `Z` the three occurrences are a cyclic instance of `h1`, hence vanish.  Finally
identify `Work.Diff.GE.cov2RmExt g x v V A B C D = Submission.Diff.cov2Rm g x v v a b c d` (`rfl`), and
rewrite the other two leading terms with `Work.Diff.GE.cov2RmExt_bind_*` plus
`Submission.Diff.smoothExt_apply` (they are `cov2RmExt g x v A B V C D` and
`cov2RmExt g x v B V A C D`). -/
theorem diffBianchi2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (h1 : ∀ (y : M) (v a b c d : TangentSpace I y),
      Submission.Diff.covRm g y v a b c d + Submission.Diff.covRm g y a b v c d
        + Submission.Diff.covRm g y b v a c d = 0)
    (x : M) (v a b c d : TangentSpace I x) :
    Submission.Diff.cov2Rm g x v v a b c d + Submission.Diff.cov2Rm g x v a b v c d
      + Submission.Diff.cov2Rm g x v b v a c d = 0 := by
  -- the five smooth extension fields
  set V : Π y : M, TangentSpace I y := smoothExt x v with hVdef
  set A : Π y : M, TangentSpace I y := smoothExt x a with hAdef
  set B : Π y : M, TangentSpace I y := smoothExt x b with hBdef
  set C : Π y : M, TangentSpace I y := smoothExt x c with hCdef
  set D : Π y : M, TangentSpace I y := smoothExt x d with hDdef
  have hVsm : CMDiff ∞ (T% V) := by rw [hVdef]; exact Work.Diff.GE.smoothExt_cmdiff x v
  have hAsm : CMDiff ∞ (T% A) := by rw [hAdef]; exact Work.Diff.GE.smoothExt_cmdiff x a
  have hBsm : CMDiff ∞ (T% B) := by rw [hBdef]; exact Work.Diff.GE.smoothExt_cmdiff x b
  have hCsm : CMDiff ∞ (T% C) := by rw [hCdef]; exact Work.Diff.GE.smoothExt_cmdiff x c
  have hDsm : CMDiff ∞ (T% D) := by rw [hDdef]; exact Work.Diff.GE.smoothExt_cmdiff x d
  -- the three summands of `Φ` are smooth
  have hS1 : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) :=
    Work.Diff.GE.covRm_fields_smooth hLC hVsm hAsm hBsm hCsm hDsm
  have hS2 : CMDiff ∞ (fun y : M => covRm g y (A y) (B y) (V y) (C y) (D y)) :=
    Work.Diff.GE.covRm_fields_smooth hLC hAsm hBsm hVsm hCsm hDsm
  have hS3 : CMDiff ∞ (fun y : M => covRm g y (B y) (V y) (A y) (C y) (D y)) :=
    Work.Diff.GE.covRm_fields_smooth hLC hBsm hVsm hAsm hCsm hDsm
  -- each summand: derivative = `cov2RmExt` + the five tensorialising corrections
  have hd1 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x v
      = Work.Diff.GE.cov2RmExt g x v V A B C D
        + covRm g x (lcOf g V x v) (A x) (B x) (C x) (D x)
        + covRm g x (V x) (lcOf g A x v) (B x) (C x) (D x)
        + covRm g x (V x) (A x) (lcOf g B x v) (C x) (D x)
        + covRm g x (V x) (A x) (B x) (lcOf g C x v) (D x)
        + covRm g x (V x) (A x) (B x) (C x) (lcOf g D x v) := by
    rw [Work.Diff.GE.cov2RmExt]; ring
  have hd2 : mvfderiv I (fun y : M => covRm g y (A y) (B y) (V y) (C y) (D y)) x v
      = Work.Diff.GE.cov2RmExt g x v A B V C D
        + covRm g x (lcOf g A x v) (B x) (V x) (C x) (D x)
        + covRm g x (A x) (lcOf g B x v) (V x) (C x) (D x)
        + covRm g x (A x) (B x) (lcOf g V x v) (C x) (D x)
        + covRm g x (A x) (B x) (V x) (lcOf g C x v) (D x)
        + covRm g x (A x) (B x) (V x) (C x) (lcOf g D x v) := by
    rw [Work.Diff.GE.cov2RmExt]; ring
  have hd3 : mvfderiv I (fun y : M => covRm g y (B y) (V y) (A y) (C y) (D y)) x v
      = Work.Diff.GE.cov2RmExt g x v B V A C D
        + covRm g x (lcOf g B x v) (V x) (A x) (C x) (D x)
        + covRm g x (B x) (lcOf g V x v) (A x) (C x) (D x)
        + covRm g x (B x) (V x) (lcOf g A x v) (C x) (D x)
        + covRm g x (B x) (V x) (A x) (lcOf g C x v) (D x)
        + covRm g x (B x) (V x) (A x) (C x) (lcOf g D x v) := by
    rw [Work.Diff.GE.cov2RmExt]; ring
  -- the derivative of the sum is the sum of the derivatives
  have hsum3 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)
        + covRm g y (A y) (B y) (V y) (C y) (D y)
        + covRm g y (B y) (V y) (A y) (C y) (D y)) x v
      = mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x v
        + mvfderiv I (fun y : M => covRm g y (A y) (B y) (V y) (C y) (D y)) x v
        + mvfderiv I (fun y : M => covRm g y (B y) (V y) (A y) (C y) (D y)) x v := by
    rw [show (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)
            + covRm g y (A y) (B y) (V y) (C y) (D y)
            + covRm g y (B y) (V y) (A y) (C y) (D y))
        = (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y))
          + (fun y : M => covRm g y (A y) (B y) (V y) (C y) (D y))
          + (fun y : M => covRm g y (B y) (V y) (A y) (C y) (D y)) from rfl]
    rw [mvfderiv_add (g := (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y))
            + (fun y : M => covRm g y (A y) (B y) (V y) (C y) (D y)))
          (g' := fun y : M => covRm g y (B y) (V y) (A y) (C y) (D y))
          ((hS1.mdifferentiableAt (by simp)).add (hS2.mdifferentiableAt (by simp)))
          (hS3.mdifferentiableAt (by simp)),
        mvfderiv_add (g := fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y))
          (g' := fun y : M => covRm g y (A y) (B y) (V y) (C y) (D y))
          (hS1.mdifferentiableAt (by simp)) (hS2.mdifferentiableAt (by simp))]
    simp
  -- `Φ` vanishes identically, so its derivative along `v` is zero
  have hΦ0 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)
        + covRm g y (A y) (B y) (V y) (C y) (D y)
        + covRm g y (B y) (V y) (A y) (C y) (D y)) x v = 0 := by
    have hzero : (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)
          + covRm g y (A y) (B y) (V y) (C y) (D y)
          + covRm g y (B y) (V y) (A y) (C y) (D y)) =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) :=
      Filter.Eventually.of_forall (fun y => h1 y (V y) (A y) (B y) (C y) (D y))
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hzero, mvfderiv_const]
    rfl
  -- the fifteen corrections cancel, grouped by the differentiated field (cyclic `h1` at `x`)
  have hGV : covRm g x (lcOf g V x v) (A x) (B x) (C x) (D x)
      + covRm g x (A x) (B x) (lcOf g V x v) (C x) (D x)
      + covRm g x (B x) (lcOf g V x v) (A x) (C x) (D x) = 0 :=
    h1 x (lcOf g V x v) (A x) (B x) (C x) (D x)
  have hGA : covRm g x (V x) (lcOf g A x v) (B x) (C x) (D x)
      + covRm g x (lcOf g A x v) (B x) (V x) (C x) (D x)
      + covRm g x (B x) (V x) (lcOf g A x v) (C x) (D x) = 0 :=
    h1 x (V x) (lcOf g A x v) (B x) (C x) (D x)
  have hGB : covRm g x (V x) (A x) (lcOf g B x v) (C x) (D x)
      + covRm g x (A x) (lcOf g B x v) (V x) (C x) (D x)
      + covRm g x (lcOf g B x v) (V x) (A x) (C x) (D x) = 0 :=
    h1 x (V x) (A x) (lcOf g B x v) (C x) (D x)
  have hGC : covRm g x (V x) (A x) (B x) (lcOf g C x v) (D x)
      + covRm g x (A x) (B x) (V x) (lcOf g C x v) (D x)
      + covRm g x (B x) (V x) (A x) (lcOf g C x v) (D x) = 0 :=
    h1 x (V x) (A x) (B x) (lcOf g C x v) (D x)
  have hGD : covRm g x (V x) (A x) (B x) (C x) (lcOf g D x v)
      + covRm g x (A x) (B x) (V x) (C x) (lcOf g D x v)
      + covRm g x (B x) (V x) (A x) (C x) (lcOf g D x v) = 0 :=
    h1 x (V x) (A x) (B x) (C x) (lcOf g D x v)
  -- identify the three leading terms with the frozen `Submission.Diff.cov2Rm` components
  have hL1 : Submission.Diff.cov2Rm g x v v a b c d = Work.Diff.GE.cov2RmExt g x v V A B C D := by
    rw [hVdef, hAdef, hBdef, hCdef, hDdef]
    simp only [Submission.Diff.cov2Rm, Work.Diff.GE.cov2RmExt, Work.Diff.GE.smoothExt_apply]
  have hL2 : Submission.Diff.cov2Rm g x v a b v c d = Work.Diff.GE.cov2RmExt g x v A B V C D := by
    rw [hVdef, hAdef, hBdef, hCdef, hDdef]
    simp only [Submission.Diff.cov2Rm, Work.Diff.GE.cov2RmExt, Work.Diff.GE.smoothExt_apply]
  have hL3 : Submission.Diff.cov2Rm g x v b v a c d = Work.Diff.GE.cov2RmExt g x v B V A C D := by
    rw [hVdef, hAdef, hBdef, hCdef, hDdef]
    simp only [Submission.Diff.cov2Rm, Work.Diff.GE.cov2RmExt, Work.Diff.GE.smoothExt_apply]
  rw [hL1, hL2, hL3]
  linarith [hΦ0, hsum3, hd1, hd2, hd3, hGV, hGA, hGB, hGC, hGD]

end Work.Diff.Evol
