import Mathlib
import Submission.Work.Diff.GE.swap_defs
import Submission.Work.Diff.GE.cov2Rm_ricci_defs
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.kato_covRm_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci identity for `∇²Rm`, assembled from the generic `Ext`-pattern lemma

`Work.Diff.GE.cov2Rm_ricci_pt` (equivalently `Work.Diff.GE.cov2Rm_ricci`) is the pointwise Ricci
identity for the second covariant derivative of the curvature:
`cov2Rm g x u p a b c d - cov2Rm g x p u a b c d = -∑_i Rm(… R(u,p) · …)`.

This module reduces it to the *generic* statement about the `Ext`-pattern of a field-level tensor
(`Work.Diff.GE.extDD_antisymm`/`extDD_antisymm_swap`): the antisymmetrised second `Ext` derivative is
the algebraic curvature contraction.  The bridge is the identification

* `cov2RmExt g x u V A B C D = extDD (lcOf g) (rmPTensor g) x X V (rmPQuad A B C D)` for a field
  `X` with `X x = u` (`cov2RmExt_eq_extDD`), which is almost definitional once one knows
  `extD (rmPTensor g) = covRm` on the fields (`extD_rmPTensor`, from `kato_covRm_field`).

The main lemma `ricciPt_of_antisymm` takes the generic statement as a hypothesis, so that either
proof of it (`Work.Diff.GE.extDD_antisymm`, or a copy) can be plugged in.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- `SmoothTuple` of `rmPQuad A B C D`. -/
theorem rmPQuad_smooth {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    SmoothTuple (I := I) (M := M) (rmPQuad A B C D) := by
  intro i
  fin_cases i
  · exact hA
  · exact hB
  · exact hC
  · exact hD

/-- **`extD` of the curvature `(0,4)`-tensor is `∇Rm`.**  The first `Ext` derivative of
`rmPTensor g` is the frozen `covRm`, evaluated on the values of the fields. -/
theorem extD_rmPTensor (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X : Π y : M, TangentSpace I y) (hX : CMDiff ∞ (T% X))
    (F : Fin 4 → (Π y : M, TangentSpace I y)) (hF : SmoothTuple F) :
    extD (lcOf g) (rmPTensor g) x X F
      = covRm g x (X x) (F 0 x) (F 1 x) (F 2 x) (F 3 x) := by
  have hk := (kato_covRm_field (I := I) (M := M) hLC g x X (F 0) (F 1) (F 2) (F 3)
    hX (hF 0) (hF 1) (hF 2) (hF 3)).1
  have hfun : rmPTensor g F = fun y : M => rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) :=
    funext fun y => rmPTensor_apply g F y
  have hsum : (∑ i : Fin 4, rmPTensor g (upd (lcOf g) X F i) x)
      = rmP g x ((lcOf g) (F 0) x (X x)) (F 1 x) (F 2 x) (F 3 x)
        + rmP g x (F 0 x) ((lcOf g) (F 1) x (X x)) (F 2 x) (F 3 x)
        + rmP g x (F 0 x) (F 1 x) ((lcOf g) (F 2) x (X x)) (F 3 x)
        + rmP g x (F 0 x) (F 1 x) (F 2 x) ((lcOf g) (F 3) x (X x)) := by
    rw [Fin.sum_univ_four]
    simp (config := { decide := true }) only [rmPTensor_apply, upd, covAlong,
      Function.update_apply, Fin.isValue, reduceIte]
    try ring
  rw [extD_eq, hfun, hk, hsum]
  ring

/-- **`cov2RmExt` is the second `Ext` derivative of the curvature.** -/
theorem cov2RmExt_eq_extDD (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    (V A B C D : Π y : M, TangentSpace I y)
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (X : Π y : M, TangentSpace I y) (hX : CMDiff ∞ (T% X)) (hXu : X x = u) :
    cov2RmExt g x u V A B C D = extDD (lcOf g) (rmPTensor g) x X V (rmPQuad A B C D) := by
  have hF : SmoothTuple (I := I) (M := M) (rmPQuad A B C D) := rmPQuad_smooth hA hB hC hD
  have hcov : CovSmooth (lcOf g) := (hLC g).1.some
  have hpt : ∀ y : M, extD (lcOf g) (rmPTensor g) y V (rmPQuad A B C D)
      = covRm g y (V y) (A y) (B y) (C y) (D y) := by
    intro y
    rw [extD_rmPTensor (I := I) (M := M) hLC g y V hV (rmPQuad A B C D) hF]
    simp only [rmPQuad_zero, rmPQuad_one, rmPQuad_two, rmPQuad_three]
  have hE : ∀ i : Fin 4, extD (lcOf g) (rmPTensor g) x V (upd (lcOf g) X (rmPQuad A B C D) i)
      = covRm g x (V x) ((upd (lcOf g) X (rmPQuad A B C D) i) 0 x)
          ((upd (lcOf g) X (rmPQuad A B C D) i) 1 x)
          ((upd (lcOf g) X (rmPQuad A B C D) i) 2 x)
          ((upd (lcOf g) X (rmPQuad A B C D) i) 3 x) := by
    intro i
    exact extD_rmPTensor (I := I) (M := M) hLC g x V hV _
      (smoothTuple_upd (lcOf g) hcov hX hF i)
  have hsum : (∑ i : Fin 4, extD (lcOf g) (rmPTensor g) x V (upd (lcOf g) X (rmPQuad A B C D) i))
      = covRm g x (V x) ((lcOf g) A x (X x)) (B x) (C x) (D x)
        + covRm g x (V x) (A x) ((lcOf g) B x (X x)) (C x) (D x)
        + covRm g x (V x) (A x) (B x) ((lcOf g) C x (X x)) (D x)
        + covRm g x (V x) (A x) (B x) (C x) ((lcOf g) D x (X x)) := by
    rw [Fin.sum_univ_four]
    simp only [hE 0, hE 1, hE 2, hE 3]
    simp (config := { decide := true }) only [rmPQuad_zero, rmPQuad_one, rmPQuad_two,
      rmPQuad_three, upd, covAlong, Function.update_apply, Fin.isValue, reduceIte]
    try ring
  have h00 : extD (lcOf g) (rmPTensor g) x (covAlong (lcOf g) X V) (rmPQuad A B C D)
      = covRm g x ((lcOf g) V x (X x)) (A x) (B x) (C x) (D x) := by
    rw [show covAlong (lcOf g) X V = fun y : M => (lcOf g) V y (X y) from rfl]
    rw [extD_rmPTensor (I := I) (M := M) hLC g x _ (cmdiff_covAlong (lcOf g) hcov hX hV)
      (rmPQuad A B C D) hF]
    simp only [rmPQuad_zero, rmPQuad_one, rmPQuad_two, rmPQuad_three]
  rw [extDD_eq]
  rw [show (fun y : M => extD (lcOf g) (rmPTensor g) y V (rmPQuad A B C D))
      = fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y) from funext hpt]
  rw [h00, hsum, ← hXu, cov2RmExt]
  ring

/-- **The pointwise Ricci identity for `∇²Rm` from the generic `Ext`-pattern identity.**
`hanti` is the statement of `Work.Diff.GE.extDD_antisymm` for `τ = rmPTensor g` (with the fields
`A,B,C,D` of the curvature tensor). -/
theorem ricciPt_of_antisymm (hLC : LCSmooth I M) (g : SMet I M)
    (hanti : ∀ (x : M) (X Y : Π y : M, TangentSpace I y),
      CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
      ∀ (F : Fin 4 → (Π y : M, TangentSpace I y)), SmoothTuple (I := I) (M := M) F →
      extDD (lcOf g) (rmPTensor g) x X Y F - extDD (lcOf g) (rmPTensor g) x Y X F
        = -(Finset.univ.sum (fun i => rmPTensor g (Function.update F i
            (fun y => curv (lcOf g) X Y (F i) y)) x))) :
    RicciPt (I := I) (M := M) g := by
  intro y u p a b c d
  set F : Fin 4 → (Π y' : M, TangentSpace I y') :=
    rmPQuad (smoothExt y a) (smoothExt y b) (smoothExt y c) (smoothExt y d) with hFdef
  have hF : SmoothTuple (I := I) (M := M) F :=
    rmPQuad_smooth (smoothExt_cmdiff y a) (smoothExt_cmdiff y b) (smoothExt_cmdiff y c)
      (smoothExt_cmdiff y d)
  have h1 : cov2Rm g y u p a b c d
      = extDD (lcOf g) (rmPTensor g) y (smoothExt y u) (smoothExt y p) F := by
    rw [cov2Rm, cov2RmExt_eq_extDD (I := I) (M := M) hLC g y u (smoothExt y p) (smoothExt y a)
      (smoothExt y b) (smoothExt y c) (smoothExt y d) (smoothExt_cmdiff y p)
      (smoothExt_cmdiff y a) (smoothExt_cmdiff y b) (smoothExt_cmdiff y c)
      (smoothExt_cmdiff y d) (smoothExt y u) (smoothExt_cmdiff y u) (smoothExt_apply y u),
      ← hFdef]
  have h2 : cov2Rm g y p u a b c d
      = extDD (lcOf g) (rmPTensor g) y (smoothExt y p) (smoothExt y u) F := by
    rw [cov2Rm, cov2RmExt_eq_extDD (I := I) (M := M) hLC g y p (smoothExt y u) (smoothExt y a)
      (smoothExt y b) (smoothExt y c) (smoothExt y d) (smoothExt_cmdiff y u)
      (smoothExt_cmdiff y a) (smoothExt_cmdiff y b) (smoothExt_cmdiff y c)
      (smoothExt_cmdiff y d) (smoothExt y p) (smoothExt_cmdiff y p) (smoothExt_apply y p),
      ← hFdef]
  rw [h1, h2, hanti y (smoothExt y u) (smoothExt y p) (smoothExt_cmdiff y u)
    (smoothExt_cmdiff y p) F hF]
  congr 1
  rw [Fin.sum_univ_four]
  simp (config := { decide := true }) only [rmPTensor_apply, hFdef, rmPQuad_zero, rmPQuad_one,
    rmPQuad_two, rmPQuad_three, Function.update_apply, Fin.isValue, smoothExt_apply, reduceIte,
    rmVec]

end Work.Diff.GE
