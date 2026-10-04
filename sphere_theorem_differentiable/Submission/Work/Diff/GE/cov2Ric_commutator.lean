import Mathlib
import Submission.Work.Diff.Evol.RicPhi
import Submission.Work.Diff.Evol.ricci_identity_rm
import Submission.Work.Diff.Evol.covDLC_B_identity
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci identity (commutator of `∇²Ric`) in pointwise form

`Work.Diff.GE.cov2Ric_commutator` is the pointwise Ricci identity for the second covariant
derivative of the Ricci tensor of a smooth metric `g`:

`(∇_v∇_w Ric)(a,b) − (∇_w∇_v Ric)(a,b)
   = −Ric(R(v,w)a, b) − Ric(a, R(v,w)b)`.

It is the Ricci-tensor analogue of `Work.Diff.GE.cov2Rm_ricci` (the same identity for `Rm`), and the
proof follows the same route.  The `Ext`-pattern machinery of `Work.Diff.GE` computes covariant
derivatives of a *field-level tensor* `τ`; here `τ` is the Ricci tensor viewed as a `(0,2)`-tensor
`ricPTensor g F y = ricAt (lcOf g) y (F 0 y) (F 1 y)` of arity `Fin 2`.  The generic Ricci identity
for the `Ext` pattern (`Work.Diff.Evol.ricci_id_aux_extDD_antisymm`, proved in the `Evol` area)
then gives the antisymmetrised second derivative as the contraction of `τ` with the curvature in
each slot; unfolding one contraction reproduces the displayed formula.

The bridges are

* `cov2Ric_eq_cov2RicExt` (`Evol`): the frozen pointwise `cov2Ric` is the `Ext` pattern
  `cov2RicExt` on the chosen smooth extensions `smoothExt x ·`;
* `cov2RicExt_eq_extDD`: `cov2RicExt` is the second `Ext` derivative of `ricPTensor g` (this is
  essentially the definition, once `extD (ricPTensor g) = dRicPhi`);
* `ricPTensor_smooth/add/smul`: the bookkeeping (smoothness, `C^∞(M)`-linearity in each slot) that
  the generic identity needs, imported from the `Evol`/`EXT` areas.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

namespace Cov2RicComm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]

/-- The Ricci tensor of `g` as a field-level `(0,2)`-tensor (arity `Fin 2`). -/
noncomputable abbrev ricPTensor (g : SMet I M) : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin 2) :=
  fun F y => ricAt (lcOf g) y (F 0 y) (F 1 y)

/-- The tuple of two fields `(A, B)`, as an element of `Fin 2 → fields`. -/
abbrev ricPQuad (A B : Π y : M, TangentSpace I y) : Fin 2 → (Π y : M, TangentSpace I y) := ![A, B]

@[simp] theorem ricPQuad_zero (A B : Π y : M, TangentSpace I y) : ricPQuad A B 0 = A := rfl
@[simp] theorem ricPQuad_one (A B : Π y : M, TangentSpace I y) : ricPQuad A B 1 = B := rfl

/-- **`extD` of the Ricci `(0,2)`-tensor is `∇Ric`**: the first `Ext` derivative of `ricPTensor g`
is the `Ext` pattern `dRicPhi` of the covariant derivative of the Ricci tensor, evaluated on the
values of the fields.  This is almost the definition of `dRicPhi`. -/
theorem extD_ricPTensor (g : SMet I M) (x : M) (X : Π y : M, TangentSpace I y)
    (F : Fin 2 → (Π y : M, TangentSpace I y)) :
    extD (lcOf g) (ricPTensor g) x X F = Work.Diff.Evol.dRicPhi g x (X x) (F 0) (F 1) := by
  have hric : ricPTensor g F = Work.Diff.Evol.ricF g (F 0) (F 1) := rfl
  rw [extD_eq, Fin.sum_univ_two, hric]
  simp only [ricPTensor, Function.update_apply, Fin.reduceEq, ite_true, ite_false,
    Function.update_self, Work.Diff.Evol.dRicPhi, upd, covAlong, Fin.isValue]
  ring

/-- `ricPTensor g` is smooth on smooth tuples. -/
theorem ricPTensor_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {F : Fin 2 → (Π y : M, TangentSpace I y)} (hF : SmoothTuple F) :
    SmoothFunT (I := I) (M := M) (ricPTensor g F) := by
  have h : ricPTensor g F = Work.Diff.Evol.ricF g (F 0) (F 1) := rfl
  rw [h]
  exact Work.Diff.Evol.covDLC_B_ricF_smooth hLC g (F 0) (F 1) (hF 0) (hF 1)

/-- `ricPTensor g` is additive in each of its two slots (as a function on `M`). -/
theorem ricPTensor_add (hLC : LCSmooth I M) (g : SMet I M)
    (F : Fin 2 → (Π y : M, TangentSpace I y)) (i : Fin 2)
    (G H : Π y : M, TangentSpace I y) :
    ricPTensor g (Function.update F i (G + H))
      = ricPTensor g (Function.update F i G) + ricPTensor g (Function.update F i H) := by
  obtain ⟨hcov0, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  funext y
  fin_cases i <;>
    simp only [ricPTensor, Function.update_apply, Fin.reduceEq, ite_true, ite_false,
      Function.update_self, Fin.isValue, Pi.add_apply]
  · exact Work.Diff.EXT.ricAt_add_middle_L g hcov y _ _ _
  · exact Work.Diff.EXT.ricAt_add_last_L g hcov y _ _ _

/-- `ricPTensor g` is `ℝ`-homogeneous in each of its two slots (as a function on `M`). -/
theorem ricPTensor_smul (hLC : LCSmooth I M) (g : SMet I M)
    (F : Fin 2 → (Π y : M, TangentSpace I y)) (i : Fin 2)
    (G : Π y : M, TangentSpace I y) (c : ℝ) :
    ricPTensor g (Function.update F i (c • G)) = c • ricPTensor g (Function.update F i G) := by
  obtain ⟨hcov0, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  funext y
  fin_cases i <;>
    simp only [ricPTensor, Function.update_apply, Fin.reduceEq, ite_true, ite_false,
      Function.update_self, Fin.isValue, Pi.smul_apply, smul_eq_mul]
  · exact Work.Diff.EXT.ricAt_smul_middle_L g hcov y _ _ _
  · exact Work.Diff.EXT.ricAt_smul_last_L g hcov y _ _ _

/-- **`cov2RicExt` is the second `Ext` derivative of the Ricci `(0,2)`-tensor.**  The `Ext` pattern
of `∇²Ric` on the fields `(X, W, A, B)` equals `extDD` of `ricPTensor g`, where `X` is the field
supplying the derivative directions `∇A`, `∇B` (so we use the same field for the derivative
direction and for the connection corrections; this is exactly the situation in `cov2Ric`, where
both are `smoothExt x ·`). -/
theorem cov2RicExt_eq_extDD (g : SMet I M) (x : M) (v : TangentSpace I x)
    (X W A B : Π y : M, TangentSpace I y) (hxX : X x = v) :
    Work.Diff.Evol.cov2RicExt g x v X W A B
      = extDD (lcOf g) (ricPTensor g) x X W (ricPQuad A B) := by
  rw [extDD_eq, Work.Diff.Evol.cov2RicExt]
  have hpt : (fun y : M => extD (lcOf g) (ricPTensor g) y W (ricPQuad A B))
      = fun y : M => Work.Diff.Evol.dRicPhi g y (W y) A B := by
    funext y
    rw [extD_ricPTensor]
    simp only [ricPQuad_zero, ricPQuad_one]
  rw [hpt]
  have hc : extD (lcOf g) (ricPTensor g) x (covAlong (lcOf g) X W) (ricPQuad A B)
      = Work.Diff.Evol.dRicPhi g x ((lcOf g) W x (X x)) A B := by
    rw [extD_ricPTensor]
    simp only [ricPQuad_zero, ricPQuad_one, covAlong]
  rw [hc, Fin.sum_univ_two]
  have h0 : extD (lcOf g) (ricPTensor g) x W (upd (lcOf g) X (ricPQuad A B) 0)
      = Work.Diff.Evol.dRicPhi g x (W x) (fun y : M => (lcOf g) A y (X y)) B := by
    rw [extD_ricPTensor]
    simp only [ricPQuad_zero, ricPQuad_one, upd, covAlong, Function.update_apply, Fin.reduceEq,
      ite_true, ite_false, Function.update_self, Fin.isValue]
  have h1 : extD (lcOf g) (ricPTensor g) x W (upd (lcOf g) X (ricPQuad A B) 1)
      = Work.Diff.Evol.dRicPhi g x (W x) A (fun y : M => (lcOf g) B y (X y)) := by
    rw [extD_ricPTensor]
    simp only [ricPQuad_zero, ricPQuad_one, upd, covAlong, Function.update_apply, Fin.reduceEq,
      ite_true, ite_false, Function.update_self, Fin.isValue]
  rw [h0, h1, hxX]
  ring

end Cov2RicComm

open Cov2RicComm

theorem cov2Ric_commutator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v w a b : TangentSpace I x) :
    Work.Diff.Evol.cov2Ric g x v w a b - Work.Diff.Evol.cov2Ric g x w v a b
      = -Submission.Diff.ricAt (Submission.Diff.lcOf g) x
            (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v w a) b
        - Submission.Diff.ricAt (Submission.Diff.lcOf g) x a
            (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v w b) := by
  obtain ⟨hcov0, htor, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  set F : Fin 2 → (Π y : M, TangentSpace I y) :=
    ricPQuad (smoothExt x a) (smoothExt x b) with hFdef
  have hF : SmoothTuple (I := I) (M := M) F := by
    intro i
    rw [hFdef]
    fin_cases i
    · simp only [ricPQuad_zero]; exact smoothExt_cmdiff x a
    · simp only [ricPQuad_one]; exact smoothExt_cmdiff x b
  have hvs : CMDiff ∞ (T% (smoothExt x v)) := smoothExt_cmdiff x v
  have hws : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_cmdiff x w
  -- identify the two pointwise second covariant derivatives with the `Ext` pattern
  have h1 : Work.Diff.Evol.cov2Ric g x v w a b
      = extDD (lcOf g) (ricPTensor g) x (smoothExt x v) (smoothExt x w) F := by
    rw [Work.Diff.Evol.cov2Ric_eq_cov2RicExt hLC g x v w a b, hFdef,
      cov2RicExt_eq_extDD g x v (smoothExt x v) (smoothExt x w) (smoothExt x a)
        (smoothExt x b) (smoothExt_apply x v)]
  have h2 : Work.Diff.Evol.cov2Ric g x w v a b
      = extDD (lcOf g) (ricPTensor g) x (smoothExt x w) (smoothExt x v) F := by
    rw [Work.Diff.Evol.cov2Ric_eq_cov2RicExt hLC g x w v a b, hFdef,
      cov2RicExt_eq_extDD g x w (smoothExt x w) (smoothExt x v) (smoothExt x a)
        (smoothExt x b) (smoothExt_apply x w)]
  rw [h1, h2]
  -- the generic Ricci identity for the `Ext` pattern of a field-level tensor
  rw [Work.Diff.Evol.ricci_id_aux_extDD_antisymm (lcOf g) hcov htor (ricPTensor g)
    (fun F' hF' => ricPTensor_smooth hLC g hF') (ricPTensor_add hLC g) (ricPTensor_smul hLC g)
    x (smoothExt x v) (smoothExt x w) hvs hws F hF]
  -- unfold the curvature contraction in the two slots
  have hsum : (∑ i : Fin 2, ricPTensor g (Function.update F i
        (fun y => curv (lcOf g) (smoothExt x v) (smoothExt x w) (F i) y)) x)
      = ricAt (lcOf g) x (rmVec (lcOf g) x v w a) b
        + ricAt (lcOf g) x a (rmVec (lcOf g) x v w b) := by
    rw [Fin.sum_univ_two]
    congr 1
    · rw [ricPTensor, Function.update_self,
        Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
      simp only [hFdef, ricPQuad_zero, ricPQuad_one, rmVec, smoothExt_apply]
    · rw [ricPTensor, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        Function.update_self]
      simp only [hFdef, ricPQuad_zero, ricPQuad_one, rmVec, smoothExt_apply]
  rw [hsum]
  ring

end Work.Diff.GE
