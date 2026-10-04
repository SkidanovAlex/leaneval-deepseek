import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.GE.swap_ricci

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci identity for the second covariant derivative of the curvature

`Work.Diff.Evol.ricci_identity_rm` : for the Levi-Civita connection of a smooth metric `g`,

`(∇_v∇_w Rm)(a,b,c,d) − (∇_w∇_v Rm)(a,b,c,d)
   = −Rm(R(v,w)a,b,c,d) − Rm(a,R(v,w)b,c,d) − Rm(a,b,R(v,w)c,d) − Rm(a,b,c,R(v,w)d)`,

i.e. the commutator of the second covariant derivative of the curvature tensor acts on each of the
four slots of `Rm` by the curvature endomorphism.

The proof follows the `Ext`-pattern development of `Submission/Work/Diff/GE/`:
`Submission.Diff.cov2Rm` is (definitionally) the second `Ext` derivative
`Work.Diff.GE.extDD (lcOf g) (Work.Diff.GE.rmPTensor g)` of the curvature `(0,4)`-tensor
(`Work.Diff.GE.extD_rmPTensor`, `Work.Diff.GE.ricciPt_of_antisymm`), and the general Ricci identity
for the `Ext` pattern (`ricci_id_aux_extDD_antisymm`, proved here) is its antisymmetrisation.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Two elementary auxiliaries -/

/-- **Combination in one slot.**  If `τ` is a field-level tensor which is additive and
`ℝ`-homogeneous in each slot (in the form of `hτ_add`, `hτ_smul`), then the combination
`τ(…Z₁…) - τ(…Z₂…) + τ(…Z₃…) - τ(…Z₄…)` in slot `i` is `τ(…Z₁ - Z₂ + Z₃ - Z₄…)`. -/
theorem ricci_id_aux_tau_update_comb
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι) (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι) (G : Π y : M, TangentSpace I y)
      (c : ℝ), τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (F : ι → (Π y : M, TangentSpace I y)) (i : ι) (Z1 Z2 Z3 Z4 : Π y : M, TangentSpace I y)
    (x : M) :
    τ (Function.update F i Z1) x - τ (Function.update F i Z2) x
      + (τ (Function.update F i Z3) x - τ (Function.update F i Z4) x)
    = τ (Function.update F i (Z1 - Z2 + Z3 - Z4)) x := by
  have hfun : τ (Function.update F i Z1) - τ (Function.update F i Z2)
      + (τ (Function.update F i Z3) - τ (Function.update F i Z4))
      = τ (Function.update F i (Z1 - Z2 + Z3 - Z4)) := by
    have hneg : ∀ B : Π y : M, TangentSpace I y,
        τ (Function.update F i (-B)) = -τ (Function.update F i B) := by
      intro B
      rw [show -B = (-1 : ℝ) • B from (neg_one_smul ℝ B).symm, hτ_smul F i B (-1), neg_one_smul]
    have hterm : ∀ (A B : Π y : M, TangentSpace I y),
        τ (Function.update F i (A - B)) = τ (Function.update F i A) - τ (Function.update F i B) := by
      intro A B
      have e1 : Function.update F i (A - B) = Function.update F i (A + -B) := by rw [sub_eq_add_neg]
      rw [e1, hτ_add F i A (-B), hneg B, sub_eq_add_neg]
    rw [← hterm Z1 Z2, ← hterm Z3 Z4, ← hτ_add F i (Z1 - Z2) (Z3 - Z4)]
    congr 1
    abel
  simpa only [Pi.sub_apply, Pi.add_apply] using congrFun hfun x

/-- **The torsion replacement.**  For a torsion-free connection `cov` and smooth fields `X, Y, Z`,
`∇_{∇_X Y}Z - ∇_{∇_Y X}Z + ∇_Y∇_X Z - ∇_X∇_Y Z = -R(X,Y)Z`; this is the pointwise content of the
Ricci identity, written in terms of the `Ext` pattern's `covAlong`. -/
theorem ricci_id_aux_covAlong_curv
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) Z
      - Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) Z
      + Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X Z)
      - Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y Z)
    = - curv cov X Y Z := by
  funext y
  have hbr : cov Y y (X y) - cov X y (Y y) = mlieBracket I X Y y :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor
      ((hX y).mdifferentiableAt (by simp)) ((hY y).mdifferentiableAt (by simp))
  have key : cov Z y (cov Y y (X y)) - cov Z y (cov X y (Y y))
      = cov Z y (mlieBracket I X Y y) := by
    rw [← ContinuousLinearMap.map_sub, hbr]
  simp only [curv, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  simp only [Work.Diff.GE.covAlong]
  rw [key]
  abel

/-! ## The Ricci identity for the `Ext` pattern of a field-level tensor -/

/-- **Ricci identity for the `Ext` pattern.**  Antisymmetrising the second `Ext` derivative of a
`C^∞(M)`-multilinear field-level tensor `τ` in its two differentiation slots gives the algebraic
curvature contraction `-∑ i, τ(…, R(X,Y)(F i), …)`.

The proof expands both `extDD`s with `Work.Diff.GE.extDD_expand`; the two sums of derivatives of the
once-updated tuples cancel, Clairaut's theorem
(`Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields`) turns the two second
derivatives of `τ F` into `mvfderiv (τ F) x ([X,Y] x)`, torsion-freeness identifies this with the
`∇_X Y` / `∇_Y X` correction terms, `Work.Diff.GE.sum_univ_univ_sub_eq_diag` extracts the diagonal of
the double sums, and `ricci_id_aux_tau_update_comb` + `ricci_id_aux_covAlong_curv` finish. -/
theorem ricci_id_aux_extDD_antisymm
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) (htor : cov.torsion = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ F : ι → (Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
        Work.Diff.GE.SmoothFunT (I := I) (M := M) (τ F))
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι) (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι) (G : Π y : M, TangentSpace I y)
      (c : ℝ), τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (F : ι → (Π y : M, TangentSpace I y)) (hF : Work.Diff.GE.SmoothTuple (I := I) (M := M) F) :
    Work.Diff.GE.extDD cov τ x X Y F - Work.Diff.GE.extDD cov τ x Y X F
      = -∑ i, τ (Function.update F i (fun y => curv cov X Y (F i) y)) x := by
  classical
  rw [Work.Diff.GE.extDD_expand cov hcov τ hτ x X Y hY F hF,
      Work.Diff.GE.extDD_expand cov hcov τ hτ x Y X hX F hF]
  -- align the eta-redexes so that the two sums of first derivatives cancel
  have hT1 : (∑ i, ((d% fun y => τ (Work.Diff.GE.upd cov Y F i) y) x) (X x))
      = (∑ i, (d% (τ (Work.Diff.GE.upd cov Y F i)) x) (X x)) :=
    Finset.sum_congr rfl fun i _ => rfl
  have hT2 : (∑ i, ((d% fun y => τ (Work.Diff.GE.upd cov X F i) y) x) (Y x))
      = (∑ i, (d% (τ (Work.Diff.GE.upd cov X F i)) x) (Y x)) :=
    Finset.sum_congr rfl fun i _ => rfl
  rw [hT1, hT2]
  -- name the pieces
  set A := (d% fun y => (d% (τ F) y) (Y y)) x (X x) with hA
  set A' := (d% fun y => (d% (τ F) y) (X y)) x (Y x) with hA'
  set B := (d% (τ F) x) (Work.Diff.GE.covAlong cov X Y x) with hB
  set B' := (d% (τ F) x) (Work.Diff.GE.covAlong cov Y X x) with hB'
  set TY := ∑ i, (d% (τ (Work.Diff.GE.upd cov Y F i)) x) (X x) with hTY
  set TX := ∑ i, (d% (τ (Work.Diff.GE.upd cov X F i)) x) (Y x) with hTX
  set C := ∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x with hC
  set C' := ∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x with hC'
  set D := ∑ i, ∑ k, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x with hD
  set D' := ∑ i, ∑ k, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x with hD'
  set S := ∑ i, τ (Function.update F i (fun y => curv cov X Y (F i) y)) x with hS
  have hred : A - TY - B + C - TX + D - (A' - TX - B' + C' - TY + D')
      = (A - A') - (B - B') + (C - C') + (D - D') := by ring
  rw [hred]
  -- the second derivatives of `τ F` and the `∇_X Y`/`∇_Y X` corrections cancel (Clairaut + torsion)
  have hAB : A - A' = B - B' := by
    rw [hA, hA', hB, hB']
    have hcl := Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields
      (f := τ F) (x := x) (hτ F hF) hX hY
    rw [hcl]
    rw [show ((d% fun y => (d% (τ F) y) (X y)) x) (Y x) + (d% (τ F) x) (mlieBracket I X Y x)
          - ((d% fun y => (d% (τ F) y) (X y)) x) (Y x)
        = (d% (τ F) x) (mlieBracket I X Y x) by ring]
    rw [← ContinuousLinearMap.map_sub,
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor
        ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]
  -- off-diagonal cancellation in the double sums
  have hoff : ∀ i k : ι, k ≠ i →
      τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F k) i) x
        = τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x := by
    intro i k hki
    have h1 : (Function.update F k (Work.Diff.GE.covAlong cov X (F k))) i = F i :=
      Function.update_of_ne (Ne.symm hki) _ _
    have h2 : (Function.update F i (Work.Diff.GE.covAlong cov Y (F i))) k = F k :=
      Function.update_of_ne hki _ _
    have hupd : Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F k) i
        = Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k := by
      simp only [Work.Diff.GE.upd, h1, h2]
      exact Function.update_comm hki _ _ _
    rw [hupd]
  have hdiag := Work.Diff.GE.sum_univ_univ_sub_eq_diag
    (fun i k : ι => τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) k) x)
    (fun i k : ι => τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) k) x)
    (fun i k (hki : k ≠ i) => hoff i k hki)
  have hDsub : D - D'
      = (∑ i, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) i) x)
        - (∑ i, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) i) x) := by
    rw [hD, hD']
    simp only [← Finset.sum_sub_distrib]
    simp only [hdiag]
  -- the four field terms in slot `i` combine into `-R(X,Y)(F i)`
  have hper : ∀ i : ι,
      τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x
        - τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x
        + (τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) i) x
            - τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) i) x)
      = -τ (Function.update F i (fun y => curv cov X Y (F i) y)) x := by
    intro i
    have e1 : Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i
        = Function.update F i
            (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) (F i)) := rfl
    have e2 : Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i
        = Function.update F i
            (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) (F i)) := rfl
    have e3 : Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) i
        = Function.update F i
            (Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X (F i))) := by
      simp only [Work.Diff.GE.upd, Function.update_self, Function.update_idem]
    have e4 : Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) i
        = Function.update F i
            (Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y (F i))) := by
      simp only [Work.Diff.GE.upd, Function.update_self, Function.update_idem]
    rw [e1, e2, e3, e4]
    rw [ricci_id_aux_tau_update_comb τ hτ_add hτ_smul F i
      (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) (F i))
      (Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) (F i))
      (Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X (F i)))
      (Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y (F i))) x]
    rw [show Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov X Y) (F i)
            - Work.Diff.GE.covAlong cov (Work.Diff.GE.covAlong cov Y X) (F i)
            + Work.Diff.GE.covAlong cov Y (Work.Diff.GE.covAlong cov X (F i))
            - Work.Diff.GE.covAlong cov X (Work.Diff.GE.covAlong cov Y (F i))
          = -curv cov X Y (F i) from ricci_id_aux_covAlong_curv cov htor hX hY]
    rw [show -curv cov X Y (F i) = (-1 : ℝ) • curv cov X Y (F i)
        from (neg_one_smul ℝ (curv cov X Y (F i))).symm,
      hτ_smul F i (curv cov X Y (F i)) (-1), neg_one_smul]
    rfl
  have hCD : (C - C') + (D - D') = -S := by
    rw [hC, hC', hDsub]
    have hsplit : (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x)
          - (∑ i, τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x)
          + ((∑ i, τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) i) x)
              - (∑ i, τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) i) x))
        = ∑ i, (τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov X Y) F i) x
              - τ (Work.Diff.GE.upd cov (Work.Diff.GE.covAlong cov Y X) F i) x
              + (τ (Work.Diff.GE.upd cov Y (Work.Diff.GE.upd cov X F i) i) x
                - τ (Work.Diff.GE.upd cov X (Work.Diff.GE.upd cov Y F i) i) x)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    rw [hsplit, Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_neg_distrib, hS]
  linarith [hAB, hCD]

/-! ## The bridge to the frozen `Submission.Diff.cov2Rm` -/

/-- The GE area's `∇∇Rm` is the frozen `Submission.Diff.cov2Rm`: both are `cov2RmExt` on the chosen
extensions `smoothExt x ·`. -/
theorem ricci_id_aux_cov2Rm_eq (g : SMet I M) (x : M) (u p a b c d : TangentSpace I x) :
    Work.Diff.GE.cov2Rm g x u p a b c d = cov2Rm g x u p a b c d := by
  simp only [Work.Diff.GE.cov2Rm, Work.Diff.GE.cov2RmExt, Submission.Diff.cov2Rm,
    Work.Diff.GE.smoothExt_apply]

/-! ## The target -/

theorem ricci_identity_rm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v w a b c d : TangentSpace I x) :
    cov2Rm g x v w a b c d - cov2Rm g x w v a b c d
      = -rmP g x (rmVec (lcOf g) x v w a) b c d - rmP g x a (rmVec (lcOf g) x v w b) c d
        - rmP g x a b (rmVec (lcOf g) x v w c) d - rmP g x a b c (rmVec (lcOf g) x v w d) := by
  obtain ⟨hcov0, htor, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  have hanti : ∀ (y : M) (X Y : Π y : M, TangentSpace I y),
      CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
      ∀ (F : Fin 4 → (Π y : M, TangentSpace I y)),
        Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
        Work.Diff.GE.extDD (lcOf g) (Work.Diff.GE.rmPTensor g) y X Y F
          - Work.Diff.GE.extDD (lcOf g) (Work.Diff.GE.rmPTensor g) y Y X F
        = -(Finset.univ.sum (fun i => Work.Diff.GE.rmPTensor g (Function.update F i
            (fun y => curv (lcOf g) X Y (F i) y)) y)) :=
    fun y X Y hX hY F hF =>
      ricci_id_aux_extDD_antisymm (lcOf g) hcov htor (Work.Diff.GE.rmPTensor g)
        (fun F hF => Work.Diff.GE.rmPTensor_smooth (I := I) (M := M) hLC g hF)
        (Work.Diff.GE.rmPTensor_add (I := I) (M := M) hLC g)
        (Work.Diff.GE.rmPTensor_smul (I := I) (M := M) hLC g) y X Y hX hY F hF
  have hRicci : Work.Diff.GE.RicciPt (I := I) (M := M) g :=
    Work.Diff.GE.ricciPt_of_antisymm (I := I) (M := M) hLC g hanti
  have hR := hRicci x v w a b c d
  rw [show cov2Rm g x v w a b c d = Work.Diff.GE.cov2Rm g x v w a b c d from
        (ricci_id_aux_cov2Rm_eq (I := I) (M := M) g x v w a b c d).symm,
      show cov2Rm g x w v a b c d = Work.Diff.GE.cov2Rm g x w v a b c d from
        (ricci_id_aux_cov2Rm_eq (I := I) (M := M) g x w v a b c d).symm,
      hR]
  ring

end Work.Diff.Evol
