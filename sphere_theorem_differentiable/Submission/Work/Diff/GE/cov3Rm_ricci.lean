import Mathlib
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.extDD_antisymm
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.cov2RmExt_prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The `(0,5)`-tensor `∇Rm` as a field-level tensor (an `ExtTensor` of arity `Fin 5`):
`covRmT g G = (y ↦ covRm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y))`. -/
noncomputable def covRmT (g : SMet I M) : ExtTensor (I := I) (M := M) (Fin 5) :=
  fun G => fun y => covRm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y)

/-- Unfolding lemma for `covRmT`. -/
theorem covRmT_apply (g : SMet I M) (G : Fin 5 → (Π y : M, TangentSpace I y)) (y : M) :
    covRmT g G y = covRm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y) := rfl

/-- The first `Ext` derivative of `∇Rm` is the frozen `∇∇Rm`, evaluated on smooth fields. -/
theorem extD_covRmT (g : SMet I M) (x : M) (X : Π y : M, TangentSpace I y)
    (F : Fin 5 → (Π y : M, TangentSpace I y)) :
    extD (lcOf g) (covRmT g) x X F
      = cov2RmExt g x (X x) (F 0) (F 1) (F 2) (F 3) (F 4) := by
  rw [extD_eq]
  rw [show (covRmT g) F = (fun y => covRm g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) (F 4 y)) from rfl]
  simp only [cov2RmExt, covRmT_apply]
  rw [Fin.sum_univ_five]
  simp only [upd, covAlong, Function.update_apply]
  simp
  ring

/-- `cov2RmExt` on smooth fields is the frozen `cov2Rm` on their values. -/
theorem cov2RmExt_eq_cov2Rm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u : TangentSpace I x)
    {V A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    cov2RmExt g x u V A B C D = cov2Rm g x u (V x) (A x) (B x) (C x) (D x) := by
  rw [show cov2Rm g x u (V x) (A x) (B x) (C x) (D x)
      = cov2RmExt g x u (smoothExt x (V x)) (smoothExt x (A x)) (smoothExt x (B x))
          (smoothExt x (C x)) (smoothExt x (D x)) from rfl]
  exact (kato_cov2RmExt_field (I := I) (M := M) hLC g x V A B C D
    (smoothExt x (V x)) (smoothExt x (A x)) (smoothExt x (B x)) (smoothExt x (C x))
    (smoothExt x (D x)) hV hA hB hC hD (smoothExt_cmdiff x (V x)) (smoothExt_cmdiff x (A x))
    (smoothExt_cmdiff x (B x)) (smoothExt_cmdiff x (C x)) (smoothExt_cmdiff x (D x))
    (smoothExt_apply x (V x)).symm (smoothExt_apply x (A x)).symm (smoothExt_apply x (B x)).symm
    (smoothExt_apply x (C x)).symm (smoothExt_apply x (D x)).symm).1 u

/-- `cov2RmExt` on the fields agrees with `cov2Rm` on their values, as functions. -/
theorem cov2RmExt_field_fun (hLC : LCSmooth I M) (g : SMet I M) (Y : Π y : M, TangentSpace I y)
    (hY : CMDiff ∞ (T% Y)) {V A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    (fun y : M => cov2RmExt g y (Y y) V A B C D)
      = (fun y : M => cov2Rm g y (Y y) (V y) (A y) (B y) (C y) (D y)) := by
  funext y
  exact (Kato3.cov2Rm_field_form (g := g) hLC y hY hV hA hB hC hD).symm

/-- The second `Ext` derivative of `∇Rm` is the frozen `∇∇∇Rm`, evaluated on smooth fields. -/
theorem extDD_covRmT (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X Y : Π y : M, TangentSpace I y) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (F : Fin 5 → (Π y : M, TangentSpace I y)) (hF : ∀ i, CMDiff ∞ (T% (F i))) :
    extDD (lcOf g) (covRmT g) x X Y F
      = cov3RmExt g x (X x) Y (F 0) (F 1) (F 2) (F 3) (F 4) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have hF' : SmoothTuple (I := I) (M := M) F := hF
  rw [extDD_eq]
  simp only [extD_covRmT]
  rw [cov2RmExt_field_fun (g := g) hLC Y hY (hF 0) (hF 1) (hF 2) (hF 3) (hF 4)]
  rw [cov2RmExt_eq_cov2Rm (g := g) hLC x ((covAlong (lcOf g) X Y) x)
        (hF 0) (hF 1) (hF 2) (hF 3) (hF 4)]
  have hupd : ∀ i : Fin 5, SmoothTuple (I := I) (M := M) (upd (lcOf g) X F i) := fun i =>
    smoothTuple_upd (lcOf g) hcov hX hF' i
  rw [Finset.sum_congr rfl (fun i _ =>
    cov2RmExt_eq_cov2Rm (g := g) hLC x (Y x) (hupd i 0) (hupd i 1) (hupd i 2) (hupd i 3)
      (hupd i 4))]
  rw [Fin.sum_univ_five]
  rw [cov3RmExt]
  simp only [upd, covAlong, Function.update_apply]
  simp
  ring

/-- Smoothness of `covRmT g` on smooth tuples. -/
theorem covRmT_smooth (hLC : LCSmooth I M) (g : SMet I M) :
    ∀ F : Fin 5 → (Π y : M, TangentSpace I y),
      SmoothTuple (I := I) (M := M) F → SmoothFunT (I := I) (M := M) (covRmT g F) := by
  intro F hF
  rw [show covRmT g F = (fun y => covRm g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) (F 4 y)) from rfl]
  exact covRm_fields_smooth (g := g) hLC (hF 0) (hF 1) (hF 2) (hF 3) (hF 4)

/-- Additivity of `covRmT g` in each slot. -/
theorem covRmT_add (hLC : LCSmooth I M) (g : SMet I M)
    (F : Fin 5 → (Π y : M, TangentSpace I y)) (i : Fin 5)
    (G H : Π y : M, TangentSpace I y) :
    covRmT g (Function.update F i (G + H))
      = covRmT g (Function.update F i G) + covRmT g (Function.update F i H) := by
  funext y
  simp only [covRmT_apply, Function.update_apply, Pi.add_apply]
  fin_cases i <;>
    · simp only [Fin.isValue, ite_apply]
      first
        | simpa using covRm_linear_fst hLC g y 1 1 (G y) (H y) (F 1 y) (F 2 y) (F 3 y) (F 4 y)
        | simpa using covRm_linear_snd hLC g y (F 0 y) 1 1 (G y) (H y) (F 2 y) (F 3 y) (F 4 y)
        | simpa using covRm_linear_thd hLC g y (F 0 y) (F 1 y) 1 1 (G y) (H y) (F 3 y) (F 4 y)
        | simpa using covRm_linear_fth hLC g y (F 0 y) (F 1 y) (F 2 y) 1 1 (G y) (H y) (F 4 y)
        | simpa using covRm_linear_fif hLC g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) 1 1 (G y) (H y)

/-- Constant-homogeneity of `covRmT g` in each slot. -/
theorem covRmT_smul (hLC : LCSmooth I M) (g : SMet I M)
    (F : Fin 5 → (Π y : M, TangentSpace I y)) (i : Fin 5)
    (G : Π y : M, TangentSpace I y) (c : ℝ) :
    covRmT g (Function.update F i (c • G)) = c • covRmT g (Function.update F i G) := by
  funext y
  simp only [covRmT_apply, Function.update_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
    · simp only [Fin.isValue, ite_apply]
      first
        | simpa using covRm_linear_fst hLC g y c 0 (G y) (G y) (F 1 y) (F 2 y) (F 3 y) (F 4 y)
        | simpa using covRm_linear_snd hLC g y (F 0 y) c 0 (G y) (G y) (F 2 y) (F 3 y) (F 4 y)
        | simpa using covRm_linear_thd hLC g y (F 0 y) (F 1 y) c 0 (G y) (G y) (F 3 y) (F 4 y)
        | simpa using covRm_linear_fth hLC g y (F 0 y) (F 1 y) (F 2 y) c 0 (G y) (G y) (F 4 y)
        | simpa using covRm_linear_fif hLC g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) c 0 (G y) (G y)

theorem cov3Rm_ricci
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (w u p a b c d : TangentSpace I x) :
    Work.Diff.GE.cov3Rm g x w u p a b c d - Work.Diff.GE.cov3Rm g x u w p a b c d
      = - (Submission.Diff.covRm g x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u p) a b c d
          + Submission.Diff.covRm g x p (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u a) b c d
          + Submission.Diff.covRm g x p a (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u b) c d
          + Submission.Diff.covRm g x p a b (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u c) d
          + Submission.Diff.covRm g x p a b c (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u d)) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have htor : (Submission.Diff.lcOf g).torsion = 0 := (hLC g).2.1
  let F : Fin 5 → (Π y : M, TangentSpace I y) :=
    ![smoothExt x p, smoothExt x a, smoothExt x b, smoothExt x c, smoothExt x d]
  have hF : ∀ i, CMDiff ∞ (T% (F i)) := by
    intro i
    fin_cases i <;>
      · simp only [F]
        simp
        exact smoothExt_cmdiff x _
  have hX : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_cmdiff x w
  have hY : CMDiff ∞ (T% (smoothExt x u)) := smoothExt_cmdiff x u
  have hgen := extDD_antisymm (cov := Submission.Diff.lcOf g) hcov htor (covRmT g)
    (covRmT_smooth hLC g) (covRmT_add hLC g) (covRmT_smul hLC g)
    x (smoothExt x w) (smoothExt x u) hX hY F hF
  have h1 : extDD (Submission.Diff.lcOf g) (covRmT g) x (smoothExt x w) (smoothExt x u) F
      = Work.Diff.GE.cov3Rm g x w u p a b c d := by
    rw [extDD_covRmT hLC g x (smoothExt x w) (smoothExt x u) hX hY F hF]
    rw [smoothExt_apply x w]
    simp only [F]
    simp
    rfl
  have h2 : extDD (Submission.Diff.lcOf g) (covRmT g) x (smoothExt x u) (smoothExt x w) F
      = Work.Diff.GE.cov3Rm g x u w p a b c d := by
    rw [extDD_covRmT hLC g x (smoothExt x u) (smoothExt x w) hY hX F hF]
    rw [smoothExt_apply x u]
    simp only [F]
    simp
    rfl
  have hsumR : (∑ i : Fin 5, covRmT g (Function.update F i
        (fun y => curv (Submission.Diff.lcOf g) (smoothExt x w) (smoothExt x u) (F i) y)) x)
      = Submission.Diff.covRm g x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u p) a b c d
        + Submission.Diff.covRm g x p (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u a) b c d
        + Submission.Diff.covRm g x p a (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u b) c d
        + Submission.Diff.covRm g x p a b (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u c) d
        + Submission.Diff.covRm g x p a b c (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u d) := by
    rw [Fin.sum_univ_five]
    simp only [covRmT_apply, Function.update_apply, ite_apply, F]
    simp
    simp only [smoothExt_apply, rmVec]
  rw [h1, h2] at hgen
  rw [hsumR] at hgen
  exact hgen

end Work.Diff.GE
