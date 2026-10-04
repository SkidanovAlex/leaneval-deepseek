import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib
import Submission.Work.Diff.GE.cov3Rm_ricci
import Submission.Work.Diff.GE.EvolB.extDD_antisymm_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci identity for `∇²Rm` (`EvolB`)

`Work.Diff.GE.EvolB.cov3Rm_ricci_B` is the antisymmetry of the first two slots of
`Work.Diff.GE.cov3Rm` — the Ricci identity for the `(0,5)`-tensor `∇Rm` — obtained from the general
`Ext`-pattern identity `Work.Diff.GE.EvolB.extDD_antisymm_B` applied to the field-level tensor
`Work.Diff.GE.covRmT g` of `Submission/Work/Diff/GE/cov3Rm_ricci.lean` (whose auxiliary results are
sorry-free; only its final application of the `sorry`ed `Work.Diff.GE.extDD_antisymm` is replaced
here).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]

/-- **The Ricci identity for `∇Rm`** (the antisymmetry of the first two slots of `cov3Rm`): the
`EvolB` version of `Work.Diff.GE.cov3Rm_ricci`, proved from `extDD_antisymm_B` so that it is free
of `sorryAx`. -/
theorem cov3Rm_ricci_B
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (w u p a b c d : TangentSpace I x) :
    Work.Diff.GE.cov3Rm g x w u p a b c d - Work.Diff.GE.cov3Rm g x u w p a b c d
      = - (Submission.Diff.covRm g x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u p) a b c d
          + Submission.Diff.covRm g x p (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u a) b c d
          + Submission.Diff.covRm g x p a (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u b) c d
          + Submission.Diff.covRm g x p a b (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u c) d
          + Submission.Diff.covRm g x p a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u d)) := by
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
  have hgen := extDD_antisymm_B (cov := Submission.Diff.lcOf g) hcov htor (Work.Diff.GE.covRmT g)
    (Work.Diff.GE.covRmT_smooth hLC g) (Work.Diff.GE.covRmT_add hLC g)
    (Work.Diff.GE.covRmT_smul hLC g)
    x (smoothExt x w) (smoothExt x u) hX hY F hF
  have h1 : Work.Diff.GE.extDD (Submission.Diff.lcOf g) (Work.Diff.GE.covRmT g) x
        (smoothExt x w) (smoothExt x u) F
      = Work.Diff.GE.cov3Rm g x w u p a b c d := by
    rw [Work.Diff.GE.extDD_covRmT hLC g x (smoothExt x w) (smoothExt x u) hX hY F hF]
    rw [smoothExt_apply x w]
    simp only [F]
    simp
    rfl
  have h2 : Work.Diff.GE.extDD (Submission.Diff.lcOf g) (Work.Diff.GE.covRmT g) x
        (smoothExt x u) (smoothExt x w) F
      = Work.Diff.GE.cov3Rm g x u w p a b c d := by
    rw [Work.Diff.GE.extDD_covRmT hLC g x (smoothExt x u) (smoothExt x w) hY hX F hF]
    rw [smoothExt_apply x u]
    simp only [F]
    simp
    rfl
  have hsumR : (∑ i : Fin 5, Work.Diff.GE.covRmT g (Function.update F i
        (fun y => curv (Submission.Diff.lcOf g) (smoothExt x w) (smoothExt x u) (F i) y)) x)
      = Submission.Diff.covRm g x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u p) a b c d
        + Submission.Diff.covRm g x p (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u a) b c d
        + Submission.Diff.covRm g x p a (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u b) c d
        + Submission.Diff.covRm g x p a b
            (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u c) d
        + Submission.Diff.covRm g x p a b c
            (Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u d) := by
    rw [Fin.sum_univ_five]
    simp only [Work.Diff.GE.covRmT_apply, Function.update_apply, ite_apply, F]
    simp
    simp only [smoothExt_apply, rmVec]
  rw [h1, h2] at hgen
  rw [hsumR] at hgen
  exact hgen

end Work.Diff.GE.EvolB
