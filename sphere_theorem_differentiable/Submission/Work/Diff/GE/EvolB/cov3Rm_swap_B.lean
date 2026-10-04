import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib
import Submission.Work.Diff.GE.swap_defs
import Submission.Work.Diff.GE.swap_ricci
import Submission.Work.Diff.GE.swap_curvsection
import Submission.Work.Diff.GE.swap_extDphiT
import Submission.Work.Diff.GE.EvolB.extDD_antisymm_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second/third slot swap for `∇³Rm` (`EvolB`)

`Work.Diff.GE.EvolB.cov3Rm_swap_B` is the antisymmetry of the second and third slots of
`Work.Diff.GE.cov3Rm`.  The proof is the one written in
`Submission/Work/Diff/GE/cov3Rm_swap.lean`, with the single `sorry`ed input
`Work.Diff.GE.extDD_antisymm_swap` replaced by the proved
`Work.Diff.GE.EvolB.extDD_antisymm_B` (the two statements are identical).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
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

/-- **The second/third slot swap for `∇³Rm`**: the `EvolB` version of `Work.Diff.GE.cov3Rm_swap`,
free of `sorryAx`. -/
theorem cov3Rm_swap_B
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (X Y P a b c d : TangentSpace I x) :
    Work.Diff.GE.cov3Rm g x X Y P a b c d - Work.Diff.GE.cov3Rm g x X P Y a b c d
      = - (Submission.Diff.rmP g x (Work.Diff.GE.curvDeriv g x X Y P a) b c d
          + Submission.Diff.rmP g x a (Work.Diff.GE.curvDeriv g x X Y P b) c d
          + Submission.Diff.rmP g x a b (Work.Diff.GE.curvDeriv g x X Y P c) d
          + Submission.Diff.rmP g x a b c (Work.Diff.GE.curvDeriv g x X Y P d))
        - (Submission.Diff.covRm g x X
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x Y P a) b c d
          + Submission.Diff.covRm g x X a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x Y P b) c d
          + Submission.Diff.covRm g x X a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x Y P c) d
          + Submission.Diff.covRm g x X a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x Y P d)) := by
  -- The Ricci identity for `∇²Rm`, from the generic `Ext`-pattern identity.
  have hRicci : Work.Diff.GE.RicciPt (I := I) (M := M) g :=
    Work.Diff.GE.ricciPt_of_antisymm (I := I) (M := M) hLC g
      (fun x X Y hX hY F hF =>
        extDD_antisymm_B (I := I) (M := M) (Submission.Diff.lcOf g)
          ((hLC g).1.some) ((hLC g).2.1) (Work.Diff.GE.rmPTensor g)
          (fun F hF => Work.Diff.GE.rmPTensor_smooth (I := I) (M := M) hLC g hF)
          (Work.Diff.GE.rmPTensor_add (I := I) (M := M) hLC g)
          (Work.Diff.GE.rmPTensor_smul (I := I) (M := M) hLC g) x X Y hX hY F hF)
  -- Step 1: the antisymmetrised third derivative is `-extD phiT`.
  have h1 := Work.Diff.GE.cov3Rm_swap_step1 (I := I) (M := M) hLC g x X Y P a b c d hRicci
  -- Step 2: `extD phiT` is the sum of the two brackets.
  have h2 := Work.Diff.GE.extD_phiT_fields (I := I) (M := M) hLC g x
    (Xs := Submission.Diff.smoothExt x X) (Ys := Submission.Diff.smoothExt x Y)
    (Ps := Submission.Diff.smoothExt x P) (As := Submission.Diff.smoothExt x a)
    (Bs := Submission.Diff.smoothExt x b) (Cs := Submission.Diff.smoothExt x c)
    (Ds := Submission.Diff.smoothExt x d)
    (Work.Diff.GE.smoothExt_cmdiff x X) (Work.Diff.GE.smoothExt_cmdiff x Y)
    (Work.Diff.GE.smoothExt_cmdiff x P) (Work.Diff.GE.smoothExt_cmdiff x a)
    (Work.Diff.GE.smoothExt_cmdiff x b) (Work.Diff.GE.smoothExt_cmdiff x c)
    (Work.Diff.GE.smoothExt_cmdiff x d)
  simp only [Work.Diff.GE.smoothExt_apply, Submission.Diff.rmVec] at h2 ⊢
  rw [h1, h2]
  ring

end Work.Diff.GE.EvolB
