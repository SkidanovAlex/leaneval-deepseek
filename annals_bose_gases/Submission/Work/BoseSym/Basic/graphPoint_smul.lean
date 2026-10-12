import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Homogeneity of the graph point map

`graphPoint N L F = (F, ∇F)` is the graph of the gradient, as an element of the
ambient space `Amb N = L²(Conf N) × ∏_j L²(Conf N)`.  This file proves that it
is homogeneous over `ℝ`:

`graphPoint N L (c • F) = c • graphPoint N L F`.

Both components are handled by the `L²` bookkeeping lemmas
`MemLp.toLp_congr` (which lets us replace the function by an a.e. equal one,
independently of the `MemLp` proof term, the latter being a `Prop`) and
`MemLp.toLp_const_smul`.  The pointwise inputs are
`Submodule.coe_smul` (the coercion `testSub N L → (Conf N → ℝ)` is linear) and
`fderiv_const_smul` (the directional derivative `x ↦ fderiv ℝ F x u` is
linear in `F`).
-/

namespace Work.BoseSym.Basic

open MeasureTheory

theorem graphPoint_smul {N : ℕ} {L : ℝ} (c : ℝ) (F : testSub N L) :
    graphPoint N L (c • F) = c • graphPoint N L F := by
  simp only [graphPoint]
  apply Prod.ext
  · rw [Prod.smul_fst]
    have hF : MemLp (F : Conf N → ℝ) 2 (volC N) :=
      memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)
    have hcF : MemLp ((c • F : testSub N L) : Conf N → ℝ) 2 (volC N) :=
      memLp_of_contDiff_hasCompactSupport (c • F).2.1 (hasCompactSupport_of_testFun (c • F).2)
    have hae : ((c • F : testSub N L) : Conf N → ℝ) =ᵐ[volC N] c • (F : Conf N → ℝ) :=
      Filter.Eventually.of_forall fun x => congrFun (Submodule.coe_smul c F) x
    exact (MemLp.toLp_congr hcF (hF.const_smul c) hae).trans (MemLp.toLp_const_smul c hF)
  · rw [Prod.smul_snd]
    funext j
    have hg0 : MemLp (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x
        (Submission.BoseGases.kcDir N j.1 j.2)) 2 (volC N) :=
      memLp_of_contDiff_hasCompactSupport
        (Submission.BoseGases.firstDir_contDiff F.2.1 (Submission.BoseGases.kcDir N j.1 j.2))
        (IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun F.2)
          (isClosed_tsupport (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x
            (Submission.BoseGases.kcDir N j.1 j.2)))
          (Submission.BoseGases.tsupport_firstDir_subset (f := (F : Conf N → ℝ))
            (Submission.BoseGases.kcDir N j.1 j.2)))
    have hg1 : MemLp (fun x : Conf N => fderiv ℝ ((c • F : testSub N L) : Conf N → ℝ) x
        (Submission.BoseGases.kcDir N j.1 j.2)) 2 (volC N) :=
      memLp_of_contDiff_hasCompactSupport
        (Submission.BoseGases.firstDir_contDiff (c • F).2.1
          (Submission.BoseGases.kcDir N j.1 j.2))
        (IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun (c • F).2)
          (isClosed_tsupport (fun x : Conf N => fderiv ℝ ((c • F : testSub N L) : Conf N → ℝ) x
            (Submission.BoseGases.kcDir N j.1 j.2)))
          (Submission.BoseGases.tsupport_firstDir_subset (f := ((c • F : testSub N L) : Conf N → ℝ))
            (Submission.BoseGases.kcDir N j.1 j.2)))
    have hae : (fun x : Conf N => fderiv ℝ ((c • F : testSub N L) : Conf N → ℝ) x
          (Submission.BoseGases.kcDir N j.1 j.2))
        =ᵐ[volC N] (fun x : Conf N => c • fderiv ℝ (F : Conf N → ℝ) x
          (Submission.BoseGases.kcDir N j.1 j.2)) := by
      refine Filter.Eventually.of_forall fun x => ?_
      have hd : DifferentiableAt ℝ (F : Conf N → ℝ) x :=
        F.2.1.contDiffAt.differentiableAt (by simp)
      simp only [Submodule.coe_smul, fderiv_const_smul hd c, smul_apply]
    exact (MemLp.toLp_congr hg1 (hg0.const_smul c) hae).trans (MemLp.toLp_const_smul c hg0)

end Work.BoseSym.Basic
