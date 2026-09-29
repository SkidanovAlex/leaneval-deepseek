import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMC14Core.Main

/-!
# TMC14Core: bridge to the frozen contract

This chapter keeps its own verbatim copies of the `Interfaces.lean` vocabulary
(`Work.TMC14Core.tmC`, `iterC`, `frob`, `lyap`, `pruferStep`, `pruferIter`, `rotLift`, `ids`,
`amoSpec`, …).  The frozen contract keeps copies of the same text in `Work.TMContract`.
Here we record the (definitional, up to unfolding) bridges and transport C14:

    p_gapBound_contract :
      Work.TMContract.P_LEBasics → Work.TMContract.P_RotBasics →
      Work.TMContract.P_IDSSpectrum → Work.TMContract.P_BJ → Work.TMContract.P_GapBound

so a caller working in the frozen vocabulary never has to reach past this module.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. The definitional bridges (non-recursive definitions: `rfl`) -/

theorem amoSpec_bridge (α lam : ℝ) : amoSpec α lam = Work.TMContract.amoSpec α lam := rfl

theorem frob_bridge (A : Matrix (Fin 2) (Fin 2) ℂ) : frob A = Work.TMContract.frob A := rfl

theorem tmR_bridge (lam E x : ℝ) : tmR lam E x = Work.TMContract.tmR lam E x := rfl

theorem rot_bridge (c : ℝ) : rot c = Work.TMContract.rot c := rfl

theorem HasDegree_bridge (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) :
    HasDegree B k = Work.TMContract.HasDegree B k := rfl

/-! ## 2. The recursive definitions -/

theorem pruferStep_bridge' (a t : ℝ) : pruferStep a t = Work.TMContract.pruferStep a t := rfl

theorem pruferIter_bridge_point (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    pruferIter α lam E n x t = Work.TMContract.pruferIter α lam E n x t :=
  pruferIter_bridge α lam E n x t

theorem iterC_bridge_point (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam z n x = Work.TMContract.iterC α lam z n x :=
  iterC_bridge_apply α lam z n x

theorem rotLift_bridge_point (α lam E : ℝ) :
    rotLift α lam E = Work.TMContract.rotLift α lam E :=
  rotLift_bridge α lam E

/-- `ids = 1 - rotLift` in both vocabularies. -/
theorem ids_bridge (α lam E : ℝ) : ids α lam E = Work.TMContract.ids α lam E := by
  simp only [ids, Work.TMContract.ids, rotLift_bridge_point]

theorem lyap_bridge (α lam : ℝ) (E : ℂ) : lyap α lam E = Work.TMContract.lyap α lam E := by
  simp only [lyap, Work.TMContract.lyap, iterC_bridge_point, frob_bridge]

/-! ## 3. The `Prop`s -/

theorem P_LEBasics_bridge : P_LEBasics ↔ Work.TMContract.P_LEBasics := by
  simp only [P_LEBasics, Work.TMContract.P_LEBasics, lyap_bridge, iterC_bridge_point,
    frob_bridge]

/-- `ids α lam` as a function. -/
theorem ids_fn_bridge (α lam : ℝ) : ids α lam = Work.TMContract.ids α lam := by
  funext E; exact ids_bridge α lam E

theorem P_RotBasics_bridge : P_RotBasics ↔ Work.TMContract.P_RotBasics := by
  simp only [P_RotBasics, Work.TMContract.P_RotBasics, pruferIter_bridge_point,
    rotLift_bridge_point, ids_fn_bridge, HasDegree_bridge, tmR_bridge, rot_bridge]

theorem P_IDSSpectrum_bridge : P_IDSSpectrum ↔ Work.TMContract.P_IDSSpectrum := by
  simp only [P_IDSSpectrum, Work.TMContract.P_IDSSpectrum, amoSpec_bridge, ids_fn_bridge,
    ids_bridge]

theorem P_BJ_bridge : P_BJ ↔ Work.TMContract.P_BJ := by
  simp only [P_BJ, Work.TMContract.P_BJ, amoSpec_bridge, lyap_bridge]

theorem P_GapBound_bridge : P_GapBound ↔ Work.TMContract.P_GapBound := by
  simp only [P_GapBound, Work.TMContract.P_GapBound, amoSpec_bridge, ids_fn_bridge,
    ids_bridge]

/-! ## 4. C14 in the frozen vocabulary -/

/-- **C14 in the frozen vocabulary** (`Work.TMContract.P_GapBound`). -/
theorem p_gapBound_contract (h4 : Work.TMContract.P_LEBasics)
    (h5 : Work.TMContract.P_RotBasics) (h6 : Work.TMContract.P_IDSSpectrum)
    (h7 : Work.TMContract.P_BJ) : Work.TMContract.P_GapBound :=
  P_GapBound_bridge.mp
    (p_gapBound (P_LEBasics_bridge.mpr h4) (P_RotBasics_bridge.mpr h5)
      (P_IDSSpectrum_bridge.mpr h6) (P_BJ_bridge.mpr h7))

end Work.TMC14Core
