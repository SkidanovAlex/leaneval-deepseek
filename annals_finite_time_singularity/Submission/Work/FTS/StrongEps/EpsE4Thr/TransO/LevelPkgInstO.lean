/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/LevelPkgInstO.lean` — the per-level transfer package of `IP4`, open class

`CoercivityFix/Transfer/LevelPkgInst` discharges the `AddOKSm`/Cauchy–Schwarz part of
`LevelPkg` from the regularity of the transfer, reducing the package to the two algebraic inputs
`CommSm α n IP` and `CSQ α n IP CC`.  This module is its open-class twin: it proves the same
reduction with `LevelPkg → LevelPkgO`, `CoerAdm → CoerAdmO`, using

* `TransO.HkMem_slots_O` for the four *slot* memberships,
* `TransO.SlotsMemO.Q0Sm_Lhat_slots_O` / `Q0Sm_Dth_Dz_O` for the *datum* smoothness, and
* the delegated `TransO.ContDiffOn_E1_O` / `ContDiffOn_E2_O` (smoothness of the two defects on
  the open quadrant), `TransO.HkMem_E1_O` / `HkMem_E2_O` (their `ℋⁿ`-honesty).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.DefsO
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.SlotsMemO
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.ContDiffOn_E1_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.ContDiffOn_E2_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.HkMem_E1_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.HkMem_E2_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two defects as finite-order classes -/

/-- `E1 α f` is `Q0Sm n` for `CoerAdmO α f` and `n ≤ 3`. -/
theorem Q0Sm_E1_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.FTS.CoercivityFix.Transfer.E1 α f) :=
  (ContDiffOn_E1_O α hα hα1 hf).of_le (m := (((n : ℕ)) : WithTop ℕ∞))
    (by exact_mod_cast hn)

/-- `E2 α f` is `Q0Sm n` for `CoerAdmO α f` and `n ≤ 3`. -/
theorem Q0Sm_E2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.FTS.CoercivityFix.Transfer.E2 α f) :=
  (ContDiffOn_E2_O α hα hα1 hf).of_le (m := (((n : ℕ)) : WithTop ℕ∞))
    (by exact_mod_cast hn)

/-! ## The two `AddOKSm` triples -/

/-- **The `AddOKSm` half of `LevelPkgO`**, from the regularity of the two defects. -/
theorem AddOKSm_of_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) {f : Fn}
    (hf : CoerAdmO α f) :
    Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)
      ∧ Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
          (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f) := by
  obtain ⟨hsLth, hsLdz, hsdth, hsdz⟩ := HkMem_slots_O α hα hn hf
  obtain ⟨hqLth, hqLdz⟩ := Q0Sm_Lhat_slots_O hf.1.1 n
  obtain ⟨hqdth, hqdz⟩ := Q0Sm_Dth_Dz_O hf.1.1 n
  exact
    ⟨⟨hqLth, Q0Sm_E1_O α hα hα1 hf n hn, hqdth,
        hsLth, HkMem_E1_O α hα hα1 hf n hn, hsdth⟩,
      ⟨hqLdz, Q0Sm_E2_O α hα hα1 hf n hn, hqdz,
        hsLdz, HkMem_E2_O α hα hα1 hf n hn, hsdz⟩⟩

/-- **`LevelPkgO` of a concrete level**, from the algebraic and Cauchy–Schwarz packages. -/
theorem levelPkg_of_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3)
    {IP : Fn → Fn → ℝ} {CC : ℝ} (hcomm : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hCS : Work.FTS.CoercivityFix.Transfer.CSQ α n IP CC) :
    LevelPkgO α n IP CC := by
  refine ⟨hcomm, fun f hf => ?_⟩
  obtain ⟨hAdd1, hAdd2⟩ := AddOKSm_of_O α hα hα1 n hn hf
  obtain ⟨hLdth, hLdz, hdth, hdz⟩ := HkMem_slots_O α hα hn hf
  obtain ⟨hqdth, hqdz⟩ := Q0Sm_Dth_Dz_O hf.1.1 n
  exact ⟨hAdd1, hAdd2,
    hCS (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)
      (Q0Sm_E1_O α hα hα1 hf n hn) hqdth (HkMem_E1_O α hα hα1 hf n hn) hdth,
    hCS (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)
      (Q0Sm_E2_O α hα hα1 hf n hn) hqdz (HkMem_E2_O α hα hα1 hf n hn) hdz⟩

end Work.FTS.StrongEps.EpsE4Thr.TransO
