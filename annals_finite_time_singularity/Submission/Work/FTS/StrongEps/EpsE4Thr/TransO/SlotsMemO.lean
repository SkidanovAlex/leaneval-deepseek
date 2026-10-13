/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/SlotsMemO.lean` — the open-class slot data of the transfer

The transfer induction of `CoercivityFix/Transfer/` consumes, for every `f` of its class and
every `n ≤ 3`, the four facts

* `ℋⁿ(𝓛̂(D_θf))`, `ℋⁿ(𝓛̂(D_zf))` — the two *clean* operator slots of the right-hand side,
* `ℋⁿ(D_θf)`, `ℋⁿ(D_zf)` — the two differentiated slots of the datum,

together with the finite-order smoothness `Q0Sm n` of the same four functions (`Q0Sm n X` is
`C^n` of the uncurried `X` on the open quadrant, the class in which the additivity clause of the
transfer is phrased).

The frozen versions (`Transfer/LevelPkgInst.HkMem_slots`, `Q0SmDefects.Q0Sm_Lhat_Dth`,
`Q0Sm_Dth_Dz`) are stated on `Work.FTS.Nonlin.CoerAdm α f`, whose regularity component is the
*strip* class `LocData.SmoothQuad f` (`C^∞` on `z > -1`).  The projected mollified slices of the
route do **not** satisfy that class (`EpsE4Thr/OpenClass.lean`), so the transfer has to be re-run
against the open class `CoerAdmO α f`, whose regularity component is
`EllipticEst.SmoothOpen f` (`C^∞` on the open quadrant `Qd = (0,∞) × (0,π/2)`) — the class that
the open coercivity chapter (`RegQo`, `StepReg2O`, `Comm2O`, `CoerData2O`, `CoerDataTO`) already
runs on.

Everything here is proved from `SmoothOpen` plus the two `RegQo`-ports `regQo_dth_dz` and
`Lhat_RegQo`; it rests on `[propext, Classical.choice, Quot.sound]`.

The two *defect* slots `E1 α f`, `E2 α f` are handled separately (`TransO/HkMem_E1_O`,
`TransO/HkMem_E2_O`), and the two transfer identities in `TransO/Dth_LGammaT_eq_O`,
`TransO/Dz_LGammaT_eq_O`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.Lhat_RegQo
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.ContE1

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

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `SmoothOpen` as a finite-order class -/

/-- `SmoothOpen` (genuine `C^∞` on the open quadrant) gives the finite-order class `Q0Sm n`. -/
theorem Q0Sm_of_smoothOpen {X : Fn} (h : Work.FTS.EllipticEst.SmoothOpen X) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n X :=
  h.of_le (m := (((n : ℕ)) : WithTop ℕ∞)) (WithTop.coe_le_coe.mpr le_top)

/-- `D_θf` and `D_zf` are in `Q0Sm n` for every `n` when `f` is `SmoothOpen`. -/
theorem Q0Sm_Dth_Dz_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.Spaces.Dth f) ∧
      Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.Spaces.Dz f) :=
  ⟨Work.FTS.CoercivityFix.Transfer.Q0Sm.dth
      (Q0Sm_of_smoothOpen hf (n + 1)),
    Work.FTS.CoercivityFix.Transfer.Q0Sm.dz
      (Q0Sm_of_smoothOpen hf (n + 1))⟩

/-! ## The two clean-operator slots are `C^∞` on the open quadrant -/

/-- **`𝓛̂(D_θf)` is `C^∞` on the open quadrant** for `SmoothOpen f`.  This is the `SmoothOpen`
twin of `E1Parts.contDiffOn_uncurry_Lhat_Dth` (which asks for `SmoothQuad f`, a class the
route's slices do not satisfy). -/
theorem contDiffOn_uncurry_Lhat_Dth_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)))
      Work.Construction.Qd := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hf
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dth f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_pz hV hDth
  have hDthDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hDth
  have hne : ∀ p ∈ Work.Construction.Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    linarith
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
      = fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.Dth f) p
            + p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.Dth f)) p
            - 2 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)
            - 3 * Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth f)) p / (1 + p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz]
  rw [hfun]
  exact (((hDth.add (contDiffOn_fst.mul hpz)).sub
      ((contDiffOn_const.mul hDth).div (contDiffOn_const.add contDiffOn_fst) hne)).sub
    ((contDiffOn_const.mul hDthDth).div (contDiffOn_const.add contDiffOn_fst) hne))

/-- **`𝓛̂(D_zf)` is `C^∞` on the open quadrant** for `SmoothOpen f` (the `SmoothOpen` twin of
`E2_pkg.contDiffOn_uncurry_Lhat_Dz`). -/
theorem contDiffOn_uncurry_Lhat_Dz_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)))
      Work.Construction.Qd := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dz hV hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_pz hV h1
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV h1
  have hne : ∀ p ∈ Work.Construction.Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    linarith
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      = fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.Dz f) p
            + p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz f)) p
            - 2 * Function.uncurry (Work.Spaces.Dz f) p / (1 + p.1)
            - 3 * Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f)) p / (1 + p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz]
  rw [hfun]
  exact (((h1.add (contDiffOn_fst.mul h2)).sub
      ((contDiffOn_const.mul h1).div (contDiffOn_const.add contDiffOn_fst) hne)).sub
    ((contDiffOn_const.mul h3).div (contDiffOn_const.add contDiffOn_fst) hne))

/-- `Q0Sm n` of the two clean-operator slots, for `SmoothOpen f`. -/
theorem Q0Sm_Lhat_slots_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) ∧
      Work.FTS.CoercivityFix.Transfer.Q0Sm n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) :=
  ⟨(contDiffOn_uncurry_Lhat_Dth_O hf).of_le (WithTop.coe_le_coe.mpr le_top),
    (contDiffOn_uncurry_Lhat_Dz_O hf).of_le (WithTop.coe_le_coe.mpr le_top)⟩

/-! ## The `ℋⁿ`-membership of the four slots -/

/-- **The four slot memberships of the transfer on the open class**: for `CoerAdmO α f` and
`n ≤ 3`, the `ℋⁿ`-honesty of `𝓛̂(D_θf)`, `𝓛̂(D_zf)`, `D_θf`, `D_zf`.

This is the open-class twin of `Transfer/LevelPkgInst.HkMem_slots` (which asks for `CoerAdm`).
The `D_θ`/`D_z` slots come from the `RegQo`-port `regQo_dth_dz`, and the two clean-operator
slots from `Lhat_RegQo`. -/
theorem HkMem_slots_O (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : n ≤ 3) {f : Fn}
    (hf : CoerAdmO α f) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
      ∧ Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      ∧ Work.Spaces.HkMem α n (Work.Spaces.Dth f)
      ∧ Work.Spaces.HkMem α n (Work.Spaces.Dz f) := by
  have h5 : RegQo α 5 f := hf.1
  have h1 : RegQo α (n + 1) f := regQo_mono (by omega) h5
  have h2 : RegQo α (n + 2) f := regQo_mono (by omega) h5
  obtain ⟨hdth1, hdz1⟩ := regQo_dth_dz hα h1
  obtain ⟨hdth2, hdz2⟩ := regQo_dth_dz hα h2
  have hLth : RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) :=
    Work.FTS.StrongEps.EpsE4Thr.Lhat_RegQo α hα n hdth2
  have hLdz : RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) :=
    Work.FTS.StrongEps.EpsE4Thr.Lhat_RegQo α hα n hdz2
  exact ⟨hLth.2.1, hLdz.2.1, hdth1.2.1, hdz1.2.1⟩

end Work.FTS.StrongEps.EpsE4Thr.TransO
