/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2/COP — `L10`: `RN0` proved

`NOTES_LEAD_mandelbar_rn0.md` §2, `L10`; `COP/NOTES_COP.md`.  `Work.SeedSimple2.rotationZero`
(every angle landing at the root point `z₁` is fixed by `θ ↦ 1024 θ mod 1`) follows from the two
geometric obligations

* `COP/arcBound_proved.lean` (`L8`, no hypotheses at all) —
  `Work.SeedSimple2.Rotation.arcBound`;
* `COP/angleMono_proved.lean` (`L9`, only `hJ`) — `Work.SeedSimple2.Rotation.angleMono`,

via the real-analysis core `Rotation/rotation_zero_of_step` (proved in the earlier stretch of this
area, on top of `Rotation/rotation_monotone_eq_self_mono`).

This file also records the **bonus** consequence `Rotation.SidePreserveData` (`L6'` of the design
note): the `α`-pair side preservation `SP` near `z₁`, which was previously the *hypothesis* of
`Rotation/arcBound_of_sidePreserve.lean`, is now a theorem of `COP/cop_sides.lean`.
-/
import Submission.Work.SeedSimple2.COP.arcBound_proved
import Submission.Work.SeedSimple2.COP.angleMono_proved
import Submission.Work.SeedSimple2.Rotation.rotationZero_of_step
import Submission.Work.SeedSimple2.Rotation.arcBound_of_spData
import Submission.Work.ELTop.RigInput

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.COP

/-- **`RN0` proved** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L10`): every angle landing at the root
point is fixed by the angle map `θ ↦ 1024 θ mod 1`. -/
theorem rotationZero_proved (hJ : Work.Top.JordanForm) : Work.SeedSimple2.rotationZero :=
  Work.SeedSimple2.Rotation.rotationZero_of_step
    Work.SeedSimple2.COP.arcBound_proved (Work.SeedSimple2.COP.angleMono_proved hJ)

/-- **The bonus `L6'`**: the side-preservation data `Work.SeedSimple2.Rotation.SidePreserveData` of
the `α`-pair, which was the hypothesis of `Rotation/arcBound_of_sidePreserve.lean`, is a theorem
now that `cop_sides` (`L6`) is available. -/
theorem sidePreserveData_proved (hJ : Work.Top.JordanForm) :
    Work.SeedSimple2.Rotation.SidePreserveData := by
  intro c d
  -- the `α`-pair, with its two-sidedness, and the side preservation of `cop_sides` for `P' = P`
  have hnd : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 ≠ 0 := by
    apply Work.ELTop.arcLen_ne_zero_of_lt
    · norm_num [Work.EL.alpha1, Work.EL.alpha2]
    · norm_num [Work.EL.alpha1, Work.EL.alpha2]
  let P : Work.EL.CoPair d.hN :=
    { toRawPair := ⟨Work.EL.alpha1, Work.EL.alpha2, d.z₁⟩
      lands_a := (Work.SeedSimple2.landsN_iff_landsAt d).mpr d.rays.1
      lands_b := (Work.SeedSimple2.landsN_iff_landsAt d).mpr d.rays.2 }
  have hPa : P.a = Work.EL.alpha1 := rfl
  have hPb : P.b = Work.EL.alpha2 := rfl
  have hPy : P.y = d.z₁ := rfl
  have hPnd : Work.EL.arcLen P.a P.b ≠ 0 := by rw [hPa, hPb]; exact hnd
  obtain ⟨ε, hε, hcop⟩ :=
    cop_sides d hJ P P hPy hPy
      (by rw [hPa]; norm_num [Work.EL.alpha1])
      (by rw [hPb]; norm_num [Work.EL.alpha2])
      (by rw [hPa, hPb]; norm_num [Work.EL.alpha1, Work.EL.alpha2])
      ⟨-371, by rw [hPa]; norm_num [Work.EL.alpha1]⟩
      ⟨-404, by rw [hPb]; norm_num [Work.EL.alpha2]⟩
      hPnd
  exact ⟨P, hPa, hPb, hPy, ε, hε, fun z hz hzc =>
    by simpa [Work.EL.F, Work.FSeed.F] using hcop z hz hzc⟩

end Work.SeedSimple2.COP

end
