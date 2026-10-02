import Mathlib
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSplit
import Submission.Work.StemsB.Rat.CollarCup
import Submission.Work.StemsB.Rat.collarSuspClass_sq_rat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The suspension class of the collar, over `ℚ` (provisional)

The suspension class `s` of the collar pair over `ℚ` and the Thom class `τ` it transgresses to,
together with the four properties used by the derivation argument.  The existence statement
`collarSuspensionClass_sq` is the ℚ-coefficient analogue of `Work.StemsB.collarSuspensionClass_sq`;
it is currently proved by a placeholder and will be replaced by a proof (its own, or the one produced
by the delegate at `Submission.Work.StemsB.Rat.collarSuspClass_sq_rat`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB.Rat

noncomputable section

/-- **The suspension class of the collar pair.** -/
theorem collarSuspensionClass_sq (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    ∃ (s : (Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
      (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)),
      CollarThom (Y := Y) b τ ∧
      CollarTransgresses (Y := Y) b (by omega) s τ ∧
      Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj
          (TopCat.of ↥(sphLoopCollarProd b Y))) (b - 1) (b - 1) s s = 0 ∧
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
          (TopCat.of ↥(sphLoopCollarProd b Y))
          (TopCat.ofHom (collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0 :=
  Work.StemsB.Rat.collarSuspClass_sq_rat b hb Y

/-- The suspension class `s` of the collar pair. -/
noncomputable def wangSusS (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) :=
  Classical.choose (collarSuspensionClass_sq b hb Y)

/-- The Thom class `τ` of the collar pair. -/
noncomputable def wangSusT (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
  Classical.choose (Classical.choose_spec (collarSuspensionClass_sq b hb Y))

/-- The Thom property of `wangSusT`. -/
theorem wangSusT_thom (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    CollarThom (Y := Y) b (wangSusT b hb Y) :=
  (Classical.choose_spec (Classical.choose_spec (collarSuspensionClass_sq b hb Y))).1

/-- The transgression property of `wangSusS`. -/
theorem wangSusS_trans (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    CollarTransgresses (Y := Y) b (by omega) (wangSusS b hb Y) (wangSusT b hb Y) :=
  (Classical.choose_spec (Classical.choose_spec (collarSuspensionClass_sq b hb Y))).2.1

/-- `s ⌣ s = 0` for the suspension class. -/
theorem wangSusS_sq (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) (wangSusS b hb Y) (wangSusS b hb Y) = 0 :=
  (Classical.choose_spec (Classical.choose_spec (collarSuspensionClass_sq b hb Y))).2.2.1

/-- The suspension class restricts to `0` on the collar section. -/
theorem wangSusS_sect (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
        (TopCat.of ↥(sphLoopCollarProd b Y))
        (TopCat.ofHom (collarSection (Y := Y) b (by omega))) (b - 1)).hom
      (wangSusS b hb Y) = 0 :=
  (Classical.choose_spec (Classical.choose_spec (collarSuspensionClass_sq b hb Y))).2.2.2

end

end Work.StemsB.Rat
