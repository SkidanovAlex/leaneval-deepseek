import Mathlib
import Submission.Work.WingbergH3.Constructive
import Submission.Work.WingbergH3.H3Wall
import Submission.Work.WingbergH3.Obstruction

/-!
# `Work.WingbergH3.Wiring` -- the consumers of this area

Every wall of this area (`KummerInput`, `ConstructiveInput`, `H3DeficiencyWall`, its sharp and unit
normalisations) is plugged into the consumers of `Submission/Work/WingbergRoute/`:

| consumer | declaration |
|---|---|
| `Work.ShafarevichKoch.KcProTwoPresentationInput` | `kcProTwoPresentationInput_of_kummerInput`, `..._of_constructiveInput`, `..._of_H3DeficiencyWall` (and the `_seamFree` variants) |
| `Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6` | `hasProTwoPresentation_Kc_five_six_of_...` |
| `Submission.NumberField.BoundedRdTowerWall` | `boundedRdTowerWall_of_...` |
| `Submission.NumberField.UnramifiedPro2TowerWall` | `unramifiedPro2TowerWall_of_...` |
| `Work.ClassFieldTower.InfiniteProTwoExtension Kc` | `infiniteProTwoExtension_Kc_of_...` |
| `Work.RelatorRank.HasProP2Presentation (G_∅) (GeneratorRank) (d + 2)` at `gsF` | `exists_hasProP2Presentation_gsF_of_...` |
| the benchmark | `benchmark_of_kcWingbergWall_of_realPart` (Kc, with the real-part wall) and, for `gsF`, `Work.WingbergRoute.exists_totallyReal_discr_le_of_gsFArithmeticInput` once the `gsF` dictionary is supplied |

All of these are compositions of the proved implications of this area with the proved endgame of
`Work.WingbergRoute`; nothing new is assumed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

/-! ## `Kc`: the Shafarevich--Koch crux and its consequences -/

/-- **The crux from the Kummer form of the constructive input.** -/
theorem kcProTwoPresentationInput_of_kummerInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KummerInput Kc) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.WingbergRoute.kcProTwoPresentationInput_of_kcWingbergWall hdict
    (kcWingbergWall_of_kummerInput h)

/-- **The crux from the pro-`2` form of the constructive input.** -/
theorem kcProTwoPresentationInput_of_constructiveInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ConstructiveInput Kc) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.WingbergRoute.kcProTwoPresentationInput_of_kcWingbergWall hdict
    (kcWingbergWall_of_constructiveInput h)

/-- **The crux from the `H³`-half of Wingberg's duality.** -/
theorem kcProTwoPresentationInput_of_H3DeficiencyWall
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : H3DeficiencyWall Kc) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.WingbergRoute.kcProTwoPresentationInput_of_kcWingbergWall hdict
    (kcWingbergWall_of_H3DeficiencyWall h)

/-- **The crux from the sharp form of Wingberg's duality.** -/
theorem kcProTwoPresentationInput_of_sharpH3Wall
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : SharpH3Wall Kc) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_H3DeficiencyWall hdict (H3DeficiencyWall_of_sharpH3Wall h)

/-- **`HasProTwoPresentation Kc 5 6` from the `H³`-half.** -/
theorem hasProTwoPresentation_Kc_five_six_of_H3DeficiencyWall
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : H3DeficiencyWall Kc) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  Work.WingbergRoute.hasProTwoPresentation_Kc_five_six_of_kcWingbergWall hdict
    (kcWingbergWall_of_H3DeficiencyWall h)

/-- **`HasProTwoPresentation Kc 5 6` from the Kummer form of the constructive input.** -/
theorem hasProTwoPresentation_Kc_five_six_of_kummerInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KummerInput Kc) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  Work.WingbergRoute.hasProTwoPresentation_Kc_five_six_of_kcWingbergWall hdict
    (kcWingbergWall_of_kummerInput h)

/-- **The caller's `BoundedRdTowerWall` from the `H³`-half.** -/
theorem boundedRdTowerWall_of_H3DeficiencyWall
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : H3DeficiencyWall Kc) : Submission.NumberField.BoundedRdTowerWall :=
  Work.WingbergRoute.boundedRdTowerWall_of_kcWingbergWall hdict
    (kcWingbergWall_of_H3DeficiencyWall h)

/-- **The caller's `BoundedRdTowerWall` from the Kummer form of the constructive input.** -/
theorem boundedRdTowerWall_of_kummerInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KummerInput Kc) : Submission.NumberField.BoundedRdTowerWall :=
  Work.WingbergRoute.boundedRdTowerWall_of_kcWingbergWall hdict (kcWingbergWall_of_kummerInput h)

/-- **`Kc` has an infinite unramified pro-`2` tower, from the Kummer form of the constructive
input.** -/
theorem infiniteProTwoExtension_Kc_of_kummerInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KummerInput Kc) : Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  Work.WingbergRoute.infiniteProTwoExtension_Kc_of_kcWingbergWall hdict
    (kcWingbergWall_of_kummerInput h)

/-- **The caller's `UnramifiedPro2TowerWall` from the `H³`-half.** -/
theorem unramifiedPro2TowerWall_of_H3DeficiencyWall
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : H3DeficiencyWall Kc) : Submission.NumberField.UnramifiedPro2TowerWall :=
  Work.WingbergRoute.unramifiedPro2TowerWall_of_kcWingbergWall hdict
    (kcWingbergWall_of_H3DeficiencyWall h)

/-! ### The seam-free variants (Gaschütz via `Work.AbstractDictionary`) -/

/-- **The crux from the Kummer form of the constructive input, seam-free.** -/
theorem kcProTwoPresentationInput_of_kummerInput_seamFree
    (hpres : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (galoisGroup M))
    (h : KummerInput Kc) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.WingbergRoute.kcProTwoPresentationInput_of_kcWingbergWall_seamFree hpres
    (kcWingbergWall_of_kummerInput h)

/-- **The crux from the `H³`-half, seam-free.** -/
theorem kcProTwoPresentationInput_of_H3DeficiencyWall_seamFree
    (hpres : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (galoisGroup M))
    (h : H3DeficiencyWall Kc) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.WingbergRoute.kcProTwoPresentationInput_of_kcWingbergWall_seamFree hpres
    (kcWingbergWall_of_H3DeficiencyWall h)

/-- **`HasProTwoPresentation Kc 5 6` from the `H³`-half, seam-free.** -/
theorem hasProTwoPresentation_Kc_five_six_of_H3DeficiencyWall_seamFree
    (hpres : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (galoisGroup M))
    (h : H3DeficiencyWall Kc) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  Work.WingbergRoute.hasProTwoPresentation_Kc_five_six_of_kcWingbergWall_seamFree hpres
    (kcWingbergWall_of_H3DeficiencyWall h)

/-- **The benchmark with the real-part wall, from the Kummer form of the constructive input.** -/
theorem benchmark_of_kummerInput_of_realPart
    (hdict : ∀ M : MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KummerInput Kc) (hr : Work.HilbertTowerCM.RealPartWall Kc) :
    Work.CMRealSubfield.Benchmark :=
  Work.WingbergRoute.benchmark_of_kcWingbergWall_of_realPart hdict
    (kcWingbergWall_of_kummerInput h) hr

/-! ## `gsF`: the totally real instance -/

/-- **The presentation step at `gsF` from the Kummer form of the constructive input.** -/
theorem exists_hasProP2Presentation_gsF_of_kummerInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} gsF 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KummerInput gsF) :
    ∃ M : MaximalUnramifiedProP.{0} gsF 2, ∃ d : ℕ,
      Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.HasProP2Presentation (galoisGroup M)
          (Work.RelatorRank.GeneratorRank (galoisGroup M)) (d + 2) := by
  obtain ⟨M, hM⟩ := gsFWingbergWall_of_kummerInput h
  exact ⟨M, Work.WingbergRoute.hasProP2Presentation_gsF_of_wall M (hdict M) hM⟩

/-- **The presentation step at `gsF` from the pro-`2` form of the constructive input.** -/
theorem exists_hasProP2Presentation_gsF_of_constructiveInput
    (hdict : ∀ M : MaximalUnramifiedProP.{0} gsF 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ConstructiveInput gsF) :
    ∃ M : MaximalUnramifiedProP.{0} gsF 2, ∃ d : ℕ,
      Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.HasProP2Presentation (galoisGroup M)
          (Work.RelatorRank.GeneratorRank (galoisGroup M)) (d + 2) := by
  obtain ⟨M, hM⟩ := gsFWingbergWall_of_constructiveInput h
  exact ⟨M, Work.WingbergRoute.hasProP2Presentation_gsF_of_wall M (hdict M) hM⟩

/-- **The presentation step at `gsF` from the `H³`-half of Wingberg's duality.** -/
theorem exists_hasProP2Presentation_gsF_of_H3DeficiencyWall
    (hdict : ∀ M : MaximalUnramifiedProP.{0} gsF 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : H3DeficiencyWall gsF) :
    ∃ M : MaximalUnramifiedProP.{0} gsF 2, ∃ d : ℕ,
      Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.HasProP2Presentation (galoisGroup M)
          (Work.RelatorRank.GeneratorRank (galoisGroup M)) (d + 2) := by
  obtain ⟨M, hM⟩ := gsFWingbergWall_of_H3DeficiencyWall h
  exact ⟨M, Work.WingbergRoute.hasProP2Presentation_gsF_of_wall M (hdict M) hM⟩

/-- **The Golod--Shafarevich inequality at `gsF` from the Kummer form of the constructive
input**: the presentation above has `d ≥ 6` generators (the multiquadratic certificate) and
`d + 2` relators, whence `4 · rel ≤ d²` and the tower is infinite. -/
theorem four_mul_le_sq_of_kummerInput {d r : ℕ} (hd : 6 ≤ d)
    (hr : r ≤ d + unitTwoRank gsF) : 4 * r ≤ d * d :=
  Work.WingbergRoute.four_mul_le_sq_of_le_add_unitTwoRank hd hr

end Work.WingbergH3
