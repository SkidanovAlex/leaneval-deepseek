import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ClassFieldTower.Defs

/-!
# The unit dichotomy for the maximal unramified pro-`2` extension

Let `F` be a number field and `M` the maximal unramified pro-`2` extension of `F`.  Assume that
(i) every unit `u` of `𝓞 F` is, inside `Fˣ`, either a square or the negative of a square
(`hunit`), and (ii) `-1` is not a square in `M.K` (`hneg`).

Then the second alternative of the dichotomy cannot occur for a unit whose square root already
lives in `M.K`:

`Work.ShafarevichKoch.hunits_of_unit_dichotomy` says that whenever `z ∈ M.K` satisfies
`z * z = u` for a unit `u ∈ (𝓞 F)ˣ` (viewed inside `M.K`), then `u` is already a square in `Fˣ`.

The mathematics is one line: if `u = -y²` with `y ∈ Fˣ`, then in `M.K`

`(z / y)² = z² / y² = -y² / y² = -1`,

contradicting `hneg`.  So the dichotomy `hunit` collapses to "square" as soon as one square root
of the unit is visible in the unramified extension.  This is the unit input of the sharpened
Kummer two-descent (`Work.ShafarevichKoch.card_quadraticLevel_le_of_unit_dichotomy`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **The unit dichotomy, collapsed along the unramified extension.**  If every unit of `𝓞 F` is
`±` a square in `F` and `-1` is not a square in the maximal unramified pro-`2` extension `M.K`,
then a unit of `𝓞 F` which acquires a square root in `M.K` is a square in `F`. -/
theorem hunits_of_unit_dichotomy (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hunit : ∀ u : Work.ShafarevichKoch.RingUnit F, ∃ y : Fˣ,
      Work.ShafarevichKoch.unitEmbed F u = y ^ 2 ∨
        Work.ShafarevichKoch.unitEmbed F u = -y ^ 2)
    (hneg : ∀ z : M.K, z * z = -1 → False) :
    ∀ (u : Work.ShafarevichKoch.RingUnit F) (z : M.K),
      z * z = algebraMap F M.K (Work.ShafarevichKoch.unitEmbed F u : F) →
      ∃ y : Fˣ, Work.ShafarevichKoch.unitEmbed F u = y ^ 2 := by
  intro u z hz
  obtain ⟨y, hy | hy⟩ := hunit u
  · -- the unit is already a square
    exact ⟨y, hy⟩
  · -- the unit is the negative of a square: then `-1` is a square in `M.K`
    exfalso
    have hyF : ((unitEmbed F u : Fˣ) : F) = - ((y : F) ^ 2) := by
      rw [hy]; simp
    have hz' : z * z = - (algebraMap F M.K (y : F)) ^ 2 := by
      rw [hz, hyF]
      push_cast
      ring
    have hane : algebraMap F M.K (y : F) ≠ 0 := by
      simp
    refine hneg (z * (algebraMap F M.K (y : F))⁻¹) ?_
    have hzz : z * (algebraMap F M.K (y : F))⁻¹ * (z * (algebraMap F M.K (y : F))⁻¹)
        = (z * z) * ((algebraMap F M.K (y : F))⁻¹ * (algebraMap F M.K (y : F))⁻¹) := by ring
    rw [hzz, hz']
    field_simp

end Work.ShafarevichKoch
