import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.Wall
import Submission.Work.ClassFieldTower.WallShrunk
import Submission.Work.ClassFieldTower.unitTwoRank_witness_eq_one
import Submission.Work.ClassFieldTower.ProPDeficiencyBridge
import Submission.Work.ProPDeficiency.Deficiency

/-!
# `Work.ClassFieldTower.NumericalCertificate` -- the assignment's consumable form

The assignment's "essential consumable form" of the Shafarevich--Koch deficiency bound is:

  **for the explicit `F`, `G_∅` admits a minimal presentation with `d = rank₂ Cl(F) ≥ 5`
  generators and `r` relators satisfying `4r ≤ d²`.**

This module states that form as a theorem, in both of the available normalisations of the wall:

* `four_mul_le_sq_of_kcPresentationWall` -- from `KcPresentationWall = ProTwoPresentationData Kc`
  (the Artin generator rank `d = rank₂ Cl(Kc)`, the Koch bound `r ≤ d + d₂(O_{Kc}^×)`, and the
  *proved* numerical inputs `5 ≤ rank₂ Cl(Kc)`, `d₂(O_{Kc}^×) = 1`), the Golod--Shafarevich
  inequality `4r ≤ d²` holds for the minimal presentation of `G_∅`;
* `four_mul_le_sq_of_kcShrunkInput` -- the same for the sound existential wall `KcShrunkInput`
  (the numerical data alone, without the class-group identification);
* `four_mul_le_sq_of_shafarevichKochBound_witness` -- the numeric statement for `Kc` used by both:
  `ShafarevichKochBound Kc d r` (`r ≤ d + d₂(O_{Kc}^×)`) with `5 ≤ d` gives `4r ≤ d²`, using the
  *proved* `d₂(O_{Kc}^×) = 1` (`unitTwoRank_witness_eq_one`).

Together with `Work.ClassFieldTower.infiniteProTwoExtension_of_kcShrunkInput` (which feeds this
inequality into `Work.ClassFieldTower.infinite_of_hasMinimalPresentation`, hence into the finite
`p`-group Golod--Shafarevich inequality of Chapter B) this is the complete numerical path from the
arithmetic input to `InfiniteProTwoExtension Kc`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The numerical crux for `Kc`**: the Shafarevich--Koch bound `r ≤ d + d₂(O_{Kc}^×)` together
with `d ≥ 5` and the proved `d₂(O_{Kc}^×) = 1` gives the Golod--Shafarevich inequality
`4 r ≤ d * d`. -/
theorem four_mul_le_sq_of_shafarevichKochBound_witness {d r : ℕ}
    (h : ShafarevichKochBound Kc d r) (h5 : 5 ≤ d) : 4 * r ≤ d * d := by
  have h1 : r ≤ d + 1 := by
    have h2 : unitTwoRank Kc = 1 := unitTwoRank_witness_eq_one
    simp only [ShafarevichKochBound] at h
    omega
  exact Work.ProPDeficiency.four_mul_le_sq_of_le_add_one h1 h5

/-- **The assignment's consumable form, from the presentation wall `KcPresentationWall`.**

From the (Artin) generator rank `d = rank₂ Cl(Kc)`, the Shafarevich--Koch relation bound and the two
proved numerical inputs (`5 ≤ rank₂ Cl(Kc)`, `d₂(O_{Kc}^×) = 1`) one gets a minimal presentation of
`G_∅` with `d = rank₂ Cl(Kc) ≥ 5` generators, `r ≤ d + 1` relators, and `4r ≤ d²`. -/
theorem four_mul_le_sq_of_kcPresentationWall (h : KcPresentationWall) :
    ∃ d r : ℕ, d = classGroupTwoRank Kc ∧ 5 ≤ d ∧ r ≤ d + 1 ∧ 4 * r ≤ d * d := by
  obtain ⟨α, iα, iDα, rel, hgen, hrel, -, -, -⟩ := h
  refine ⟨Fintype.card α, rel.card, hgen, ?_, ?_, ?_⟩
  · rw [hgen]; exact five_le_classGroupTwoRank
  · have h2 : unitTwoRank Kc ≤ 1 := le_of_eq unitTwoRank_witness_eq_one
    have h1 : rel.card ≤ Fintype.card α + unitTwoRank Kc := by rw [hgen]; exact hrel
    omega
  · have hbound : ShafarevichKochBound Kc (classGroupTwoRank Kc) rel.card := hrel
    have := four_mul_le_sq_of_shafarevichKochBound_witness hbound five_le_classGroupTwoRank
    rwa [hgen]

/-- **The assignment's consumable form, from the sound existential wall `KcShrunkInput`** (the
numerical data alone). -/
theorem four_mul_le_sq_of_kcShrunkInput (h : KcShrunkInput) :
    ∃ d r : ℕ, 5 ≤ d ∧ r ≤ d + 1 ∧ 4 * r ≤ d * d := by
  obtain ⟨G, iG, α, iα, iDα, rel, -, hrel, -, -, -, h5⟩ := h
  exact ⟨Fintype.card α, rel.card, h5, hrel,
    Work.ProPDeficiency.four_mul_le_sq_of_le_add_one hrel h5⟩

/-- **The same for the `Work.ProPDeficiency`-vocabulary wall.** -/
theorem four_mul_le_sq_of_proPDeficiencyInput (h : KcProPDeficiencyInput) :
    ∃ d r : ℕ, 5 ≤ d ∧ r ≤ d + 1 ∧ 4 * r ≤ d * d :=
  four_mul_le_sq_of_kcShrunkInput (kcShrunkInput_of_proPDeficiencyInput h)

end Work.ClassFieldTower
