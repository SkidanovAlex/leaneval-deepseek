import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.PotLocDefs` — the `u = 0` two-body kernels of `potWordU`

`Work.BoseKinLoc.potWordU N v g ℓ μ 0` is, at translation parameter `u = 0`,

    `-μ Σ_i ∫_y w_{1}(x_i,y) dy + Σ_{i<j} w(x_i,x_j)`,

where both kernels are the χ-renormalised ones `wLoc ℓ h 0 a b`.  This file records the two
ingredients that an integrability proof about the **bare word** (with only *local*
integrability of `v` and `g`, and no support-radius/diluteness hypothesis) runs on:

* `wLoc 0` is the χ-renormalised kernel `wPairC` (`wLoc_zero_eq_wPairC`),
* `chemP ℓ h a = ∫_y wPairC ℓ h a y` — the `y`-integral of the one-body kernel,
* `chemQ ℓ h a = ∫⁻_y ‖wPairC ℓ h a y‖ₑ` — its `enorm` majorant (the Bochner integral of a
  non-integrable function is `0` in Lean, so every integrability estimate is run through
  `chemQ`).

Everything here is *definitional*; the analysis (the exact cancellation of the two `χ_ℓ`
factors against the denominator `(χ⋆χ)_ℓ` in the *joint* integral, which is what makes the
kernel integrable for a merely locally integrable numerator) is in
`Work.BoseFixR.lintegral_wPairC_acube_le`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- With translation parameter `u = 0` the localisation kernel `wLoc` is the
χ-renormalised two-body kernel `wPairC`. -/
lemma wLoc_zero_eq_wPairC (ℓ : ℝ) (h : E3 → ℝ) (a b : E3) :
    Submission.BoseGases.wLoc ℓ h 0 a b = Submission.BoseGases.wPairC ℓ h a b := by
  rw [Submission.BoseGases.wPairC_apply]
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-- The `y`-integral of the χ-renormalised one-body kernel `w_{1,u}` at `u = 0`, i.e. the
function whose `-μ Σᵢ` is the chemical-potential part of `potWordU`. -/
def chemP (ℓ : ℝ) (h : E3 → ℝ) (a : E3) : ℝ :=
  ∫ y : E3, Submission.BoseGases.wPairC ℓ h a y

/-- The `enorm` majorant `a ↦ ∫⁻_y ‖wPairC ℓ h a y‖ₑ` of `chemP`.  By
`MeasureTheory.enorm_integral_le_lintegral_enorm`, `‖chemP ℓ h a‖ₑ ≤ chemQ ℓ h a` for every
`a`, whether or not the Bochner integral is genuine; this is what makes it possible to bound
the integrability of `chemP` by a `∫⁻`-estimate on the joint kernel. -/
def chemQ (ℓ : ℝ) (h : E3 → ℝ) (a : E3) : ENNReal :=
  ∫⁻ y : E3, ‖Submission.BoseGases.wPairC ℓ h a y‖ₑ

/-- `chemP` is the `wLoc`-version of the same integral (the `u = 0` rewriting, at the level of
the Bochner integral). -/
lemma chemP_eq_wLoc_integral (ℓ : ℝ) (h : E3 → ℝ) (a : E3) :
    chemP ℓ h a = ∫ y : E3, Submission.BoseGases.wLoc ℓ h 0 a y := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (wLoc_zero_eq_wPairC ℓ h a y).symm)

end Work.BoseFixR
