/-
# The three `L¹` norms of the cutoff `η` and its derivatives

This module fixes the three constants of the `SupNorm` area:

* `Work.KMTAreas.SupNorm.etaI0 = ∫ y, ‖η y‖`,
* `Work.KMTAreas.SupNorm.etaI1 = ∫ y, ‖deriv η y‖`,
* `Work.KMTAreas.SupNorm.etaI2 = ∫ y, ‖iteratedDeriv 2 η y‖`,

where `η = Work.KMTContract.kmtEta`.  They are the only numerical inputs of the pointwise
sup-norm bound for an `Lᵖ` Fourier multiplier: the `L¹` norms of the wave packet
`𝓕⁻(η((· - x₀)/δ))` and its first two derivatives are `δ ηI0`, `ηI1` and `ηI2 / δ` respectively.
-/
import Mathlib
import Submission.Work.KMTContract.Defs

set_option autoImplicit false

open scoped ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.SupNorm

open Work.KMTContract

/-- `ηI0 = ∫ ‖η‖`, the `L¹` norm of the cutoff `η = kmtEta`. -/
noncomputable def etaI0 : ℝ := ∫ y, ‖kmtEta y‖

/-- `ηI1 = ∫ ‖η'‖`, the `L¹` norm of the derivative of the cutoff. -/
noncomputable def etaI1 : ℝ := ∫ y, ‖deriv kmtEta y‖

/-- `ηI2 = ∫ ‖η''‖`, the `L¹` norm of the second derivative of the cutoff. -/
noncomputable def etaI2 : ℝ := ∫ y, ‖iteratedDeriv 2 kmtEta y‖

theorem etaI0_nonneg : 0 ≤ etaI0 := integral_nonneg fun _ => norm_nonneg _

theorem etaI1_nonneg : 0 ≤ etaI1 := integral_nonneg fun _ => norm_nonneg _

theorem etaI2_nonneg : 0 ≤ etaI2 := integral_nonneg fun _ => norm_nonneg _

end Work.KMTAreas.SupNorm
