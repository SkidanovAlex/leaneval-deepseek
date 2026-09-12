import Submission.MinkBox
import Submission.MinkLower
import Submission.MinkUpper
import Submission.HilbertMink
import Submission.EnergyNeg
import Submission.SqueezeMink

/-!
# Contract-1 core: unconditional consequences

Glue module: instantiates the conditional theorems with the proved Minkowski
boxes.  Provides:

* `hilbert : hilbertProp`  (Smith prop:Hilbert)
* `energy_nonpos : EnergyHalf.energy ≤ 0`  (Smith cor:neg_energy)
* `squeeze : squeezeProp`  (Smith prop:squeeze)
* `mink_upper_uncond`, `mink_lower_uncond` (re-exports)

All sorry-free; axioms ⊆ {propext, Quot.sound, Classical.choice}.
-/

noncomputable section

open Polynomial
open scoped Real BigOperators

namespace Submission.Contract1Core

open Submission.MinkBox
open Submission.MinkLower
open Submission.MinkUpper
open Submission.HilbertMink
open Submission.EnergyNeg
open Submission.SqueezeMink

/-- The Minkowski upper box (proved). -/
theorem mink_upper_uncond : minkUpper := MinkUpper.mink_upper

/-- The Minkowski lower box (proved). -/
theorem mink_lower_uncond : minkLower := MinkLower.mink_lower

/-- Smith prop:Hilbert (unconditional). -/
theorem hilbert : hilbertProp := hilbert_of_mink mink_upper_uncond

/-- Smith cor:neg_energy: the energy of the arithmetic Serre measure is ≤ 0. -/
theorem energy_nonpos : Submission.EnergyHalf.energy ≤ 0 :=
  cor_neg_energy_of_hilbert hilbert

/-- Smith prop:squeeze (unconditional). -/
theorem squeeze : squeezeProp := squeeze_of_mink_lower mink_lower_uncond

end Submission.Contract1Core
