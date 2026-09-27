import Mathlib
import Submission.Work.EKLC7.AeHaar_of_isUInvariant
import Submission.Work.EKLRelCross.isUInvariant_of_ae_translation

/-!
# `Work.EKLC7.leafwise_invariant_full` — the frozen clause `(U4)` of `P_Leafwise`

`IsUInvariant μ U ↔` (`ν x` is a.e. right-`U`-invariant), with exactly the binders of
`Work.EKLRelCross.leafwise_invariant` (whose forward direction is the last `sorry` of component C5).

* `⇐` is `Work.EKLRelCross.isUInvariant_of_ae_translation` (Pisa 6.27, via the local invariance
  `Work.EKLUInv.local_invariance_of_ae_haar` and the contraction);
* `⇒` is `Work.EKLC7.AeHaar_of_isUInvariant`, (Pisa 6.27 / EKL (6), the direction attacked by
  `Work.EKLRelCross.localQuasiInv`/`leftQuasiInv`), proved here by comparing the `condexp` field of
  `IsLeafwise` at `x` with the same field of the *translated* plaque algebra `u·m` at `u • x`
  (see `Submission/Work/EKLC7/AeHaarPLAN.md` and `Work.EKLC7.smulMS_propor`), then feeding the
  resulting left quasi-invariance into the frozen clause (U5) via
  `Work.EKLRelCross.rightQuasiInv`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

/-- **Clause (U4) of the frozen `P_Leafwise`** (EKL (6) / Pisa 6.27): `μ` is `U`-invariant iff the
leafwise measures are a.e. right-`U`-invariant. -/
theorem leafwise_invariant_full (h2 : P_X3) (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X') :
    IsUInvariant μ U ↔ ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x :=
  ⟨fun hinv => AeHaar_of_isUInvariant h2 μ U hU t0 hmp hcontr ν X' hL hinv,
    fun hae => Work.EKLRelCross.isUInvariant_of_ae_translation h2 μ U hU t0 hmp hcontr ν X' hL
      hae⟩

end Work.EKLC7
