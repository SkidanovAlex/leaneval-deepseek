/-
# `SharpMassDDI σ` for every `σ ≥ 1`, from the base case and the proved dimension step

`Work.Peluse.Ulower.StepLe.sharpMassDDI_step` (`StepLe/sharpMassDDI_step.lean`, PROVED,
axiom-clean) is the dimension step `SharpMassDDI σ → SharpMassDDI (σ+1)`, so the mass form of
Peluse's Lemma 7.4 in every dimension follows by induction from its `σ = 1` case.

The `σ = 1` case is the only remaining input; it is available both as
`Work.Peluse.Ulower.StepLe.sharpMassDDI_one_v2` (`StepLe/sharpMassDDI_one_v2.lean`) and as
`Work.Peluse.Ulower.StepLe.ddiSharp.ddiSharp_one` (`StepLe/ddiSharp/ddiSharp_one.lean`).  This
module states the induction with the base case as an explicit hypothesis, so that the wiring of the
degree-lowering target can name whichever proof of `SharpMassDDI 1` lands first.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.sharpMassDDI_step

set_option autoImplicit false

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- `SharpMassDDI` in every dimension `σ ≥ 1`, by induction from the `σ = 1` case and the dimension
step `sharpMassDDI_step` (PROVED). -/
theorem sharpMassDDI_all (h1 : Work.Peluse.Ulower.StepLe.SharpMassDDI 1) :
    ∀ σ : ℕ, 1 ≤ σ → Work.Peluse.Ulower.StepLe.SharpMassDDI σ := by
  intro σ hσ
  induction σ with
  | zero => omega
  | succ n ih =>
      match n with
      | 0 => simpa using h1
      | m + 1 => exact sharpMassDDI_step (σ := m + 1) (by omega) (ih (by omega)) h1

end

end Work.Peluse.Ulower.StepLe
