import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_Defs
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts

theorem sep_HkSq_le {α : ℝ} {C : ℝ → ℝ} {B : ℝ → ℝ}
    (hAng : MeasureTheory.IntegrableOn
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C) Work.Spaces.Iθ)
    (hRad : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum B) Work.Spaces.Iz) :
    Work.Spaces.HkSq α 6 (fun z θ => C θ * B z)
      ≤ (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ)
        * (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum B z) := by
  -- The pointwise separation bound: on `Iθ` the `ℋ⁶`-integrand of `C·B` is dominated by the
  -- product of the angular block `AngBlk α C θ` and the radial slot sum `SlotSum B z`.
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z' θ' => C θ' * B z') z θ
        ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ
          * Work.FTS.StrongPersist.SlotSum B z := by
    intro z hz θ hθ
    have h1 := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
      (C := C) (B := B) (z := z) (θ := θ) hθ
    simpa only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk,
      Work.FTS.StrongPersist.SlotSum] using h1
  -- Integrate the bound in `θ` (the radial factor is a constant there).
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z' θ' => C θ' * B z') z θ)
        ≤ (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ)
          * Work.FTS.StrongPersist.SlotSum B z := by
    intro z hz
    have hmaj : MeasureTheory.Integrable
        (fun θ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ
          * Work.FTS.StrongPersist.SlotSum B z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hAng.mul_const _
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 6 (fun z' θ' => C θ' * B z') z θ
          ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ
            * Work.FTS.StrongPersist.SlotSum B z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    refine (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hmaj
      hae).trans (le_of_eq ?_)
    rw [MeasureTheory.integral_mul_const]
  -- Integrate in `z` (now the angular factor is the constant `∫_θ AngBlk`).
  have houter := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
    (hRad.const_mul (∫ θ in Work.Spaces.Iθ,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
  rw [MeasureTheory.integral_const_mul] at houter
  rw [Work.Spaces.HkSq]
  exact houter

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts
