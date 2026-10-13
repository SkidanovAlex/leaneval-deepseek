import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotCore
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.LeafShiftCSLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-six transport row with the coefficient `L₁₂(f)·D_θ f`.**

The pairing `slotPairing ρ a b (L₁₂(f)·D_θf) f` is expanded by Leibniz in the radial coefficient
`L₁₂ f` (`T4bSlotCore`); the `k = 0` term is the `θ`-integration by parts of the extra angular
derivative (`L12ShiftThetaLe`), the intermediate `k` are dominated pointwise by the `ℋ⁶`
integrand against the uniform `z`-jet bounds `L12Sup4`/`L12Sup6`, and the top two slots are
priced by two-level Cauchy–Schwarz (`LeafShiftCSLe`). -/
theorem T4bRowSlot : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C4, hC4pos, hsup4⟩ := L12Sup4
  obtain ⟨C6, hC6pos, hsup6⟩ := L12Sup6
  obtain ⟨Ccs, hCcspos, hcs⟩ := LeafShiftCSLe
  obtain ⟨C0, hC0pos, h0le⟩ := L12ShiftThetaLe
  exact T4bRowSlot_core hCcspos hC0pos hC4pos hC6pos hsup4 hsup6
    (fun X g hX hg => Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hg) hcs h0le

end Work.FTS.StrongPersist.H6Pair6Aux
