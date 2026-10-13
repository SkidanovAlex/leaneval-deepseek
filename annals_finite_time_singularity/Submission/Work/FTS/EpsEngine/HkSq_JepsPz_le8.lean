/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkSq_JepsPz_le8.lean`

**The target: the counterflow `J_ε : X → ℋᵏ` for `k ≤ 8` in the projected, weighted space
`X`:**

  `HkSq α k (Pz (J_ε f)) ≤ C (C/ε)^{2k} EpsSq α f`   for every `k ≤ 8`,

with a constant `C > 0` depending only on the kernel `ρ`.

This is the order-`8` extension of the proved `Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le`
(`k ≤ 6`).  It is the order-`8` slot estimate
`Work.FTS.EpsEngine.EpsSqIter_mixed_Jeps_le_gen ρ hρ 8` fed into the assembly
`Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le8_of_slot` (module
`Submission/Work/FTS/EpsEngine/HkSq_JepsPz_le8Aux.lean`), which carries the whole proof.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8Aux
import Submission.Work.FTS.EpsEngine.EpsSqIter_mixed_Jeps_le_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The target.**  `J_ε` maps the weighted space `X` of the `ε`-scheme into the projected
`ℋᵏ`-space for every `k ≤ 8`, at a cost of one factor `C/ε` per derivative.

It is the order-`8` slot estimate `EpsSqIter_mixed_Jeps_le_gen ρ hρ 8` (`EpsSqIter_mixed_Jeps_le6`
was the `k ≤ 6` case) fed into the assembly `HkSq_JepsPz_le8_of_slot`, which is the proof of
`EpsSqTools.HkSq_JepsPz_le` with the order-`8` bump bound `exists_HkNorm_bump_le8` and the
cardinal constants `9`, `81`, `90`, `180` replacing `7`, `49`, `56`, `112`. -/
theorem HkSq_JepsPz_le8 (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ k : ℕ, k ≤ 8 → ∀ f : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
        Work.Spaces.HkSq α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
          ≤ C * (C / ε) ^ (2 * (k : ℕ)) * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := EpsSqIter_mixed_Jeps_le_gen ρ hρ 8
  exact Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le8_of_slot ρ hρ hC₀pos hC₀

end Work.FTS.EpsEngine
