import Submission.Work.Serre.serreS2OfC0C2oddS1
import Submission.Work.RatHurewicz.freudenthalTorsionTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Freudenthal's suspension theorem in the SERRE vocabulary

`Work.Serre.SerreFreudenthal` is one of the inputs of the chapter's `S2` assembly
(`Work.Serre.serreS2OfC0C2oddS1`, proved) and of the range-form assembly
`Work.Stems.Engine.stableStemsTorsion_of_rangeInputs`.  Its content is exactly
`Work.Stems.FreudenthalTorsionTransfer` (area RATHUREWICZ / STEMS), which is **proved** from
homotopy excision in `Submission/Work/RatHurewicz/freudenthalTorsionTransfer.lean`; the only
difference is the spelling of the sphere model (both use `Metric.sphere (0 : ℝ^{n+1}) 1`) and the
way the degree is written (`n + 1 + i` versus `n + i + 1`).  This file records the transport
`piTorsion_of_index_eq`, so that `SerreFreudenthal` is no longer an open input.
-/

namespace Work.Stems.Engine

open Work.Serre

noncomputable section

/-- **Freudenthal, in the SERRE vocabulary**, from the proved suspension transfer of area STEMS. -/
theorem serreFreudenthal : Work.Serre.SerreFreudenthal := by
  intro n i hn hi htop x₀
  have htop' : ∀ y₀ : Sph (n + 1), PiTorsion (Sph (n + 1)) y₀ (n + i + 1) :=
    fun y₀ => piTorsion_of_index_eq y₀ (by omega) (htop y₀)
  have h := Work.RatHurewicz.freudenthalTorsionTransfer n i hn hi
    (fun y₀ β => htop' y₀ β) x₀
  exact h

end

end Work.Stems.Engine
