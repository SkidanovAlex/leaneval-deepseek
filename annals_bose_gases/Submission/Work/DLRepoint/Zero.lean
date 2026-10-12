import ChallengeDeps
import Submission.Work.DLRepoint.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLRepoint.Zero` — the empty box at the faithful energy

The DL bound's two-arm split must handle the remainder count `n″ = 0` (the
`N ≡ 0 (mod n′)` case): superadditivity then involves `diagWeBAt 0`, and the
remainder arm's target bound is *negative*, so it is dominated by
`0 ≤ diagWeBAt 0`.

At zero particles the faithful word and the potential word both vanish
(`cnPlus`, `pDiagForm` and `qLHSden`/`qLHSword` are empty sums), so the
`eB`-infimum is `0` — this module records the (one-sided) form the assembly
consumes.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLRepoint

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The faithful box ground energy at zero particles is nonnegative.** -/
theorem diagWeBAt_zero_nonneg (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) (hs : 0 < s) :
    0 ≤ Work.BlockBound4.diagWeBAt 0 s μ v h c₀ cgap := by
  haveI : Nonempty (CSBox 0 s) := nonempty_CSBox 0 hs
  unfold Work.BlockBound4.diagWeBAt Work.KinPSuperadd.diagKinPeBAt Work.KinPSuperadd.slotEB
  refine le_ciInf (fun Φ => ?_)
  have hK : Work.KinPSuperadd.diagSlotWord s c₀ cgap 0 (Φ : X 0 → ℝ) = 0 := by
    unfold Work.KinPSuperadd.diagSlotWord
    simp [cnPlus, pDiagForm]
  have hqden : ∀ x : X 0, qLHSden 0 s μ (wPairC s v) (wPairC s (g0 v h)) x = 0 := by
    intro x
    simp [qLHSden, pairSet]
  have hq : (∫ x in abox 0 s, ((Φ : X 0 → ℝ) x) ^ 2
      * qLHSden 0 s μ (wPairC s v) (wPairC s (g0 v h)) x) = 0 := by
    simp [hqden]
  have h0 : Work.KinPSuperadd.blockE s μ (wPairC s v) (wPairC s (g0 v h))
      (Work.KinPSuperadd.diagSlotWord s c₀ cgap) 0 (Φ : X 0 → ℝ) = 0 := by
    unfold Work.KinPSuperadd.blockE
    rw [hK, hq, add_zero]
  rw [h0, zero_div]

end Work.DLRepoint
