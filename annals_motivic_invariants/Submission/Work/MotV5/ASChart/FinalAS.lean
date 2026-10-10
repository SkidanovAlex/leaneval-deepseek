import Mathlib
import Submission.Work.MotV5.ASChart.CensusAS2All
import Submission.Work.MotV5.Nodes.linkCert_AS_transport
import Submission.Work.MotV5.Nodes.exists_ASData
import Submission.Work.MotV5.exists_kleinData_shiftProj
import Submission.Work.MotV5.NotGenCharFive

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.FinalAS` — the characteristic-`5` branch of Theorem 1.2.3, closed

This is the assembly of every piece of the characteristic-`5` (Artin–Schreier) branch of the main
theorem:

* the admissible Klein data `D` with `ASGood D` and `ShiftCompatProj D` exist
  (`Work.MotV5.exists_kleinData_shiftProj`), together with the twisting data
  `τ, τ₂, σS, σ, σ₂` and the two `ASTwistData` (`Work.MotV5.Nodes.exists_ASData`);
* the link certificate between the two Artin–Schreier twist fields in the explicit
  Galois-coordinate model is `Work.MotV5.ASChart.linkCertAS`
  (`MotAS.CensusAS2` assembled from its five proved clauses in `CensusAS2All.lean`, plus my
  `Work.MotV5.ASChart.chartIsoAS2`), transported along node **AS-EQ** by
  `Work.MotV5.Nodes.linkCert_AS_of_twistFieldAS` (node **LK_AS**);
* `CO_AS` (`Work.MotV5.Nodes.constantsOnly_AS`) and `RIG_AS`
  (`Work.MotV5.Nodes.rigidity_AS`) are the proved nodes of
  `Work.MotV5.not_gen_charFive_of_linkCert` (`Submission/Work/MotV5/NotGenCharFive.lean`).

The result is the exact hypothesis `hFive` of `Work.MotV.theorem_1_2_3'_of_charFive`.
-/

set_option autoImplicit false

namespace Work.MotV5

open Work.MotV

/-- **The characteristic-`5` branch, unconditionally.**  For every infinite field `𝕜` of
characteristic `5` and every `n ≥ 4`, `GenByPseudoRegularizable 𝕜 n` fails. -/
theorem not_gen_charFive (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 = 5)
    {n : ℕ} (hn : 4 ≤ n) : ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n := by
  haveI : CharP 𝕜 5 := by rw [← hk]; exact ringChar.charP 𝕜
  obtain ⟨D, hD, hsh⟩ := Work.MotV5.exists_kleinData_shiftProj 𝕜
  obtain ⟨τ, τ₂, σS, σ, σ₂, h1, h2⟩ := Work.MotV5.Nodes.exists_ASData 𝕜 D hD hsh
  exact Work.MotV5.not_gen_charFive_of_linkCert 𝕜 hk hn D hD τ τ₂ σS σ σ₂ h1 h2
    (Classical.choice (Work.MotV5.Nodes.linkCert_AS_of_twistFieldAS 𝕜 D hD τ τ₂ σS σ σ₂ h1 h2
      (Classical.choice (Work.MotV5.ASChart.linkCertAS 𝕜 D hD))))

/-- **The characteristic-`5` branch in the exact `hFive` shape** consumed by
`Work.MotV.theorem_1_2_3'_of_charFive` (named `_hFive` to avoid the conditional
`Work.MotV5.not_gen_charFive_all` of `MotV5/Assembly.lean`, which takes the three nodes as a
hypothesis). -/
theorem not_gen_charFive_hFive :
    ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n :=
  fun 𝕜 _ _ hk {n} hn => not_gen_charFive 𝕜 hk hn

end Work.MotV5
