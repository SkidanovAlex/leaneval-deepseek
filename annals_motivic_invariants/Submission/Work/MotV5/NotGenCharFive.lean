import Mathlib
import ChallengeDeps
import Submission.Work.MotV5.Assembly
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Nodes.constantsOnly_AS
import Submission.Work.MotV5.Nodes.rigidity_AS

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The characteristic-`5` branch modulo the single link certificate

`Work.MotV5.not_gen_charFive_of` (`Assembly.lean`) reduces `¬ GenByPseudoRegularizable 𝕜 n`
(characteristic `5`, `n ≥ 4`) to three inputs for a single pair of admissible twisting data `D`,
`τ`, `τ₂`, `σS`: the link certificate `LK_AS`, constants-only `CO_AS` and rigidity `RIG_AS`.

Of those three, **`CO_AS` and `RIG_AS` are now proved** for every admissible datum —

* `Work.MotV5.Nodes.constantsOnly_AS` (`Nodes/constantsOnly_AS.lean`, from the proved
  `RigAS/constantsOnly_K_AS` and `RigAS/constantsOnly_transfer_AS`, using the bridge
  `Nodes/bridge_AS`, node **BR_AS**), and
* `Work.MotV5.Nodes.rigidity_AS` (`Nodes/rigidity_AS.lean`, axiom-clean, node **RIG_AS**),

so only the certificate remains.  This file performs that reduction explicitly: it produces the
exact hypothesis `hFive` of `Work.MotV.theorem_1_2_3'_of_charFive`
(`Submission/Work/MotV/Final.lean`) from one hypothesis — the existence, for every admissible
datum, of the Crauder–Katz link certificate between the two Artin–Schreier twist fields
(node **LK_AS**).
-/

set_option autoImplicit false

namespace Work.MotV5

open Work.MotV

/-- **The characteristic-`5` branch from the link certificate alone.**  Given, for every
characteristic-`5` infinite field `𝕜`, admissible Klein data `D` together with twisting data
`τ, τ₂, σS, σ, σ₂` and a link certificate between the two twist fields, one concludes
`¬ GenByPseudoRegularizable 𝕜 n` for all `n ≥ 4`; `ConstantsOnly` (`CO_AS`) and rigidity
(`RIG_AS`) are discharged by the proved nodes. -/
theorem not_gen_charFive_of_linkCert (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 = 5)
    {n : ℕ} (hn : 4 ≤ n) (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ)
    (h2 : Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂)
    (L : Work.MotV.LinkCert (RatFunc 𝕜)
      ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
      ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n := by
  haveI : CharP 𝕜 5 := by rw [← hk]; exact ringChar.charP 𝕜
  exact not_gen_charFive_of 𝕜 hk hn D hD τ τ₂ σS L
    (Nodes.constantsOnly_AS 𝕜 D hD (Work.MotV.fAS 𝕜) (Or.inl rfl) τ σS σ h1)
    (Nodes.rigidity_AS 𝕜 D hD τ τ₂ σS σ σ₂ h1 h2)

/-- **The characteristic-`5` branch in the exact shape `hFive` consumed by
`Work.MotV.theorem_1_2_3'_of_charFive`**, with the two proved nodes `CO_AS` and `RIG_AS`
discharged and the single remaining input (node **LK_AS**) isolated as a hypothesis. -/
theorem not_gen_charFive_all_of_linkCert
    (hLK : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 →
      ∃ (D : Work.MotV.KleinData 𝕜)
        (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
        (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
        (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜),
        Work.MotV5.KleinData.ASGood D ∧
        Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ ∧
        Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂ ∧
        Nonempty (Work.MotV.LinkCert (RatFunc 𝕜)
          ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
          ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))) :
    ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n := by
  intro 𝕜 _ _ hk n hn
  obtain ⟨D, τ, τ₂, σS, σ, σ₂, hD, h1, h2, ⟨L⟩⟩ := hLK 𝕜 hk
  exact not_gen_charFive_of_linkCert 𝕜 hk hn D hD τ τ₂ σS σ σ₂ h1 h2 L

/-- **The two twist fields of the link are *not* equal** (not merely non-isomorphic): an equality of
`IntermediateField`s would give an `AlgEquiv` (`IntermediateField.equivOfEq`), contradicting the
proved rigidity node `Work.MotV5.Nodes.rigidity_AS`.

Combined with `Work.MotAS.twistFieldAS_eq` (**AS-EQ**, proved in the sibling subproject) this
refutes the hypothesis `Work.MotAS.twistFieldAS D (2 • fAS 𝕜) = Work.MotAS.twistFieldAS D (fAS 𝕜)`
that `Work.MotAS.linkCertAS_of_census` consumes: that route to the certificate is vacuous, and the
genuine certificate has to come from the Crauder–Katz chart (see `STATUS.md` §12.4). -/
theorem asTwistFieldTrue_ne_two_smul (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ)
    (h2 : Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂) :
    asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS ≠
      asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS := by
  intro h
  haveI : IsEmpty (↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ≃ₐ[𝕜]
      ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) :=
    Nodes.rigidity_AS 𝕜 D hD τ τ₂ σS σ σ₂ h1 h2
  exact isEmptyElim ((IntermediateField.equivOfEq h).restrictScalars 𝕜)

end Work.MotV5
