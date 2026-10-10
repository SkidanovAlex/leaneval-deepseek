import Mathlib
import ChallengeDeps
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.exists_kleinData_ASGood
import Submission.Work.MotV5.exists_kleinData_shiftProj
import Submission.Work.MotV.certN_of_linkCert
import Submission.Work.MotV.not_gen_of_certN

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# Assembly of the characteristic-5 branch

This file contains the *assembly* of `theorem_1_2_3` in characteristic `5`: from a link certificate
`LinkCert (RatFunc 𝕜) F₁ F₂` for the two Artin–Schreier twists `F₁ = K(C^AS_f)`,
`F₂ = K(C^AS_{2f})` of the Klein curve (`f = fAS 𝕜 = t³ + t`), together with

* `ConstantsOnly 𝕜 F₁` (node **CO_AS**), and
* `IsEmpty (F₁ ≃ₐ[𝕜] F₂)` (node **RIG_AS**, proved from BR_AS, H1_AS, LAM_AS, TP_AS and V4_AS),

the two certificate levels give `¬ GenByPseudoRegularizable 𝕜 n` for `n ≥ 4`:

  `LinkCert` ⟶ `CertN 𝕜 n` (`Work.MotV.certN_of_linkCert`, node SPREAD)
  `CertN 𝕜 n` ⟶ `¬ GenByPseudoRegularizable 𝕜 n` (`Work.MotV.not_gen_of_certN`).

`not_gen_charFive_of` below is that assembly, with the three inputs as explicit hypotheses; it is
the characteristic-`5` analogue of `Work.MotV.not_gen_charNeFive` (`MOTIVIC_S45_LEAD.md` §C5,
node **ASM5**).  The remaining hypotheses of the challenge statement -- the existence of the
Klein data `D` and of the `E[5]`-structure `σS`, and the Artin–Schreier coefficient action `τ` --
are supplied by the proved nodes `Work.MotV5.exists_kleinData_ASGood`,
`Work.MotV5.exists_kleinData_shiftProj` and `Work.MotV5.coeffAut`; they are kept as parameters
here so that the assembly does not depend on the (long) proofs of the existence nodes.
-/

set_option autoImplicit false

namespace Work.MotV5

open Work.MotV

/-- **Node ASM5 (assembly).**  The characteristic-`5` branch of `theorem_1_2_3`: an
Artin–Schreier link certificate for the two twists `F_{f}` and `F_{2f}` of the Klein curve, with
`ConstantsOnly` for the first and rigidity for the pair, forces `¬ GenByPseudoRegularizable 𝕜 n`
for every `n ≥ 4`. -/
theorem not_gen_charFive_of (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 = 5)
    {n : ℕ} (hn : 4 ≤ n) (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (L : Work.MotV.LinkCert (RatFunc 𝕜) ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
      ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))
    (hCO : Work.MotV.ConstantsOnly 𝕜 ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS))
    (hR : IsEmpty (↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ≃ₐ[𝕜]
      ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n :=
  Work.MotV.not_gen_of_certN (𝕜 := 𝕜) (n := n)
    (Classical.choice (Work.MotV.certN_of_linkCert 𝕜 (F₁ := ↥(asTwistFieldTrue D
      (Work.MotV.fAS 𝕜) τ σS)) (F₂ := ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))
      L hCO hR n hn))

/-- **Node ASM5, existentially quantified form (`not_gen_charFive`).**  This is the form in which
the characteristic-`5` branch of `theorem_1_2_3` is actually consumed: it is enough to produce, for
*some* admissible Klein data, the three nodes of the branch

* `LK_AS`: a link certificate `LinkCert (RatFunc 𝕜) F_f F_{2f}` between the two Artin–Schreier
  twists of the Klein curve,
* `CO_AS`: `ConstantsOnly 𝕜 F_f`,
* `RIG_AS`: `IsEmpty (F_f ≃ₐ[𝕜] F_{2f})`,

in order to conclude `¬ GenByPseudoRegularizable 𝕜 n` for all `n ≥ 4`.  The data are produced from
`Work.MotV5.exists_kleinData_ASGood` / `Work.MotV5.exists_kleinData_shiftProj` and the twisting
bundles from the proved `Work.MotV5.Nodes.exists_ASData`; the two nodes `LK_AS` and `RIG_AS` are
stricter than what the existing certificates (which are stated for the refuted interpolation model
`asTwistField`) supply, hence the existential shape. -/
theorem not_gen_charFive_of_nodes (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 = 5)
    {n : ℕ} (hn : 4 ≤ n)
    (h : ∃ (D : Work.MotV.KleinData 𝕜)
      (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
      (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D),
      Work.MotV5.KleinData.ASGood D ∧
      Nonempty (Work.MotV.LinkCert (RatFunc 𝕜)
        ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
        ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) ∧
      Work.MotV.ConstantsOnly 𝕜 ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ∧
      IsEmpty (↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ≃ₐ[𝕜]
        ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n := by
  obtain ⟨D, τ, τ₂, σS, hD, ⟨L⟩, hCO, hR⟩ := h
  exact not_gen_charFive_of 𝕜 hk hn D hD τ τ₂ σS L hCO hR

/-- **The characteristic-`5` case of `theorem_1_2_3`, in the exact shape consumed by
`Work.MotV.theorem_1_2_3'_of_charFive`** (`Submission/Work/MotV/Final.lean`): the hypothesis `hFive`
of that file is
`∀ (𝕜) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 → ∀ {n}, 4 ≤ n → ¬ GenByPseudoRegularizable 𝕜 n`.

This theorem produces that hypothesis from the three nodes of the branch, existentially in the
Klein data: it is the complete statement of what is still missing in characteristic `5`, namely

* the link certificate `LK_AS` (§9.3 of `STATUS.md`: the two censuses, which are available, plus the
  Crauder–Katz chart `Φ`),
* `CO_AS` (constants-only for the first twist field), and
* `RIG_AS` (rigidity of the link, Proved above from `BR_AS` and `LAM_AS`). -/
theorem not_gen_charFive_all
    (hnodes : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 = 5),
      ∃ (D : Work.MotV.KleinData 𝕜)
        (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
        (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D),
        Work.MotV5.KleinData.ASGood D ∧
        Nonempty (Work.MotV.LinkCert (RatFunc 𝕜)
          ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
          ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) ∧
        Work.MotV.ConstantsOnly 𝕜 ↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ∧
        IsEmpty (↥(asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ≃ₐ[𝕜]
          ↥(asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))) :
    ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 → ∀ {n : ℕ}, 4 ≤ n →
      ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n :=
  fun 𝕜 _ _ hk {n} hn => not_gen_charFive_of_nodes 𝕜 hk hn (hnodes 𝕜 hk)

end Work.MotV5
