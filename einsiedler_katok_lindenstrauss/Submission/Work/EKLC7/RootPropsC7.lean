import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLRelCross.leafwise_crossSection
import Submission.Work.EKLC7.RootAeCovariant
import Submission.Work.EKLRelCross.isUInvariant_of_ae_translation
import Submission.Work.EKLRelCross.leafwise_luzin
import Submission.Work.EKLRelCross.atomic_trivial_of_covariant
import Submission.Work.EKLC6Core.trivial_ae_dichotomy
import Submission.Work.EKLC7.RootProporLemma
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# `Work.EKLC7.RootPropsC7` — `P_RootProps` for the commutator argument

This is the module `Submission/Work/EKLC7/RootProps.lean` (the C7 interface `P_RootProps`) as
proved by the C7 component.  It is kept as a separate file so that the C7 assembly
(`Submission/Work/EKLC7/CommutatorFromExistence.lean`) does not depend on the state of the
shared `RootProps.lean`, which other components edit concurrently.

The proof, clause by clause:

* (U3) `Work.EKLRelCross.leafwise_crossSection` at `U = Uij hij` (its `⇐` half is
  `crossSection_of_ae_dirac`, the `⇒` half Pisa 6.23);
* (U4) `Work.EKLRelCross.isUInvariant_of_ae_translation` (Pisa 6.27, the direction consumed
  by C7; this is `local_invariance_of_ae_haar` globalised by the contraction);
* (U5) `Work.EKLC7.RootProporClause`, the EKL (8) argument from the covariance (U7);
* (U7) `Work.EKLC7.RootAeCovariant` (= `Work.EKLRelCross.leafwise_acovariant` at `U = Uij hij`);
* (U8) `Work.EKLC6Core.trivial_ae_dichotomy` + `Work.EKLRelCross.atomic_trivial_of_covariant`
  (with the Luzin input `Work.EKLRelCross.leafwise_luzin`).

The horosphericality of `Uij hij` and its contracting vector `t0` come from
`Work.EKLContract.Lemmas.isHoro_Uij`, and the background component `P_X3` from
`Work.EKLComp.prove_X3`.
-/

set_option linter.unusedVariables false

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-- **`P_RootProps`**: clauses (U3)–(U5), (U7), (U8) of the frozen leafwise-measure contract,
restricted to the root groups `U_ij`. -/
theorem RootPropsC7 : Work.EKLC7.P_RootProps := by
  intro μ hprob hErg i j hij ν X' hL
  have hU : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  obtain ⟨t0, ht0⟩ := hU.2.2
  have hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hErg.1 t0
  -- (U7): the `A`-covariance of the leafwise system on a conull set
  obtain ⟨X'', hX''sub, hX''meas, hX''conull, hcov⟩ :=
    Work.EKLC7.RootAeCovariant Work.EKLComp.prove_X3 hij t0 hmp ht0 hL hErg.1
  have hcov' : Work.EKLC6Core.ACovariant ν X'' := hcov
  -- (U8): the ergodic dichotomy
  have hU8 : CrossSection μ (Uij hij) ∨ ∀ᵐ x ∂μ, ν x {1} = 0 := by
    by_cases htriv : ∀ᵐ x ∂μ, ν x = Measure.dirac 1
    · exact Or.inl (Work.EKLRelCross.crossSection_of_ae_dirac hL htriv)
    · refine Or.inr ?_
      have hnontriv : ∀ᵐ x ∂μ, ν x ≠ Measure.dirac 1 := by
        rcases Work.EKLC6Core.trivial_ae_dichotomy hL hU hcov' hX''conull hErg with h | h
        · exact absurd h htriv
        · exact h
      have hatomic : ∀ᵐ x ∂μ, ν x {1} > 0 → ν x = Measure.dirac 1 :=
        Work.EKLRelCross.atomic_trivial_of_covariant Work.EKLComp.prove_X3 μ (Uij hij) hU t0 hmp
          ht0 ν X' X'' hL hcov' hX''conull
          (Work.EKLRelCross.leafwise_luzin Work.EKLComp.prove_X3 μ (Uij hij) hU t0 hmp ht0 ν X' hL)
          hErg
      filter_upwards [hnontriv, hatomic] with x hne hatomic_x
      exact le_antisymm (le_of_not_gt fun hp => hne (hatomic_x hp)) zero_le
  refine ⟨?_, ?_, ?_, ⟨X'', hX''sub, hX''meas, hX''conull, hcov⟩, hU8⟩
  · -- (U3)
    exact Work.EKLRelCross.leafwise_crossSection Work.EKLComp.prove_X3 μ (Uij hij) hU t0 hmp ht0
      ν X' hL
  · -- (U4): a.e. right-`U_ij`-invariance of the leafwise measures forces `U_ij`-invariance
    -- of `μ` (Pisa 6.27, the direction consumed by the commutator argument).
    intro hae
    exact Work.EKLRelCross.isUInvariant_of_ae_translation Work.EKLComp.prove_X3 μ (Uij hij) hU t0
      hmp ht0 ν X' hL hae
  · -- (U5), from (U7) by EKL (8)
    exact RootProporClause hU t0 hmp ht0 hL hcov' hX''sub hX''conull

end Work.EKLC7
