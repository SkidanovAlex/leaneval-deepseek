import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.degenerateFamily
import Submission.Work.ThomBordism.nullBordismFamily_subtype
import Submission.Work.ThomBordism.assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The nonempty-family form of the transversality core implies the unrestricted one

`Work.ThomBordism.Man8` has no nonemptiness hypothesis, so the chapter's family statements quantify
over families with empty members, and the assembly `Work.ThomBordism.assembly` produces them (a
degenerate `Work.Drive.Smooth8` is replaced by `Man8.empty`).  The *producers* of the geometric data,
however, can only work with nonempty manifolds: `Work.Tubular.hasTubularNeighbourhood` and
`Work.Tubular.exists_collapse_genLoop` carry `[Nonempty V.pt]`, `TubeChart.inv : Euc N → NormalTotal E`
is a total function (so a tube chart of an empty manifold does not exist), and PTGEOMETRIC's
`Work.PTGeometric.GenuineTubeGeometry` is *uninhabited* for an empty piece.  Consequently the
producer-side deliverables are refutable as stated if they are universally quantified over all
families; the honest form is `Work.ThomBordism.TransversalityCoreFamilyNE` (and, on the data side, a
nonemptiness hypothesis `∀ i, Nonempty (F i).pt`).

This file proves that the restricted form *suffices*: `transversalityCoreFamily_of_nonempty`, by
dropping the empty members of a family (they contribute nothing:
`Work.ThomBordism.Man8.p1Sq_eq_zero_of_isEmpty` and friends, `degenerateFamily.lean`, plus the
`Finset` bookkeeping `Work.ThomBordism.Finset.sum_subtype_eq_sum_of_eq_zero`) and transporting the
null-bordism across the homeomorphism of the two `Σ`-types
(`Work.ThomBordism.nullBordismFamily_subtype`).  The consumer of the chapter therefore never has to
mention empty manifolds: a producer may state its deliverable with
`(∀ i, Nonempty (F i).pt) → …` and conclude `TransversalityCoreFamilyNE`, and use
`thomRational_of_transversalityCoreNE` (or `transversalityCoreFamily_of_nonempty`) here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff

attribute [local instance] Classical.propDecidable

namespace Work.ThomBordism

noncomputable section

/-- **The nonempty-family form of the transversality core implies the unrestricted one.** -/
theorem transversalityCoreFamily_of_nonempty (h : TransversalityCoreFamilyNE) :
    TransversalityCoreFamily := by
  intro ι _ F h1 h2
  have hkey1 : (∑ i : {i : ι // Nonempty (F i).pt}, (F i.1).p1Sq) = ∑ i, (F i).p1Sq :=
    Finset.sum_subtype_eq_sum_of_eq_zero (fun i => Nonempty (F i).pt) (fun i => (F i).p1Sq)
      (fun i hi => by
        haveI : IsEmpty (F i).pt := not_nonempty_iff.mp hi
        exact Man8.p1Sq_eq_zero_of_isEmpty (F i))
  have hkey2 : (∑ i : {i : ι // Nonempty (F i).pt}, (F i.1).p2Num) = ∑ i, (F i).p2Num :=
    Finset.sum_subtype_eq_sum_of_eq_zero (fun i => Nonempty (F i).pt) (fun i => (F i).p2Num)
      (fun i hi => by
        haveI : IsEmpty (F i).pt := not_nonempty_iff.mp hi
        exact Man8.p2Num_eq_zero_of_isEmpty (F i))
  have h1' : (∑ i : {i : ι // Nonempty (F i).pt}, (F i.1).p1Sq) = 0 := by
    rw [hkey1]; exact h1
  have h2' : (∑ i : {i : ι // Nonempty (F i).pt}, (F i.1).p2Num) = 0 := by
    rw [hkey2]; exact h2
  obtain ⟨N, hN, hW⟩ := h {i : ι // Nonempty (F i).pt} (fun i => F i.1) (fun i => i.2) h1' h2'
  obtain ⟨W⟩ := hW
  exact ⟨N, hN, nullBordismFamily_subtype F N W⟩

/-- **`Work.Drive.ThomRational` from the nonempty-family form of the transversality core.**  This is
`Work.ThomBordism.thomRational_of_transversalityCore` with the geometric input in its honest form. -/
theorem thomRational_of_transversalityCoreNE (hT : TransversalityCoreFamilyNE)
    (hσ : BoundarySigma) (hfund : Smooth8Fundamental) : Work.Drive.ThomRational :=
  thomRational_of_transversalityCore (transversalityCoreFamily_of_nonempty hT) hσ hfund

end

end Work.ThomBordism
