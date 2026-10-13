/-
  annals_wilkies_conjecture, AREA E3 (`Submission.Work.WilE3`): `E3_taylor_closure`, conditional
  only on the lead's separable-chain Khovanskii node.

  `hK : ∀ F, Work.WilE3.SepKhovanskiiET F` is the same hypothesis that
  `Work.WilE3.E3_identity_proved` takes (definitionally the lead's GAP-1
  `Work.WilE3K.SepKhovanskiiET`).  From it: `Realify.MultiplicityBound_of_ET hK` supplies
  `MultiplicityBound`, `Taylor.maximalPsiNode hK` supplies Gabrielov 1998's maximal-`ψ` estimate,
  and `Taylor.E3_taylor_closure_proved_of_multiplicity` closes the frozen biconditional.
-/
import Submission.Work.WilE3.Taylor.E3_taylor_closure_proved_of_multiplicity
import Submission.Work.WilE3.Taylor.maximalPsiNode

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

namespace Work.WilE3

/-- **`E3_taylor_closure`** (GV Cor. 4.5), in the exact form of the frozen
`WilkiesDesign.E.E3_taylor_closure`, from the lead's separable-chain Khovanskii node only. -/
theorem E3_taylor_closure_proved_hK (hK : ∀ F : ℕ, SepKhovanskiiET F) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
    (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
    (y ∈ closure {x | B.holds c x} ↔
      y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
                       (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}) :=
  Taylor.E3_taylor_closure_proved_of_multiplicity (Realify.MultiplicityBound_of_ET hK)
    (Taylor.maximalPsiNode hK)

end Work.WilE3
