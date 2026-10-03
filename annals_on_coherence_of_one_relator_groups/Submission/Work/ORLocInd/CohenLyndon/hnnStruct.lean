import Mathlib
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORLocInd.CohenLyndon.bsStructure

set_option autoImplicit false

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver

/-- **Bass--Serre structure theorem** (thin wrapper around
`Work.ORLocInd.CohenLyndon.bsStructure`).

Let `Γ` act on a non-empty tree `V` without inversions and with all edge stabilisers trivial, and
suppose that the quotient graph `V/Γ` is again a tree.  Then `Γ` is the free product of the
stabilisers of a set of representatives `x i` of the vertex orbits.

The hypothesis `Nonempty V` is essential: for `V = ∅` all the other hypotheses are vacuous and the
conclusion would force `Γ` to be trivial. -/
theorem hnn_struct {Γ : Type u} {V : Type u} [Group Γ] [Quiver.{u, u} V]
    [Quiver.HasInvolutiveReverse V] [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]
    [Nonempty V]
    (hT : Work.ORBassSerre.IsTree V) (hninv : Work.ORBassSerre.ActsWithoutInversions Γ V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer Γ e = ⊥)
    (hquot : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV Γ V)) :
    ∃ (Ω : Type u) (x : Ω → V),
      (∀ v : V, ∃ i : Ω, ∃ g : Γ, v = g • x i) ∧
      (∀ i j : Ω, (∃ g : Γ, x i = g • x j) → i = j) ∧
      ∃ e : Monoid.CoprodI (fun i : Ω => ↥(MulAction.stabilizer Γ (x i))) ≃* Γ,
        ∀ (i : Ω) (z : ↥(MulAction.stabilizer Γ (x i))),
          e (Monoid.CoprodI.of z) = (z : Γ) :=
  bsStructure hT hninv hedge hquot

end Work.ORLocInd.CohenLyndon
