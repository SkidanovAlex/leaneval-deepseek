import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ZassenhausTwoGroup.card_quotient_eq
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.centralizer_le_H
import Submission.Work.ZassenhausTwoGroup.feit_lemma3_4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit 1960, Lemma 3.5: auxiliary vocabulary for the class count

This module only fixes the *notation* used by `feit_lemma3_5_classes`: the set of involutions of
`G`, the set of involutions inside `Q`, the elements satisfying the four conditions of the
counted conjugacy classes, and the various `Finset`s over which the counting proof sums.  No
mathematical content is asserted here; the lemmas about these sets are delivered in the sibling
modules.

Recall Feit's dictionary in the rank-one setting (`IsSplitRankOne H Q t`, `IsZassenhaus H`):
Feit's `M` is our `Q` (`m = |Q|`), Feit's `q` is `|D| = |twoPoint H t|`, and Feit's `G` is ours.
Write `I` for the involutions of `G`, `i = |Inv(Q)|`, `D = twoPoint H t` and `Ω = G ⧸ H` (so
`|Ω| = |Q| + 1`).

Feit's Lemma 3.5 is proved by counting the conjugacy classes `c` such that every element of `c`
is a product of two involutions, has order not dividing `2`, and is not conjugate into
`Q = M`.  The proof (`NOTES_LEAD_probe1630.md`, §3) counts ordered pairs of involutions and uses
that an involution lies in exactly one conjugate of `Q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Classical

namespace Work.ZassenhausTwoGroup

/-- The involutions of `G`, as a finset. -/
noncomputable def invFinset (G : Type) [Group G] [Fintype G] : Finset G :=
  Finset.univ.filter (fun u : G => orderOf u = 2)

/-- The involutions of `G` which lie in the subgroup `Q`. -/
noncomputable def invFinsetQ {G : Type} [Group G] [Fintype G] (Q : Subgroup G) : Finset G :=
  Finset.univ.filter (fun u : G => u ∈ Q ∧ orderOf u = 2)

/-- The elements of `G` satisfying the four conditions of the counted classes: nontrivial,
not an involution, a product of two involutions, and not conjugate into `Q`.  (This predicate is
invariant under conjugation, so it descends to a set of conjugacy classes.) -/
def goodPred {G : Type} [Group G] (Q : Subgroup G) (x : G) : Prop :=
  x ≠ 1 ∧ orderOf x ≠ 2 ∧
    (∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ x = u * v) ∧
    ∀ g : G, g * x * g⁻¹ ∉ Q

/-- The elements of `G` satisfying the four conditions of the counted classes. -/
noncomputable def goodElem {G : Type} [Group G] [Fintype G] (Q : Subgroup G) : Finset G :=
  Finset.univ.filter (fun x : G => goodPred Q x)

/-- The conjugacy classes counted by Feit's Lemma 3.5 (the right hand side of
`feit_lemma3_5_classes`), as a finset of `ConjClasses G`. -/
noncomputable def goodClasses {G : Type} [Group G] [Fintype G] (Q : Subgroup G) :
    Finset (ConjClasses G) :=
  Finset.univ.filter (fun c : ConjClasses G => ∀ x ∈ c.carrier, goodPred Q x)

/-- Ordered pairs of involutions lying in a common conjugate of `Q`. -/
noncomputable def sameConjPairs {G : Type} [Group G] [Fintype G] (Q : Subgroup G) :
    Finset (G × G) :=
  ((invFinset G) ×ˢ (invFinset G)).filter
    (fun p : G × G => ∃ g : G, p.1 ∈ Submission.Blueprint.conj g Q ∧
      p.2 ∈ Submission.Blueprint.conj g Q)

/-- Ordered pairs of involutions whose product is again an involution. -/
noncomputable def invProductPairs (G : Type) [Group G] [Fintype G] : Finset (G × G) :=
  ((invFinset G) ×ˢ (invFinset G)).filter (fun p : G × G => orderOf (p.1 * p.2) = 2)

/-- Ordered pairs of involutions with a prescribed product `x`. -/
noncomputable def prodFiberPairs (G : Type) [Group G] [Fintype G] (x : G) : Finset (G × G) :=
  ((invFinset G) ×ˢ (invFinset G)).filter (fun p : G × G => p.1 * p.2 = x)

/-- The involutions centralising a given element `u₀`. -/
noncomputable def centralizerInvols {G : Type} [Group G] [Fintype G] (u₀ : G) : Finset G :=
  Finset.univ.filter (fun w : G => orderOf w = 2 ∧
    w ∈ Subgroup.centralizer ({u₀} : Set G))

/-- The involutions of `G` lying in the conjugate of `Q` indexed by the point `ω` of
`Ω = G ⧸ H` (via the representative `Quotient.out ω`). -/
noncomputable def conjInvFinset {G : Type} [Group G] [Fintype G] (H Q : Subgroup G)
    (ω : G ⧸ H) : Finset G :=
  (invFinset G).filter (fun u => u ∈ Submission.Blueprint.conj (Quotient.out ω) Q)

/-- The sum of the orders of the centralisers of the elements of a conjugacy class. -/
noncomputable def classCentralizerSum {G : Type} [Group G] [Fintype G]
    (c : ConjClasses G) : ℕ := by
  classical
  exact ∑ x ∈ c.carrier.toFinset, Nat.card (Subgroup.centralizer ({(x : G)} : Set G))

end Work.ZassenhausTwoGroup
