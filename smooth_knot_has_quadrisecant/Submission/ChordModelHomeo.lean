import Mathlib
import Submission.ChordParam
import Submission.CirclePairs
import Submission.MobiusModel

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S274 — the plane-model homeo `OpenMobius ≃ₜ MobiusModel`: class-level
descent seeds (VERIFIED, sorry-free)

The missing link of the Möbius winding route (ROADMAP S273) is the
plane-model homeomorphism between the abstract open Möbius band of secants
and the plane chord model:

    OpenMobius ≃ₜ MobiusModel

composed as `CirclePairs.openMobiusCircleEquiv : OpenMobius ≃ₜ
CircleOpenPairs` (the parameter-circle transport, verified) followed by the
two-point→chord-line homeomorphism `CircleOpenPairs ≃ₜ MobiusModel`.  The
analytic core of the two-point→chord map is complete in
`Submission/ChordParam.lean` (the "second half of the OpenMobius ≃
MobiusModel bridge"): `chordDataOf u v h` (unit normal + signed offset of
the chord through `u, v`), `backwardOrdered q` (the two unit points of the
chord `q`), with the four bijection identities at the relation level —
`chordDataOf_swap` (the forward map is swap-invariant), `backwardOrdered_flip_rel`
(the backward map is flip-invariant), `chordDataOf_backwardOrdered`
(forward∘backward = id), `backwardOrdered_of_chordDataOf_rel`
(backward∘forward = id up to the swap).

This module starts the *quotient descent* layered on top: the class-level
translations of those four identities — the descent seeds from which the
type-level `Equiv` (and then, through the open-quotient-map machinery of
`SecantSpace`/`MobiusModel`, the `Homeomorph`) is assembled:

1. **`forward_swap_invariant`** — the forward class is invariant under
   swapping the two endpoints:
   `mobiusMk (chordDataOf u v h) = mobiusMk (chordDataOf v u (Ne.symm h))`
   (a one-line translation of `chordDataOf_swap` through `Quotient.sound`);
2. **`backward_flip_invariant`** — the backward pair-class is invariant
   under flipping the chord data:
   `⟦(backwardOrdered (chordFlip q))⟧ = ⟦(backwardOrdered q)⟧` in
   `CircleUnordPairs` (from `backwardOrdered_flip_rel` +
   `circleUnordMk_eq_iff`);
3. **`backwardOrdered_forward_id`** — forward of the backward pair is the
   original chord data:
   `mobiusMk (chordDataOf (backwardOrdered q) hq) = mobiusMk q`
   (`congrArg mobiusMk` of `chordDataOf_backwardOrdered`);
4. **`forward_backward_id`** — backward of the forward pair is the
   original unordered pair:
   `⟦(backwardOrdered (chordDataOf u v h))⟧ = ⟦(u, v)⟧` (from
   `backwardOrdered_of_chordDataOf_rel` + `circleUnordMk_eq_iff`).

STATUS after S274: the four quotient-descent seeds are verified; the next
steps of the bridge are (a) the type-level maps on the restricted quotient
types (off-diagonal classes ↔ chord data) using these invariance proofs
with the `Quotient.out`/`liftOn` bookkeeping, (b) the mutual-inverse proof
from the two round-trip lemmas, (c) the `Homeomorph` by continuity of both
sides through the open-quotient-map machinery.  Tree green; TWO documented
sorries; no children pending.
-/

/-- **The forward class is swap-invariant (VERIFIED)**: the chord data of
the ordered pair `(u,v)` and of the swapped pair `(v,u)` lie in the same
flip class of `MobiusModel` — the forward map descends to the unordered
pair (one-line translation of `chordDataOf_swap` through
`Quotient.sound`). -/
lemma forward_swap_invariant (u v : Circle) (h : u ≠ v) :
    mobiusMk (chordDataOf u v h) = mobiusMk (chordDataOf v u (Ne.symm h)) := by
  unfold mobiusMk
  exact Quotient.sound (Or.inr (chordDataOf_swap u v h).symm)

/-- **The backward pair-class is flip-invariant (VERIFIED)**: the unordered
pair of the two chord endpoints of `q` and of the flipped data
`chordFlip q` are the same unordered pair — the backward map descends
through the flip (from `backwardOrdered_flip_rel` +
`circleUnordMk_eq_iff`). -/
lemma backward_flip_invariant (q : ChordData) :
    (⟦(backwardOrdered (chordFlip q) : Circle × Circle)⟧ :
        CircleUnordPairs) =
      (⟦(backwardOrdered q : Circle × Circle)⟧ : CircleUnordPairs) := by
  exact (circleUnordMk_eq_iff (backwardOrdered (chordFlip q)) (backwardOrdered q)).mpr
    (backwardOrdered_flip_rel q)

/-- **Forward of the backward pair is the original chord data (VERIFIED)**:
`mobiusMk (chordDataOf (backwardOrdered q).1.1 (backwardOrdered q).1.2
hq) = mobiusMk q` — the forward∘backward round trip is the identity at the
class level (`congrArg mobiusMk` of `chordDataOf_backwardOrdered`). -/
lemma backwardOrdered_forward_id (q : ChordData) :
    mobiusMk (chordDataOf (backwardOrdered q).1.1 (backwardOrdered q).1.2
      (backwardOrdered q).2) = mobiusMk q := by
  exact congrArg mobiusMk (chordDataOf_backwardOrdered q)

/-- **Backward of the forward pair is the original unordered pair
(VERIFIED)**: `⟦(backwardOrdered (chordDataOf u v h))⟧ = ⟦(u, v)⟧` — the
backward∘forward round trip is the identity at the class level (from
`backwardOrdered_of_chordDataOf_rel` + `circleUnordMk_eq_iff`). -/
lemma forward_backward_id (u v : Circle) (h : u ≠ v) :
    (⟦(backwardOrdered (chordDataOf u v h) : Circle × Circle)⟧ :
        CircleUnordPairs) = ⟦(u, v)⟧ := by
  exact (circleUnordMk_eq_iff (backwardOrdered (chordDataOf u v h)) (u, v)).mpr
    (backwardOrdered_of_chordDataOf_rel u v h)

end LeanEval.KnotTheory.Quadrisecant
