import Submission.Work.Item3.RowInvariant
import Submission.Work.Item3.UnchangedLow

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# OtherRCOverlap: the OTHER-rc overlap-configuration skeleton

The OTHER-rc branch of U1 (`lowRC_nonempty_endInv`, `UnchangedLow.lean`):
a genuine-run post-pass state whose low even row `q` has an inhabited right
covering class `RightCoverClass (second half)` with the second half outside
{B_p, invRev A_p} is never residual — some strict boundary cancellation
exists (machine: 25+ traces, n = 3..7, all posts non-residual; see
`FallTwoRunNotes.md`).  The dissection of genuine-OTHER traces shows the
strict cancellations are **multi-flavoured**: every flavour is a heavy
suffix/prefix overlap between two rows reducing to a single letter, but
there is no single telescoping identity.  This module makes the
classification a formal object:

* `OtherRCShape` — the flavour enum (skeleton; constructors correspond to
  the verified trace shapes, expected to be refined as data grows):
  * `begTelescopeRight`    : coverer u begins `y⁻¹` and `u = y⁻¹ ++ invRev v`;
                            strict rho `u ↦ u·v` telescopes to `y⁻¹`
                            (traces 1,2: u = aBD, v = db = A_p·b, u·v = a).
  * `begTelescopeInvRight` : coverer u begins `y⁻¹` and `u = y⁻¹ ++ v`;
                            strict rho `u ↦ u·v⁻¹` telescopes to `y⁻¹`
                            (trace 5: u = AcD = A·cD, v = cD, u·v⁻¹ = A).
  * `prefixOverlap`        : `v = invRev u ++ extra`; strict rho
                            `u ↦ u·v` telescopes to `extra`
                            (trace 6: u = bc, v = CBC = invRev(bc)·C, u·v = C).
  * `covererExtendsPartner`: `u = v ++ s`; strict lam `u ↦ v⁻¹·u`
                            telescopes to `s` (traces 7,10: u = v·y).
  * `partnerExtendsCoverer`: `v = u ++ s`; strict lam `u ↦ v⁻¹·u`
                            telescopes to `s⁻¹` (traces 4,9).
  * `covererPairOverlap`   : two rc-coverers (both ending with `y` or both
                            beginning with `y⁻¹`) telescope against each
                            other by multi-cancellation — the strict move
                            does not involve `q` or a single coverer-partner
                            pair (n=4 volume: 3 of 49 OTHER-rc posts, e.g.
                            `['dBab','dBaab','Ab','dc']` with the move
                            `w0 ↦ w1⁻¹·w0` telescoping `dBab` to `BAb`;
                            the two rows `dBab`, `dBaab` are exactly the
                            rows ending with `y = b`).
  * `boundaryZipper`       : the words meet as a "zipper": `W_u = X_a ++ Z`,
                            `W_v = invRev Z ++ X_b` (the suffix `Z` of one
                            row is the inverse-reversal of the prefix of the
                            other), so `W_u · W_v` telescopes to
                            `reduce (X_a ++ X_b)` (n=4 volume: the third
                            uncovered trace `['Ca','dB','ACaD','dAcca']`,
                            where `ACaD`'s suffix `a C D`... in letters the
                            suffix `D a C` zippers into `dAcca`'s prefix
                            `d A c`; the strict drop is `ACaD · dAcca = Aca`,
                            `|W_v| = 5 < 2 * 3`).
  * `otherPair`            : residual catch-all (no instance found after
                            the tuple-vs-list bug in the machine predicate
                            was fixed; kept for the record).

* pure word-telescoping atoms (PROVEN, sorry-free) — the `rho`/`lam`
  reductions each constructor's strict move reduces to:
  * `mul_mk_app_invRev`    : `(mk (P ++ invRev L)) * mk L = mk P`
  * `mul_mk_append_invRev` : `(mk L) * mk (invRev L ++ P) = mk P`
  * `mul_mk_invRev_prefix` : `(mk (invRev L)) * mk (L ++ P) = mk P`

* `otherRC_strict_drop` — the state-level container each constructor's
  word identity is meant to feed (open): an OTHER-rc low row in a
  genuine-run post-pass state forces a strict closure move.

All kernel-checked lemmas have axioms `[propext, Classical.choice,
Quot.sound]`; the shape enum and containers are the record, no `sorry`.
-/

namespace Submission.Nielsen

/-- The flavour of the strict boundary cancellation that an OTHER-rc
configuration produces (skeleton, from machine traces). -/
inductive OtherRCShape where
  | begTelescopeRight
  | begTelescopeInvRight
  | prefixOverlap
  | covererExtendsPartner
  | partnerExtendsCoverer
  | covererPairOverlap
  | boundaryZipper
  | otherPair

namespace OtherRCShape

/-- Human-readable name of the flavour (for records/logs). -/
def toString : OtherRCShape → String
  | begTelescopeRight => "begTelescopeRight"
  | begTelescopeInvRight => "begTelescopeInvRight"
  | prefixOverlap => "prefixOverlap"
  | covererExtendsPartner => "covererExtendsPartner"
  | partnerExtendsCoverer => "partnerExtendsCoverer"
  | covererPairOverlap => "covererPairOverlap"
  | boundaryZipper => "boundaryZipper"
  | otherPair => "otherPair"

end OtherRCShape

/-! ### Pure word-telescoping atoms (PROVEN) -/

/-- `P ++ invRev L ++ L` telescopes to `P` at the element level: a word
made of `P` followed by `invRev L` right-multiplied by `L` is `P`
(the `begTelescopeRight` atom: `u = y⁻¹ ++ invRev v` gives `u·v = y⁻¹`). -/
theorem mul_mk_app_invRev {α : Type*} [DecidableEq α]
    (P L : List (α × Bool)) :
    FreeGroup.mk (P ++ FreeGroup.invRev L) * FreeGroup.mk L = FreeGroup.mk P := by
  rw [FreeGroup.mul_mk]
  apply FreeGroup.reduce.exact
  rw [List.append_assoc]
  rw [← FreeGroup.reduce_append_reduce_reduce (L₁ := P) (L₂ := FreeGroup.invRev L ++ L)]
  rw [FreeGroup.reduce_invRev_left_cancel]
  simp

/-- `L ++ invRev L ++ P` telescopes to `P`: a word made of `L` followed by
`invRev L ++ P` right-multiplied onto `L` is `P` (the `prefixOverlap`
atom: `v = invRev u ++ extra` gives `u·v = extra`). -/
theorem mul_mk_append_invRev {α : Type*} [DecidableEq α]
    (P L : List (α × Bool)) :
    FreeGroup.mk L * FreeGroup.mk (FreeGroup.invRev L ++ P) = FreeGroup.mk P := by
  rw [FreeGroup.mul_mk]
  apply FreeGroup.reduce.exact
  rw [← List.append_assoc]
  rw [← FreeGroup.reduce_append_reduce_reduce (L₁ := L ++ FreeGroup.invRev L) (L₂ := P)]
  rw [reduce_append_invRev_right L]
  simp

/-- `invRev L · (L ++ P)` telescopes to `P` (the `covererExtendsPartner`
atom: `u = v ++ s` gives `v⁻¹·u = s`). -/
theorem mul_mk_invRev_prefix {α : Type*} [DecidableEq α]
    (P L : List (α × Bool)) :
    FreeGroup.mk (FreeGroup.invRev L) * FreeGroup.mk (L ++ P) = FreeGroup.mk P := by
  rw [FreeGroup.mul_mk]
  apply FreeGroup.reduce.exact
  rw [← List.append_assoc]
  rw [← FreeGroup.reduce_append_reduce_reduce (L₁ := FreeGroup.invRev L ++ L) (L₂ := P)]
  rw [FreeGroup.reduce_invRev_left_cancel]
  simp


/-- `mk (invRev L) * mk L = 1`: the inverse-reversal word is the group
inverse. -/
private lemma mk_invRev_mul_self {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    FreeGroup.mk (FreeGroup.invRev L) * FreeGroup.mk L = 1 := by
  rw [FreeGroup.mul_mk]
  rw [← FreeGroup.reduce.self (L := FreeGroup.invRev L ++ L)]
  rw [FreeGroup.reduce_invRev_left_cancel]
  rfl

/-- `invRev (P ++ S ++ [y]) · (P ++ [y]) = y⁻¹ · invRev S · y` (element
identity): the shared prefix `P` cancels against `invRev P` in the middle
(the `covererPairOverlap` atom: two rc-coverers sharing a prefix `P`, one
with an extra block `S` before the common tail letter `y`, telescope to a
word of length at most `|S| + 2`). -/
theorem mul_mk_invRev_shared_prefix {α : Type*} [DecidableEq α]
    (P S : List (α × Bool)) (y : α × Bool) :
    FreeGroup.mk (FreeGroup.invRev (P ++ S ++ [y])) * FreeGroup.mk (P ++ [y]) =
      FreeGroup.mk (FreeGroup.invRev [y] ++ FreeGroup.invRev S ++ [y]) := by
  rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
  simp only [← FreeGroup.mul_mk, mul_assoc]
  rw [← mul_assoc (FreeGroup.mk (FreeGroup.invRev P)) (FreeGroup.mk P) (FreeGroup.mk [y])]
  rw [mk_invRev_mul_self P]
  simp

/-- `mk (invRev Z) = (mk Z)⁻¹`. -/
private lemma mk_invRev_eq_inv {α : Type*} [DecidableEq α] (Z : List (α × Bool)) :
    FreeGroup.mk (FreeGroup.invRev Z) = (FreeGroup.mk Z)⁻¹ :=
  eq_inv_of_mul_eq_one_left (mk_invRev_mul_self Z)

/-- **Zipper atom.**  If the suffix `Z` of one word is the inverse-reversal of
the prefix of another (`W_u = X_a ++ Z`, `W_v = invRev Z ++ X_b`), then
`W_u · W_v = X_a · X_b` (element identity): the matched boundary blocks
`Z · invRev Z` cancel.  This is the `boundaryZipper` constructor's overlap
content. -/
theorem mul_mk_zipper {α : Type*} [DecidableEq α]
    (Xa Xb Z : List (α × Bool)) :
    FreeGroup.mk (Xa ++ Z) * FreeGroup.mk (FreeGroup.invRev Z ++ Xb) =
      FreeGroup.mk (Xa ++ Xb) := by
  rw [FreeGroup.mul_mk]
  simp only [← FreeGroup.mul_mk]
  rw [mk_invRev_eq_inv Z]
  group

/-- **State-level container (open):** an OTHER-rc low row in a genuine-run
post-pass state forces a strict closure move (`otherRC_forces_strict`,
`UnchangedLow.lean`); the per-shape word identities above are the atoms the
case split consumes. -/
def otherRC_strict_drop {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  otherRC_forces_strict S p A B α'

end Submission.Nielsen
