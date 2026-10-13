/-
Copyright: work module for the Elgindi finite-time singularity project.

# The unfolding bookkeeping for the repaired `ip4SlotDom`

`Submission/Work/FTS/TransportS/NOTES_ip4SlotDom.md` records that the *rooted* statement of
`ip4SlotDom` (with an *arbitrary* pointwise weight `ρ ≤ slotW α a` in each slot, i.e. the
original `leafSum`) is FALSE: the unfolding of `IP4` contains the `w² sin(2θ)^{-η}`-weighted
pairing at **every** slot `(a,b)` (`10`-term and `10^10`-term of `H1IP`), not only at the slots
with `a = 0`, while the original `leafSum` carried that weight only at `a = 0`.

The repaired leaf sum `Work.FTS.TransportS.leafSum` (see `Slots.lean`, written after that
note) contains the two weights `w² sin(2θ)^{-η}` and `w²` at **every** slot `(a,b)` with
`a + b ≤ 4`, and the weight `w² sin(2θ)^{-γ}` at every such slot with `a ≥ 1` (the same
`a ≥ 1` guard as `IsLeafW`).  With this repair the domination of `IP4` by the leaf sum is a
purely *combinatorial* statement:

* `IP4 α = HkIPStep 1 1 (HkIPStep 1 1 (HkIPStep 1 1 (H1IP α)))` unfolds into `Σ_{w}` of
  `H1IP α (w u) (w v)` over the 15 words `w` in `D_θ, D_z` of length `≤ 3`;
* each `H1IP α X Y` is a linear combination (coefficients `10, 10^10, 10^17, 10^21`) of the
  four slot pairings with the three leaf weights at the slots `(0,0)`, `(0,1)`, `(1,0)`; the
  `γ`-weight (coefficient `10^21`) always acts on `D_θ X`, so its slot has `a ≥ 1`;
* each word applied to `u` is `D_z^bD_θ^a u` with `a` (resp. `b`) the number of `D_θ`'s
  (resp. `D_z`'s) in the word — because the two operators **commute** on the open quadrant
  (`D_θ = sin 2θ ∂_θ` and `D_z = z ∂_z` have multipliers depending on the *other* variable),
  which is Clairaut's theorem on the open quadrant and needs only `SmoothOpen u`.

This file sets up the two objects that make the induction above precise:

* `SlotSum α n u v` — the sum of `|slotPairing ρ a b u v|` over the slots `a + b ≤ n` and the
  three leaf weights `ρ` (with the same `a ≥ 1` guard for the `γ`-weight as `leafSum`);
* `IPn α n` — the coercive recursion iterated `n` times from `H1IP` (so
  `IPn α 3 = IP4 α`).

The analytic input (the two commutation identities and the resulting shifts of the slot sums)
and the finite-sum API live in the sibling modules; everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.CoercivityStep.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The slot sum of level `n`**: the sum of the absolute values of the slot pairings with the
leaf weights of `H1IP`, over the slots `(a,b)` with `a + b ≤ n`.  The `a ≥ 1` guard on the
`γ`-weight is the one of `leafSum`/`IsLeafW` (the `10^21`-term of `H1IP` acts on a `D_θ` and
therefore always sits at a slot with `a ≥ 1`).

This is the quantity that the unfolding of `IPn α n` is bounded by at level `n + 1`: each
`HkIPStep` raises the order of the slot by one, and each `H1IP` adds at most one more. -/
def SlotSum (α : ℝ) (n : ℕ) (u v : Fn) : ℝ :=
  ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
    (|slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
      + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0))

/-- **The summand of `SlotSum`**: the sum of the absolute values of the three leaf weightings of
the slot `(a,b)`, with the `a ≥ 1` guard on the `γ`-weight. -/
def SlotTerm (α : ℝ) (a b : ℕ) (u v : Fn) : ℝ :=
  |slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
    + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0)

/-- `SlotSum` is the sum of the summands `SlotTerm`. -/
theorem SlotSum_eq_sum_SlotTerm (α : ℝ) (n : ℕ) (u v : Fn) :
    SlotSum α n u v
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b u v := rfl

/-- The summand of the slot sum is nonnegative. -/
theorem SlotTerm_nonneg (α : ℝ) (a b : ℕ) (u v : Fn) : 0 ≤ SlotTerm α a b u v := by
  unfold SlotTerm
  refine add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  by_cases h : 1 ≤ a
  · rw [if_pos h]; exact abs_nonneg _
  · rw [if_neg h]

/-- **The coercive recursion iterated `n` times.**  `IPn α 0 = H1IP α` and
`IPn α (n+1) = HkIPStep 1 1 (IPn α n)`, so `IPn α 3` is exactly the `IP4 α` of
`Work.FTS.CoercivityStep.Assembly`, the inner product of the `ℋ⁴` coercivity. -/
def IPn (α : ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | (n + 1) => Work.Coercivity.HkIPStep 1 1 (IPn α n)

/-- The three-step iterate is the assembled `IP4` of the coercivity chapter. -/
theorem IPn_three_eq_IP4 (α : ℝ) : IPn α 3 = Work.FTS.CoercivityStep.IP4 α := rfl

/-- The slot sum of level `n` is nonnegative (it is a sum of absolute values). -/
theorem SlotSum_nonneg (α : ℝ) (n : ℕ) (u v : Fn) : 0 ≤ SlotSum α n u v := by
  unfold SlotSum
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  refine add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  by_cases h : 1 ≤ a
  · rw [if_pos h]; exact abs_nonneg _
  · rw [if_neg h]

end Work.FTS.TransportS
