import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.Margulis.nearId_conj_power_parametric
import Submission.Work.Mostow.Margulis.nearId_pair_commuting

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

/-! ## The target statement

`margulisPair` is assembled (in `Submission.Work.Mostow.margulisPairDefs`, via
`margulisPair_of_pieces`) from two delegated pieces:

* `Work.Mostow.Margulis.nearId_conj_power_parametric` (bounded-power pigeonhole): for every
  tolerance `η > 0` there are `N`, `δ > 0` such that for every point `u` there is a *single*
  conjugating element `h` with `h • 0 = u` so that every `g` displacing `u` by less than `δ`
  has a power `g^j`, `0 < j ≤ N`, with `h⁻¹ * g^j * h` within `η` of the identity;
* `Work.Mostow.Margulis.nearId_pair_commuting` (near-identity Margulis core): for a small
  `q > 0`, two elements of a discrete subgroup of `PO(n,1)` (`n ≥ 3`) that are `q`-close to
  the identity have commuting positive powers.

The supporting matrix estimates (entrywise near-identity `Near1`/`NearId`, the quadratic
contraction `near1_commutator`, the product/power/inverse bounds) and the assembly
(`isDiscrete_map_conj`, `margulisPair_of_pieces`) live in
`Submission.Work.Mostow.margulisPairDefs`.

-/

theorem margulisPair (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) → ∀ u : E n,
      ∀ γ δ : Γ, hdist u ((γ : PO n 1) • u) < ε → hdist u ((δ : PO n 1) • u) < ε →
        ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
          (γ : PO n 1) ^ m * (δ : PO n 1) ^ k = (δ : PO n 1) ^ k * (γ : PO n 1) ^ m
:= margulisPair_of_pieces n hn hA hI
    (Margulis.nearId_conj_power_parametric n hA hI)
    (Margulis.nearId_pair_commuting n hn hA hI)

end

end Work.Mostow
