/-
# `Work.PSU3.BenderST` — the model facts for the distinguished involution

Peterfalvi II Ch. V §2 Lemma 2 c (and VI §1 2)) is applied to a *simple Bender group*
`Y = F/Z(F)` together with a split rank-one datum `(B,U,w)` of `Y` and a *distinguished*
involution `s ∈ U` (`w s w = r⁻¹ w r`, `r ∈ U`).  Since `Y` is then one of the three families
(`IsSimpleBenderGroup Y`), everything is a computation in the model, and this is the statement
recorded by the lead's design (`Submission/Work/PSU3/_design/PSU3Route.lean` §2, `BenderSTProp`).

For `q = |Inv B| + 1` exactly one of the three clauses holds:

* `PSL(2,q)`: `orderOf (s * w) = 3`, `U` abelian, `|U| = q`;
* `Sz(q)`: `orderOf (s * w) = 5`, `U` non-abelian, `|U| = q²`, and `x² = y² ⟹ x y⁻¹ ∈ ⟨Inv U⟩`;
* `PSU(3,q)`: `orderOf (s * w) = 3`, `|U| = q³`, and some `1 ≠ x ∈ B ∩ B^w` centralises
  `Inv(B)`.

The mathematics of the statement (its proof in the three models) belongs to area `Models`; the
definition lives here because the Stage A/B nodes of area `PSU3` need to name it.
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3

/-- **The model facts for the distinguished involution** (design §2): in a simple Bender group,
for a split rank-one datum `(B,U,w)` and a distinguished `s ∈ U`, the order of `s * w`, the size
and abelianness of `U`, Suzuki's "equal squares" clause and the `PSU(3,q)` centraliser clause. -/
def BenderSTProp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleBenderGroup Y →
    ∀ (B U : Subgroup Y) (w : Y), IsSplitRankOne B U w →
    ∀ s r : Y, s ∈ U → orderOf s = 2 → r ∈ U → w * s * w = r⁻¹ * w * r →
    let q := (involutions (B : Set Y)).ncard + 1
    (orderOf (s * w) = 3 ∧ IsAbelianSubgroup U ∧ Nat.card U = q) ∨
    (orderOf (s * w) = 5 ∧ ¬ IsAbelianSubgroup U ∧ Nat.card U = q ^ 2 ∧
      ∀ x ∈ U, ∀ y ∈ U, x ^ 2 = y ^ 2 →
        x * y⁻¹ ∈ Subgroup.closure (involutions (U : Set Y))) ∨
    (orderOf (s * w) = 3 ∧ Nat.card U = q ^ 3 ∧
      ∃ x ∈ twoPoint B w, x ≠ 1 ∧ ∀ u ∈ involutions (B : Set Y), x * u = u * x)

end Work.PSU3
