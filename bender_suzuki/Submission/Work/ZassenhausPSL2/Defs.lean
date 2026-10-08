import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausPSL2`: the split rank-one (Zassenhaus) data of a Bender group

This file fixes the vocabulary of the area.  The main objects are

* `dStab H t = H ⊓ H^t`, the two-point stabiliser `D`;
* `Canon H Q t`, the canonical structure maps `f, g, h` of a split rank-one group
  (`t x t = g(x) h(x) t f(x)` for `x ∈ Q#`, Peterfalvi II, Ch. V §2 Lemma 1);
* `ModelData n`, a split rank-one structure inside the literal model `PSL2Model n`
  with a faithful action;
* `ZassenhausPSL2CoreProp`, the classification input of the area: in the abelian case the
  data `(H, Q, t)` is isomorphic to the data of `PSL2Model n`.  (Zassenhaus 1936 / Feit 1960 /
  Huppert–Blackburn XI §10; see `REFS/zassenhaus_groups.md` §3.)

With `RankOneUniquenessProp` this yields `ZassenhausPSL2Prop` (`Main.lean`).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2

/-! ## The two-point stabiliser -/

/-- `D = H ∩ H^t`, the stabiliser of the two points `H` and `tH` (Peterfalvi's `D`). -/
abbrev dStab {G : Type*} [Group G] (H : Subgroup G) (t : G) : Subgroup G := twoPoint H t

/-- The stabiliser of the two points `H` and `tH` has odd order when `H` is strongly embedded
and `t ∉ H`: its order is that of `H ⊓ H^t`. -/
lemma dStab_odd {G : Type*} [Group G] (H : Subgroup G) (t : G) (hH : IsStronglyEmbedded H)
    (ht : t ∉ H) : Odd (Nat.card (dStab H t)) :=
  hH.2.2 t ht

/-- `K = J(D,t) = {x ∈ D | x^t = x⁻¹}` (Peterfalvi's `K`, `Interface.invertedBy`). -/
abbrev kSub {G : Type*} [Group G] (H : Subgroup G) (t : G) : Set G := invertedBy (dStab H t) t

/-! ## The canonical maps `f`, `g`, `h` -/

/-- **Canonical structure maps of a split rank-one group.**
For `x ∈ Q#` the element `t x t` lies outside `H` and has a unique expression
`t x t = g(x) h(x) t f(x)` with `g(x), f(x) ∈ Q` and `h(x) ∈ D = H ∩ H^t`
(Peterfalvi II, Ch. V §2 Lemma 1 and Ch. VII §1). -/
structure Canon {G : Type*} [Group G] (H Q : Subgroup G) (t : G) where
  /-- the map `f : Q# → Q#` describing the action of the Weyl element `t` on `Q#`. -/
  f : Q → Q
  /-- the `Q`-part of the `H`-factor of `t x t`. -/
  g : Q → Q
  /-- the `D`-part of the `H`-factor of `t x t`. -/
  h : Q → dStab H t
  /-- the defining relation `t x t = g(x) h(x) t f(x)`. -/
  spec : ∀ x : Q, (x : G) ≠ 1 →
    t * (x : G) * t = (g x : G) * (h x : G) * t * (f x : G)

/-! ## The model data -/

/-- Split rank-one data inside the literal model `PSL2Model n`, with faithful action. -/
structure ModelData (n : ℕ) where
  /-- the strongly embedded subgroup (a Borel). -/
  H : Subgroup (PSL2Model n)
  /-- the regular normal subgroup of `H` (the root group at the fixed point of `H`). -/
  Q : Subgroup (PSL2Model n)
  /-- the Weyl element. -/
  t : PSL2Model n
  /-- `(H, Q, t)` is a split rank-one datum. -/
  split : IsSplitRankOne H Q t
  /-- the action of `PSL2Model n` on `(PSL2Model n) ⧸ H` is faithful. -/
  faithful : ∀ g : PSL2Model n, (∀ ω : (PSL2Model n) ⧸ H, g • ω = ω) → g = 1

/-! ## The classification input of the area -/

/-- **The core input of the area `ZassenhausPSL2`.**

In a finite simple group `G` with a strongly embedded subgroup `H`, a split rank-one datum
`(H, Q, t)`, trivial three-point stabilisers and `Q` an abelian `2`-group, the whole datum
`(H, Q, t)` is isomorphic to the datum of `PSL2Model n = PSL(2, 2^n)` for some `n ≥ 2`,
through a group isomorphism `ψ : H ≃* H'` that matches the root groups, the two-point
stabilisers and the Weyl action (the `f`-relation of `RankOneUniquenessProp`).

This is the Zassenhaus classification of Zassenhaus groups with abelian root groups
(Zassenhaus 1936; Feit 1960, Illinois J. Math. 4, 170–186, §2–3; Huppert–Blackburn,
Finite Groups III, XI §10, pp. 256–264; Baumeister–Grüninger, arXiv:1011.5836, Thm. 1). -/
def ZassenhausPSL2CoreProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      IsPGroup 2 Q → IsAbelianSubgroup Q →
      ∃ (n : ℕ) (_ : 2 ≤ n) (M : ModelData n),
        ∃ ψ : H ≃* M.H,
          (∀ x : H, (x : G) ∈ Q ↔ (ψ x : PSL2Model n) ∈ M.Q) ∧
          (∀ x : H, (x : G) ∈ twoPoint H t ↔
            (ψ x : PSL2Model n) ∈ twoPoint M.H M.t) ∧
          (∀ x y : H, (x : G) ∈ Q → (y : G) ∈ Q → (x : G) ≠ 1 →
            (∃ m ∈ H, t * (x : G) * t = m * t * (y : G)) →
            ∃ m' ∈ M.H,
              M.t * (ψ x : PSL2Model n) * M.t = m' * M.t * (ψ y : PSL2Model n))

/-! ## The model's `f` in field coordinates -/

/-- The model's `f` (`w u(b) w ∈ B w u(1/b)`): `b ↦ b⁻¹` on `Multiplicative F`. -/
noncomputable def psl2F (n : ℕ) :
    Multiplicative (GaloisField 2 n) → Multiplicative (GaloisField 2 n) :=
  fun u => Multiplicative.ofAdd (Multiplicative.toAdd u)⁻¹


end Work.ZassenhausPSL2
