import Mathlib

/-!
# The `2`-rank of a commutative group, and independence modulo squares

Elementary algebraic backbone of the quadratic-field chapter.  For a commutative group `A` the
`2`-rank is the `𝔽₂`-dimension of the quotient `A ⧸ A²`.  In a number field `F` the group of
interest is `Fˣ` (whose `2`-rank counts independent quadratic Kummer extensions) or the class
group `Cl F` (whose `2`-rank counts independent unramified quadratic extensions).

## Main definitions

* `Work.QuadraticFields.squareSubgroup`: the subgroup `A²` of squares of `A`.
* `Work.QuadraticFields.rankTwo`: the `2`-rank `dim_{𝔽₂} (A ⧸ A²)`.
* `Work.QuadraticFields.sqClass`: the class of `a` in `A ⧸ A²`.
* `Work.QuadraticFields.IndependentModSquares`: `𝔽₂`-independence of a family of classes.

The basic API (monotonicity under surjections, the value on elementary abelian `2`-groups, the
criterion `independentModSquares_iff_finset`, and the counting lemma
`card_le_rankTwo_of_independentModSquares`) is proved in the companion files of this directory.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

universe u w

/-- The subgroup `A²` of squares of a commutative group `A`. -/
def squareSubgroup (A : Type u) [CommGroup A] : Subgroup A :=
  Subgroup.closure (Set.range fun x : A => x ^ 2)

/-- **The `2`-rank** of a commutative group: the `𝔽₂`-dimension of `A ⧸ A²`, computed as the
quotient of the underlying additive group by the multiples of `2`. -/
noncomputable def rankTwo (A : Type u) [CommGroup A] : ℕ :=
  Module.finrank (ZMod 2) (ModN (Additive A) 2)

/-- The class of `a` in `A ⧸ A²`. -/
noncomputable def sqClass {A : Type u} [CommGroup A] (a : A) : ModN (Additive A) 2 :=
  ModN.mkQ 2 (Additive.ofMul a)

/-- A family of elements of a commutative group is **independent modulo squares** if its images in
`A ⧸ A²` are linearly independent over `𝔽₂`. -/
noncomputable def IndependentModSquares {A : Type u} [CommGroup A] {ι : Type w} (a : ι → A) : Prop :=
  LinearIndependent (ZMod 2) fun i => sqClass (a i)

end Work.QuadraticFields
