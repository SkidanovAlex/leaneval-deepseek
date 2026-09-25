import Mathlib
import Submission.Work.ClassFieldTower.Defs

/-!
# `Work.ClassFieldTower.TwoDescentDefs` -- the Kummer classes `Kˣ/(Kˣ)²`

The first object of the (elementary, class-field-theory-free) Kummer two-descent for a number
field `K`: the group `Kˣ/(Kˣ)²` of Kummer classes.  By exponent-`2` Kummer theory the finite
Galois extensions of `K` with Galois group of exponent `2` are classified by the subgroups of this
group, and the `𝔽₂`-dimension of the class group is the number of independent generators of the
maximal such extension.  The relevant results are

* `Work.ClassFieldTower.kummer_expTwo_iso` (`Submission/Work/ClassFieldTower/kummer_expTwo_iso.lean`):
  for a finite Galois `L/K` with `∀ σ, σ² = 1` (and `char K ≠ 2`) the subgroup `U ≤ Kˣ/(Kˣ)²` of
  classes with a square root in `L` satisfies `Gal(L/K) ≃* Hom(U, 𝔽₂)` and `|Gal(L/K)| = |U|`;
* the two-descent identity `dim_{𝔽₂}(V/K^{×2}) = rank₂ Cl(K) + d₂(O_K^×)`, with
  `V = {x : (x) = I²}` (see the `README`, §11.3).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical

noncomputable section

namespace Work.ClassFieldTower

/-- **The subgroup of squares of `Kˣ`**, i.e. `(Kˣ)²`, so that `Kˣ ⧸ Sq K = Kˣ/(Kˣ)²` is the group
of Kummer classes of exponent `2`. -/
abbrev Sq (K : Type*) [Field K] : Subgroup Kˣ :=
  Subgroup.map (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ) ⊤

/-- The `𝔽₂`-dimension of the group of Kummer classes `Kˣ/(Kˣ)²`: the number of independent
quadratic (Kummer) generators of the maximal exponent-`2` abelian extension of `K`. -/
noncomputable def sqClassesRank (K : Type*) [Field K] : ℕ :=
  Nat.log 2 (Nat.card (Kˣ ⧸ Sq K))

end Work.ClassFieldTower
