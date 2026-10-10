import Mathlib.RepresentationTheory.Coinduced
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_coind
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_trivial
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_coind
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_trivial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma for the Herbrand quotient

Coinduction from a subgroup does not change the Herbrand quotient.  This is the module-theoretic
content of the contribution of **one Galois orbit of places** to Milne's Proposition 2.7: the
places of `L` over a fixed place `v` of `K` form a single orbit, and the stabiliser of a place `w`
is its decomposition group `D_w`, with `∏_{w | v} L_wˣ ≅ Coind_{D_w}^{G} L_wˣ` as `ℤ[G]`-modules
(Shapiro).  Together with the Herbrand multiplicativity of `Herbrand/Reduction.lean` — which
handles the finitely many orbits, since each splitting off of an orbit is a short exact
sequence — this turns `h` of the `S`-idèles into a product of the local Herbrand quotients
`h(D_w, L_wˣ) = [L_w : K_v]` recorded in `Herbrand/Local.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Shapiro's lemma for the Herbrand quotient**: for a subgroup `H ≤ G` and an `H`-module `M`,
the coinduced `G`-module `Coind_H^G M` has the same Herbrand quotient as `M`. -/
theorem herbrandEq_coind_iff {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H]
    (M : Rep ℤ H) (m : ℕ) : HerbrandEq (Rep.coind H.subtype M) m ↔ HerbrandEq M m := by
  rw [HerbrandEq, HerbrandEq, Herbrand.hZero_coind, Herbrand.hOne_coind]

/-- **The Herbrand quotient of the permutation module `ℤ[G/H]`**: for a subgroup `H ≤ G` the
coinduced trivial `H`-module `Coind_H^G ℤ = ℤ[G ⧸ H]` has Herbrand quotient `|H|`.  This is the
`v`-orbit contribution of Milne's Proposition 2.7 in the shape in which it is used
(`h(G, ⨁_{v ∈ S} Ind_{G_v}^G ℤ) = ∏_v n_v`). -/
theorem herbrandEq_coind_trivial {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    HerbrandEq (Rep.coind H.subtype (Rep.trivial ℤ H ℤ)) (Nat.card H) := by
  rw [HerbrandEq, Herbrand.hZero_coind, Herbrand.hOne_coind, Herbrand.hZero_trivial,
    Herbrand.hOne_trivial, mul_one]

end NK.GlobalCFTdeep
