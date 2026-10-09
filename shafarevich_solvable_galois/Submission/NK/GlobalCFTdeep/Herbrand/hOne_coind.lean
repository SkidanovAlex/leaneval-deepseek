import Mathlib
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma for coinduction, at `Ĥ¹` (the `hOne` of the Herbrand quotient)

For a finite group `G`, a subgroup `H ≤ G` and a `ℤ[H]`-module `M`, the coinduced module
`Coind_H^G M = Hom_{ℤ[H]}(ℤ[G], M)` satisfies **Shapiro's lemma**

`Ĥⁿ(G, Coind_H^G M) ≅ Ĥⁿ(H, M)`   for all `n ∈ ℤ`.

This file records the case `n = 1` in the form in which the deep chapter of the global
class field theory development uses it: the *order* of `Ĥ¹` is unchanged by coinduction,

`hOne (Rep.coind H.subtype M) = hOne M`.

The proof is the composition of the two classical inputs:

* `TateCohomology.isoGroupCohomology` — for `n ≠ 0` the `n`-th Tate cohomology of a
  representation agrees with the `n`-th group cohomology (`n = 1` here, on both sides);
* `groupCohomology.coindIso` — Shapiro's lemma for ordinary group cohomology in positive
  degrees.

Orders are compared with `Nat.card`, which is preserved by any equivalence, so no finiteness
hypothesis on `M` is needed.
-/

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory

/-- **Shapiro's lemma at `Ĥ¹`.**  Coinduction along `H ↪ G` does not change the order of `Ĥ¹`:
`|Ĥ¹(G, Coind_H^G M)| = |Ĥ¹(H, M)|`. -/
theorem hOne_coind {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (M : Rep ℤ H) :
    hOne (Rep.coind H.subtype M) = hOne M := by
  rw [hOne_def, hOne_def]
  -- `Ĥ¹` of a representation is its `H¹` in positive degrees, on `G` and on `H` respectively.
  have h1 : Nat.card (tateCohomology (Rep.coind H.subtype M) 1)
      = Nat.card (groupCohomology (Rep.coind H.subtype M) 1) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app
        (Rep.coind H.subtype M))).toEquiv
  -- Shapiro's lemma for group cohomology in degree `1`.
  have h2 : Nat.card (groupCohomology (Rep.coind H.subtype M) 1)
      = Nat.card (groupCohomology M 1) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      (groupCohomology.coindIso (S := H) M 1)).toEquiv
  have h3 : Nat.card (groupCohomology M 1) = Nat.card (tateCohomology M 1) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := H) 1).app M).symm).toEquiv
  rw [h1, h2, h3]

end NK.GlobalCFTdeep.Herbrand
