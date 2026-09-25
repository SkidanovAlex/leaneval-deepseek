import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_coind

/-!
# Shapiro's lemma for the Herbrand quotient, induction form

For a finite group `G`, a subgroup `H ≤ G` and a `ℤ[H]`-module `M`, induction from `H` to `G` does
not change the Herbrand quotient.  Since `G` is finite, `H` has finite index in `G`, so by
`Rep.indCoindIso` the induced module `Ind_H^G M` is isomorphic, as a `ℤ[G]`-module, to the
coinduced module `Coind_H^G M`; the Herbrand quotient is an isomorphism invariant
(`hZero` and `hOne` are the cardinalities of the Tate cohomology groups, which are functorial),
and Shapiro's lemma in its coinduction form `herbrandEq_coind_iff` finishes the job.
-/

open CategoryTheory

namespace NK.GlobalCFTdeep.Herbrand

/-- The numerator `hZero` of the Herbrand quotient is invariant under isomorphism of
`ℤ[G]`-modules: `tateCohomology` is a functor, so an isomorphism of representations induces an
isomorphism (hence a bijection) of the Tate cohomology groups. -/
lemma hZero_congr {G : Type} [Group G] [Fintype G] {M N : Rep ℤ G} (e : M ≅ N) :
    hZero M = hZero N := by
  rw [hZero_def, hZero_def]
  exact Nat.card_congr
    (Iso.toLinearEquiv ((tateCohomologyFunctor (R := ℤ) (G := G) 0).mapIso e)).toEquiv

/-- The denominator `hOne` of the Herbrand quotient is invariant under isomorphism of
`ℤ[G]`-modules. -/
lemma hOne_congr {G : Type} [Group G] [Fintype G] {M N : Rep ℤ G} (e : M ≅ N) :
    hOne M = hOne N := by
  rw [hOne_def, hOne_def]
  exact Nat.card_congr
    (Iso.toLinearEquiv ((tateCohomologyFunctor (R := ℤ) (G := G) 1).mapIso e)).toEquiv

/-- **Shapiro's lemma for the Herbrand quotient, induction form**: for a subgroup `H` of a finite
group `G` and a `ℤ[H]`-module `M`, the induced `ℤ[G]`-module `Ind_H^G M` has the same Herbrand
quotient as `M`.  This is the induced-module counterpart of `herbrandEq_coind_iff` and follows
from it because `Ind_H^G M ≅ Coind_H^G M` for a subgroup of finite index. -/
theorem herbrandEq_ind_iff {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H]
    (M : Rep ℤ H) (m : ℕ) :
    NK.GlobalCFTdeep.HerbrandEq (Rep.ind H.subtype M) m ↔
      NK.GlobalCFTdeep.HerbrandEq M m := by
  classical
  have hiso : Rep.ind H.subtype M ≅ Rep.coind H.subtype M := Rep.indCoindIso M
  have h0 : hZero (Rep.ind H.subtype M) = hZero (Rep.coind H.subtype M) := hZero_congr hiso
  have h1 : hOne (Rep.ind H.subtype M) = hOne (Rep.coind H.subtype M) := hOne_congr hiso
  have hstep : HerbrandEq (Rep.ind H.subtype M) m ↔ HerbrandEq (Rep.coind H.subtype M) m := by
    rw [HerbrandEq, HerbrandEq, h0, h1]
  rw [hstep]
  exact herbrandEq_coind_iff H M m

end NK.GlobalCFTdeep.Herbrand
