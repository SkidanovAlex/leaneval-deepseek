import Mathlib
import Submission.Work.Serre.DiscPair.cellStepVanishing
import Submission.Work.Serre.relKronEquiv
-- (The declarations this file needs (`Work.Serre.EulerFibreRange`,
-- `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, `isZero_coh_of_ratAcyclic`, …) were moved
-- to the upstream module `Submission.Work.Serre.EulerFibreRoot`; importing *that* instead of
-- `Submission.Work.Serre.thomIsoCylFibreRange` removes the import edge that made the target of
-- `thomIsoCylFibreRange.lean` unprovable (build cycle).  See
-- `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1.)
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.ThomCylDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Vanishing of the relative rational cohomology below the cell dimension

Let `Z = Work.RatHurewicz.attachCells n Y ι f` be the space obtained from `Y` by attaching
`(n+2)`-cells along the attaching maps `f i : S^{n+1} → Y`, and let
`Y' = Set.range (attachIncl n Y ι f) ⊆ Z` be the old part.

The relative rational *homology* of the pair `(Z, Y')` vanishes below the cell dimension,

`H_j(Z, Y'; ℚ) = 0` for `j < n + 2`,

by `Work.Serre.DiscPair.isZero_relChainsR_homology_self_of_lt` (the low-degree part of the sharp
per-cell computation: one compresses the complement of the cell centres onto `Y'`, excises the
union of the open half-balls, splits it as a coproduct of the cell pieces and observes that each
piece has vanishing homology below the cell dimension).

Over a *field* the relative Kronecker pairing

`H^j(Z,Y';ℚ) →ₗ (H_j(Z,Y';ℚ) →ₗ ℚ)`

is an isomorphism — the universal coefficient theorem, which over a field needs neither a
finiteness nor a freeness hypothesis (`Work.Serre.relKronEquiv`) — so the relative rational
*cohomology* vanishes in the same range:

`isZero_relCoh_of_isZero_relHomology` — `H_j = 0 ⟹ H^j = 0`;

`attachRelCohVanishing` — the requested statement, with `D = n + 2`: the relative rational
cohomology of the pair `(Z, Y')` vanishes in every degree `m ≤ D - 1`.

(Note that the path-connectedness hypothesis `hΓ` on `Γ` is not needed for this computation; it
is part of the interface of the surrounding Postnikov construction.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **Relative cohomology vanishes where relative homology does.**  If the relative rational
homology `H_n(X,A;ℚ)` of a pair vanishes, then so does the relative rational cohomology
`H^n(X,A;ℚ)`: the Kronecker pairing `H^n(X,A;ℚ) ≅ₗ (H_n(X,A;ℚ) →ₗ ℚ)` is an isomorphism
(`Work.Serre.relKronEquiv`, the universal coefficient theorem over the field `ℚ`), and the dual of
the zero vector space is zero. -/
theorem isZero_relCoh_of_isZero_relHomology {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (h : CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n)) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n X A) := by
  haveI : Subsingleton ↥((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n) :=
    ModuleCat.subsingleton_of_isZero h
  obtain ⟨e⟩ := Work.Serre.relKronEquiv (TopCat.of X) A n
  haveI : Subsingleton ↥(Work.Thom.RelCoh ℚ n X A) :=
    ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr ‹_›

/-- **Vanishing of the relative rational cohomology below the cell dimension.**  Let
`Z = attachCells n Y ι f` be obtained from `Y` by attaching `(n+2)`-cells and let
`Y' = Set.range (attachIncl n Y ι f)`.  Then for every `m < n + 2` the relative rational cohomology
`H^m(Z, Y'; ℚ)` vanishes: the corresponding relative rational homology vanishes
(`isZero_relChainsR_homology_self_of_lt`), and over `ℚ` relative cohomology is the dual of
relative homology (`isZero_relCoh_of_isZero_relHomology`). -/
theorem attachRelCohVanishing (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
    (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) (m : ℕ) (hm : m ≤ D - 1) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m
      (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) :=
  isZero_relCoh_of_isZero_relHomology
    (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)) m
    (Work.Serre.DiscPair.isZero_relChainsR_homology_self_of_lt (D - 2) Γ ι f m (by omega))

end

end Work.Serre
