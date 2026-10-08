import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# `F*(G) = O_p(G)` when `F*(G)` is a `p`-group

This file proves the CORE2A leaf `fstar_eq_pCore_of_isPGroup`: if the generalized Fitting
subgroup `F*(X) = F(X) E(X)` of a finite group `X` happens to be a `p`-group, then it already
coincides with the `p`-core `O_p(X)`.

The mathematical content is elementary and rests on two observations about the two pieces of
`F*(G) = F(G) ⊔ E(G)` (with `F` the Fitting subgroup and `E` the layer):

* both `F(X)` and `E(X)` are **normal** subgroups of `X` — `F(X)` because it is a `normalCore`
  (`Subgroup.normalCore_normal`), `E(X) = sSup {E | E.Normal ∧ IsQuasisimple E}` because it is
  the supremum of normal subgroups, handled here through `sSup_le` rather than by proving the
  `Normal` instance directly;
* both are **contained in `F*(X)`**, hence, when `F*(X)` is a `p`-group, are again `p`-groups
  (`IsPGroup.to_le`).

A normal `p`-subgroup is by definition contained in `O_p(X)` (this is the universal property
`le_pCore_of_normal_isPGroup`), so each piece, and hence their join `F*(X)`, lies in `O_p(X)`.

Conversely `O_p(X) ≤ F(X) ≤ F*(X)`: `O_p(X)` is a normal `p`-subgroup, `p`-groups are nilpotent,
so `O_p(X)` is a normal nilpotent subgroup and therefore lies in the Fitting subgroup, the
largest such subgroup.  No finiteness of `X`, no primality of `p` and no theory of the layer are
needed for this half.

The two auxiliary lemmas below (`le_pCore_of_normal_isPGroup`, `pCore_le_fitting`) are the
fragment of `O_p(-)`-API used here; they are stated and proved inline so that the file depends
on nothing beyond Mathlib and the shared vocabulary module.
-/

-- `haveI` (not `have`) is used to register the `Normal` instances below, so the style linter's
-- suggestion to use `have` does not apply here.
set_option linter.style.haveILetI false

open scoped MatrixGroups
open Subgroup

namespace Work.CORE2A

/-- **Universal property of `O_p(G)`.** Every normal `p`-subgroup of `G` lies in `pCore p G`.
This is the `le_sSup`-half of the definition: a normal `p`-subgroup is a member of the set whose
supremum `O_p(G)` is the `normalCore` of. -/
theorem le_pCore_of_normal_isPGroup {G : Type} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) : N ≤ Work.GW2.pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- **`O_p(G) ≤ F(G)`.** A normal `p`-subgroup is nilpotent, so `O_p(G)` — a normal `p`-subgroup
— is a normal nilpotent subgroup, and `F(G)` is by definition the largest such subgroup. -/
theorem pCore_le_fitting {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G ≤ Work.GW2.fitting G := by
  -- `F(G)` is the `normalCore` of the supremum of the normal nilpotent subgroups; it suffices to
  -- place `O_p(G)` below that supremum.
  refine Subgroup.normal_le_normalCore.mpr ?_
  refine (Subgroup.normalCore_le _).trans ?_
  refine sSup_le ?_
  intro N hN
  exact le_sSup ⟨hN.1, hN.2.isNilpotent⟩

/-- If the generalized Fitting subgroup `F*(X)` of a finite group `X` is a `p`-group, then
`F*(X) = O_p(X)`. -/
theorem fstar_eq_pCore_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : IsPGroup p (Work.GW2.fstar X)) : Work.GW2.fstar X = Work.GW2.pCore p X := by
  apply le_antisymm
  · -- `F*(X) = F(X) ⊔ E(X) ≤ O_p(X)`: each piece is a normal subgroup of the `p`-group `F*(X)`.
    rw [Work.GW2.fstar]
    apply sup_le
    · -- `F(X)`: normal (`normalCore`) and a `p`-group since `F(X) ≤ F*(X)`.
      haveI : (Work.GW2.fitting X).Normal := Subgroup.normalCore_normal _
      exact le_pCore_of_normal_isPGroup (IsPGroup.to_le h le_sup_left)
    · -- `E(X) = sSup {E | E.Normal ∧ IsQuasisimple E}`: supremum of normal `p`-subgroups.
      rw [Work.GW2.layer]
      apply sSup_le
      intro E hE
      haveI : E.Normal := hE.1
      exact le_pCore_of_normal_isPGroup (IsPGroup.to_le h ((le_sSup hE).trans le_sup_right))
  · -- `O_p(X) ≤ F(X) ≤ F*(X)`.
    exact (pCore_le_fitting (G := X)).trans le_sup_left

end Work.CORE2A
