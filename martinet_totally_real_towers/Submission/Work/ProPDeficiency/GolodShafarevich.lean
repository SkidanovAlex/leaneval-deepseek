import Mathlib
import Submission.GroupTheory.GolodShafarevichCriterion
import Submission.GroupTheory.GolodShafarevichFromCommons
import Submission.Work.ProPDeficiency.Basic

/-!
# The Golod--Shafarevich criterion in the shape used by the arithmetic side

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.GolodShafarevich`.

`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich` is the corrected criterion
(`FinitePGroupGolodShafarevich p` plus a minimal presentation with `4 r ≤ d ^ 2` and all finite
quotients `p`-groups gives `Infinite G`).  The finite `p`-group inequality itself is *proved* in
the workspace (`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`).

This module restates the criterion in exactly the shape the arithmetic side feeds it:

* `infinite_of_presentation_of_golodShafarevich_two` : the `p = 2` specialisation, phrased with
  the vocabulary of `Submission.Work.ProPDeficiency.Basic`
  (`IsPresentation`, `IsGeneratingSet`, the `4 * rel.card ≤ Fintype.card α ^ 2` inequality);
* `..._of_deficiency` : the same, with the inequality derived from the *deficiency* input
  `Deficiency (Fintype.card α) rel.card (-1)` and `5 ≤ Fintype.card α` (the shape in which the
  number theory supplies the relation count, `r = d`);
* `infinite_freeGroup_quotient_of_golodShafarevich_two` : the same for the group **literally**
  given as `FreeGroup α ⧸ normalClosure rel` (no presentation iso needed: it is `rfl`);
* `..._of_pow_card` : the quotient hypothesis stated as "every finite quotient has `2`-power
  order";
* `card_le_rel_card_of_finite_isPGroup` : the elementary consequence "a *finite* `p`-group with a
  minimal generating set of size `d` needs at least `d` relators".

Nothing here is arithmetic; every statement is pure group theory.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

open Submission.GroupTheory (FinitePGroupGolodShafarevich
  finitePGroupGolodShafarevich_of_commons infinite_of_presentation_of_golodShafarevich)

/-- **The Golod--Shafarevich criterion at `p = 2`.**  A group `G` presented on a minimal
generating set `α` with relator set `rel`, all of whose finite quotients are `2`-groups, with
`4 * #rel ≤ #α ^ 2`, is infinite. -/
theorem infinite_of_presentation_of_golodShafarevich_two
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hineq : 4 * rel.card ≤ Fintype.card α ^ 2) : Infinite G := by
  refine infinite_of_presentation_of_golodShafarevich
    (finitePGroupGolodShafarevich_of_commons 2) rel hpos hpres hmin hquot ?_
  rw [← pow_two]
  exact hineq

/-- The Golod--Shafarevich criterion at `p = 2`, with the quotient hypothesis in the form
"every finite quotient has `2`-power order". -/
theorem infinite_of_presentation_of_golodShafarevich_two_of_pow_card
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k)
    (hineq : 4 * rel.card ≤ Fintype.card α ^ 2) : Infinite G :=
  infinite_of_presentation_of_golodShafarevich_two rel hpos hpres hmin
    (fun N _ hN => (IsPGroup.iff_card).mpr (hquot N hN)) hineq

/-- The Golod--Shafarevich criterion at `p = 2` for the group **literally** presented by
`α` and `rel`, with no presentation isomorphism to supply. -/
theorem infinite_freeGroup_quotient_of_golodShafarevich_two
    {α : Type} [Fintype α] [DecidableEq α] (rel : Finset (FreeGroup α))
    (hpos : 0 < Fintype.card α)
    (hmin : ∀ S : Finset (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))),
      IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))))
      [N.Normal],
      Finite ((FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) ⧸ N) →
      IsPGroup 2 ((FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) ⧸ N))
    (hineq : 4 * rel.card ≤ Fintype.card α ^ 2) :
    Infinite (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
  infinite_of_presentation_of_golodShafarevich_two rel hpos (IsPresentation.refl α rel) hmin
    hquot hineq

/-- **The Golod--Shafarevich criterion from the deficiency input.**  If the arithmetic side knows
that the presentation has deficiency at least `-1` (`r ≤ d + 1`, in particular the `r = d` case)
and `d ≥ 5`, then the criterion applies. -/
theorem infinite_of_presentation_of_golodShafarevich_two_of_deficiency
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hdef : Deficiency (Fintype.card α) rel.card (-1)) (hd : 5 ≤ Fintype.card α) : Infinite G := by
  refine infinite_of_presentation_of_golodShafarevich_two rel hpos hpres hmin hquot ?_
  rw [pow_two]
  exact four_mul_le_sq_of_deficiency hdef hd

/-- Variation where the minimality of the generating set is recorded as `dGens G = #α`. -/
theorem infinite_of_presentation_of_golodShafarevich_two_of_dGens
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G) (hdGens : dGens G = Fintype.card α)
    (hfg : Group.FG G)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hineq : 4 * rel.card ≤ Fintype.card α ^ 2) : Infinite G := by
  obtain ⟨S, hS, hScard⟩ := exists_minimalGeneratingSet hfg
  refine infinite_of_presentation_of_golodShafarevich_two rel hpos hpres (fun T hT => ?_) hquot hineq
  rw [← hdGens, ← hScard]
  exact hS.card_le hT

/-- **The finite `p`-group Golod--Shafarevich inequality** in the vocabulary of this chapter:
a nontrivial finite `p`-group presented on a *minimal* generating set `α` with relator set `rel`
satisfies `4 * rel.card > Fintype.card α ^ 2`.  (This is
`Submission.GroupTheory.FinitePGroupGolodShafarevich` restated, and it is the exact negation of the
hypothesis of the criterion above.) -/
theorem four_mul_rel_card_gt_sq_of_finite_isPGroup {p : ℕ} [Fact p.Prime] {α : Type} [Fintype α]
    [DecidableEq α] {G : Type} [Group G] [Finite G] [Nontrivial G] (rel : Finset (FreeGroup α))
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hpg : IsPGroup p G) : 4 * rel.card > Fintype.card α ^ 2 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h := finitePGroupGolodShafarevich_of_commons p G rel hpg hpres hmin
  rw [pow_two]
  exact h

/-- **A finite `p`-group with a minimal generating set of size `d` needs at least `d` relators.**
This is the elementary consequence of the finite `p`-group Golod--Shafarevich inequality
`4 r > d ^ 2`. -/
theorem card_le_rel_card_of_finite_isPGroup {p : ℕ} [Fact p.Prime] {α : Type} [Fintype α]
    [DecidableEq α] {G : Type} [Group G] [Finite G] [Nontrivial G] (rel : Finset (FreeGroup α))
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hpg : IsPGroup p G) : Fintype.card α ≤ rel.card := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  by_contra h
  have hlt : rel.card < Fintype.card α := Nat.lt_of_not_le h
  have hgs := finitePGroupGolodShafarevich_of_commons p G rel hpg hpres hmin
  have hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α :=
    four_mul_le_sq_of_lt hlt
  omega

end Work.ProPDeficiency
