import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.GolodShafarevich
import Submission.Work.ProPDeficiency.Deficiency
import Submission.Work.ProPDeficiency.Quotients

/-!
# The packaged conclusion for the arithmetic side

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.Arithmetic`.

This module assembles the whole group-theoretic chapter into the single statement the number
theory consumes: a minimal presentation of deficiency at least `-1` (`r ≤ d + 1`; the arithmetic
supplies the sharper `r = d`) with `d ≥ 5` generators, all finite quotients `2`-groups and residual
finiteness, gives **both** infinitude of the group **and** finite quotients of order `2 ^ k`
exceeding any bound.  The arithmetic side then only has to realise each finite quotient as the
Galois group of a suitable pro-`2` extension.

## Main results

* `infinite_and_unbounded_two_pow_quotients_of_deficiency` : the packaged conclusion;
* `infinite_and_unbounded_two_pow_quotients_of_card_le_rel_card` : the same with the relation count
  supplied as `rel.card ≤ Fintype.card α` (deficiency `0`, the `r = d` case);
* `unbounded_two_pow_quotients_of_infinite` : the "infinity ⟹ unbounded `2`-power quotients" half
  on its own.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

/-- **The packaged conclusion of the pro-`p` deficiency chapter.**

A finitely generated residually finite group `G` with a minimal presentation by `α` and `rel`,
where all finite quotients are `2`-groups and whose presentation has deficiency at least `-1`
(`rel.card ≤ Fintype.card α + 1`) with at least `5` generators, is infinite and has finite
quotients of `2`-power order exceeding any prescribed bound. -/
theorem infinite_and_unbounded_two_pow_quotients_of_deficiency
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hdef : Deficiency (Fintype.card α) rel.card (-1)) (hd : 5 ≤ Fintype.card α) :
    Infinite G ∧ ∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧
      M < Nat.card (G ⧸ N) ∧ ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k := by
  have hinf : Infinite G :=
    infinite_of_presentation_of_golodShafarevich_two_of_deficiency rel hpos hpres hmin hquot
      hdef hd
  exact ⟨hinf, fun M => exists_finite_quotient_two_pow_card_gt G hquot hinf M⟩

/-- The `r = d` case of the packaged conclusion: deficiency `0`, i.e. `rel.card ≤ Fintype.card α`
(the relation count supplied by the `F_2` Euler characteristic in the tame route). -/
theorem infinite_and_unbounded_two_pow_quotients_of_card_le_rel_card
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hle : rel.card ≤ Fintype.card α) (hd : 4 ≤ Fintype.card α) :
    Infinite G ∧ ∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧
      M < Nat.card (G ⧸ N) ∧ ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k := by
  have hineq : 4 * rel.card ≤ Fintype.card α ^ 2 := by
    rw [pow_two]
    exact four_mul_le_sq_of_le hle hd
  have hinf : Infinite G :=
    infinite_of_presentation_of_golodShafarevich_two rel hpos hpres hmin hquot hineq
  exact ⟨hinf, fun M => exists_finite_quotient_two_pow_card_gt G hquot hinf M⟩

/-- The packaged conclusion in the exact shape of the arithmetic input
`Submission.NumberField.TameGolodShafarevichInput`: the inequality `4 * rel.card ≤ #α ^ 2` is
supplied directly instead of through a deficiency statement. -/
theorem infinite_and_unbounded_two_pow_quotients_of_inequality
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hineq : 4 * rel.card ≤ Fintype.card α ^ 2) :
    Infinite G ∧ ∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧
      M < Nat.card (G ⧸ N) ∧ ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k := by
  have hinf : Infinite G :=
    infinite_of_presentation_of_golodShafarevich_two rel hpos hpres hmin hquot hineq
  exact ⟨hinf, fun M => exists_finite_quotient_two_pow_card_gt G hquot hinf M⟩

/-- The packaged conclusion with the Golod--Shafarevich inequality written in the multiplicative
form `4 * rel.card ≤ #α * #α` (the literal shape of
`Submission.NumberField.TameGolodShafarevichInput`). -/
theorem infinite_and_unbounded_two_pow_quotients_of_mul_inequality
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (rel : Finset (FreeGroup α)) (hpos : 0 < Fintype.card α)
    (hpres : IsPresentation α rel G)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card)
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α) :
    Infinite G ∧ ∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧
      M < Nat.card (G ⧸ N) ∧ ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k :=
  infinite_and_unbounded_two_pow_quotients_of_inequality rel hpos hpres hmin hquot
    (by rw [pow_two]; exact hineq)

/-- The second half on its own: an infinite finitely generated residually finite group all of whose
finite quotients are `2`-groups has finite quotients of arbitrarily large `2`-power order. -/
theorem unbounded_two_pow_quotients_of_infinite (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hinf : Infinite G) (M : ℕ) :
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N) ∧
      ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k :=
  exists_finite_quotient_two_pow_card_gt G hquot hinf M

end Work.ProPDeficiency
