import Mathlib
import Submission.Commons.GroupTheory.finite_of_bounded_finite_quotients
import Submission.Work.ProPDeficiency.Basic

/-!
# Unbounded finite quotients of infinite finitely generated residually finite groups

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.Quotients`.

This is the bridge from "`G` is infinite" to "`G` has finite quotients of arbitrarily large
order", which is how an infinitude statement about a pro-`p` tower is turned into number fields of
arbitrarily large degree.  It is the reusable form of the `hunb` step of
`Submission/NumberField/TameGolodShafarevichReduction.lean`.

The hypothesis `Group.ResiduallyFinite G` is **necessary**: Higman's group is a finitely generated
infinite group all of whose finite quotients are `2`-groups (they are all trivial, and the trivial
group is a `2`-group), but it has no finite quotient of order `> 1`.  So the statement
`(∀ M, ∃ N, M < Nat.card (G ⧸ N)) ↔ Infinite G` needs residual finiteness in the `←` direction;
the `→` direction needs nothing at all.

## Main results

* `exists_finite_quotient_card_gt` : the `hunb` step (`M < Nat.card (G ⧸ N)`);
* `unbounded_finite_quotients_iff_infinite` : the iff, with residual finiteness for `←`;
* `exists_finite_quotient_card_gt_index` : the same with `N.index > M`;
* `exists_finite_quotient_two_pow_card_gt` : if moreover all finite quotients are `2`-groups, the
  quotient can be taken of order `2 ^ k` (the shape needed by the pro-`2` arithmetic).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

open Commons.GroupTheory (finite_of_bounded_finite_quotients)

/-- **Unbounded finite quotients.**  A finitely generated residually finite infinite group has, for
every `M`, a finite quotient of order exceeding `M`. -/
theorem exists_finite_quotient_card_gt (G : Type*) [Group G] [Group.FG G] [Group.ResiduallyFinite G]
    (hinf : Infinite G) (M : ℕ) :
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N) := by
  by_contra hc
  refine absurd (finite_of_bounded_finite_quotients G M ?_)
    (not_finite_iff_infinite.mpr hinf)
  intro N hNnorm hfin
  by_contra hle
  exact hc ⟨N, hNnorm, hfin, not_le.mp hle⟩

/-- The same statement in terms of the index of the (normal) subgroup. -/
theorem exists_finite_quotient_card_gt_index (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G] (hinf : Infinite G) (M : ℕ) :
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < N.index := by
  obtain ⟨N, hNnorm, hfin, hcard⟩ := exists_finite_quotient_card_gt G hinf M
  exact ⟨N, hNnorm, hfin, by rwa [Subgroup.index_eq_card]⟩

/-- **The iff**: for a finitely generated residually finite group, the finite quotients have
unbounded order precisely when the group is infinite. -/
theorem unbounded_finite_quotients_iff_infinite (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G] :
    (∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N)) ↔
      Infinite G := by
  constructor
  · intro h
    by_contra hfin
    haveI : Finite G := not_infinite_iff_finite.mp hfin
    obtain ⟨N, hNnorm, hfinq, hgt⟩ := h (Nat.card G)
    haveI := hNnorm
    have : Nat.card (G ⧸ N) ≤ Nat.card G :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    omega
  · intro h M
    exact exists_finite_quotient_card_gt G h M

/-- **Unbounded finite quotients of `2`-power order.**  If in addition every finite quotient of
`G` is a `2`-group, the finite quotients of arbitrarily large order can be taken to have `2`-power
order. -/
theorem exists_finite_quotient_two_pow_card_gt (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hinf : Infinite G) (M : ℕ) :
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N) ∧
      ∃ k : ℕ, Nat.card (G ⧸ N) = 2 ^ k := by
  obtain ⟨N, hNnorm, hfin, hgt⟩ := exists_finite_quotient_card_gt G hinf M
  refine ⟨N, hNnorm, hfin, hgt, ?_⟩
  exact (IsPGroup.iff_card (p := 2)).mp (hquot N hfin)

/-- Unbounded finite quotients of `p`-power order, for any prime `p`. -/
theorem exists_finite_quotient_prime_pow_card_gt (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G] {p : ℕ} [Fact p.Prime]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hinf : Infinite G) (M : ℕ) :
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N) ∧
      ∃ k : ℕ, Nat.card (G ⧸ N) = p ^ k := by
  obtain ⟨N, hNnorm, hfin, hgt⟩ := exists_finite_quotient_card_gt G hinf M
  exact ⟨N, hNnorm, hfin, hgt, (IsPGroup.iff_card (p := p)).mp (hquot N hfin)⟩

/-- **The bounded-quotient hypothesis implies finiteness** (the `hbound` shape of
`Submission.NumberField.exists_totallyReal_discr_le_of_golodShafarevich`): a finitely generated
residually finite group all of whose finite quotients have order at most `M` is finite.  This is
`Commons.GroupTheory.finite_of_bounded_finite_quotients` in the exact argument order of the
arithmetic side, so that the hypothesis can be discharged by a term of this type. -/
theorem bounded_finite_quotients_implies_finite :
    ∀ (M : ℕ) (G : Type) [Group G] [Group.FG G] [Group.ResiduallyFinite G],
      (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → Nat.card (G ⧸ N) ≤ M) → Finite G :=
  fun M G _ _ _ h => Commons.GroupTheory.finite_of_bounded_finite_quotients G M h

open Commons.GroupTheory in
/-- The same, with the group as an ordinary argument (this is the commons result, re-exported in
the namespace of the chapter so that callers do not have to reach into `Commons`). -/
theorem finite_of_bounded_finite_quotients (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G] (M : ℕ)
    (h : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → Nat.card (G ⧸ N) ≤ M) : Finite G :=
  Commons.GroupTheory.finite_of_bounded_finite_quotients G M h

/-- **For a finite group, "all finite quotients are `p`-groups" is the same as "`G` is a
`p`-group"** (apply the hypothesis to the trivial subgroup). -/
theorem isPGroup_of_forall_quotient_isPGroup {p : ℕ} {G : Type*} [Group G] [Finite G]
    (h : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N)) : IsPGroup p G :=
  (h ⊥ (inferInstance : Finite (G ⧸ (⊥ : Subgroup G)))).of_equiv
    (QuotientGroup.quotientBot (G := G))

/-- Unbounded finite quotients of `2`-power **index** (the form in which the arithmetic side
measures the degree `[L : F]` of the tower levels). -/
theorem exists_finite_quotient_two_pow_index_gt (G : Type*) [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hinf : Infinite G) (M : ℕ) :
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < N.index ∧
      ∃ k : ℕ, N.index = 2 ^ k := by
  obtain ⟨N, hNnorm, hfin, hgt, k, hk⟩ := exists_finite_quotient_two_pow_card_gt G hquot hinf M
  refine ⟨N, hNnorm, hfin, ?_, k, ?_⟩
  · rwa [Subgroup.index_eq_card]
  · rw [Subgroup.index_eq_card, hk]

end Work.ProPDeficiency
