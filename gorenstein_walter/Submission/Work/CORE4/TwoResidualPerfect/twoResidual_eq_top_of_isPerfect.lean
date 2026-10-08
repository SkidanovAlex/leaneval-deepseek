import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.TwoResidualPerfect

open Subgroup

set_option linter.style.haveILetI false

/-- `O²(X)` is normal: the odd-order elements are closed under conjugation, so the normalizer of
the subgroup they generate is all of `X`. -/
theorem twoResidual_normal (X : Type*) [Group X] : (Work.GW2.twoResidual X).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, Work.GW2.twoResidual,
    Subgroup.le_normalizer_closure_iff]
  intro h _ g hg
  refine Subgroup.subset_closure ?_
  have hc : orderOf g = orderOf (h * g * h⁻¹) :=
    SemiconjBy.orderOf_eq h (by simp [SemiconjBy, mul_assoc])
  simpa [hc] using hg

/-- For a finite group `X` and `x : X`, some `2`-power of `x` has odd order: with
`k = (orderOf x).factorization 2` the order of `x ^ 2 ^ k` is the odd part of `orderOf x`. -/
theorem odd_orderOf_pow_two_factorization {X : Type*} [Group X] [Finite X] (x : X) :
    Odd (orderOf (x ^ 2 ^ (orderOf x).factorization 2)) := by
  have hne : (2 : ℕ) ^ (orderOf x).factorization 2 ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [orderOf_pow_of_dvd hne (Nat.ordProj_dvd _ _)]
  have hpos : orderOf x ≠ 0 := (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)).ne'
  exact Nat.not_even_iff_odd.mp fun he =>
    Nat.not_dvd_ordCompl Nat.prime_two hpos (even_iff_two_dvd.mp he)

/-- `O²(X) = X` for a finite perfect group: the elements of odd order generate `X`.  (In
`X ⧸ O²(X)` some `2`-power of every element vanishes — the order of `x ^ 2 ^ k` is the odd part of
`orderOf x` for `k = (orderOf x).factorization 2` — so the quotient is a `2`-group, hence
nilpotent, hence solvable; being perfect as a quotient of a perfect group it is trivial.) -/
theorem twoResidual_eq_top_of_isPerfect {X : Type} [Group X] [Finite X] [Group.IsPerfect X] :
    Work.GW2.twoResidual X = ⊤ := by
  haveI hN : (Work.GW2.twoResidual X).Normal := twoResidual_normal X
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- every element of `X ⧸ O²(X)` has `2`-power order: some `2`-power of a lift lies in `O²(X)`
  have hpg : IsPGroup 2 (X ⧸ Work.GW2.twoResidual X) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Work.GW2.twoResidual X) g
    refine ⟨(orderOf x).factorization 2, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Work.GW2.twoResidual]
    exact Subgroup.subset_closure (odd_orderOf_pow_two_factorization x)
  -- so `X ⧸ O²(X)` is nilpotent, hence solvable, but it is perfect as a quotient of `X`
  by_contra htop
  haveI : Nontrivial (X ⧸ Work.GW2.twoResidual X) := QuotientGroup.nontrivial_iff.mpr htop
  exact Group.IsPerfect.not_isNilpotent (X ⧸ Work.GW2.twoResidual X) hpg.isNilpotent

end Work.CORE4.TwoResidualPerfect
