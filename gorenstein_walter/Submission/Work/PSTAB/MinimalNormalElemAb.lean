import Mathlib
import Submission.Work.PSTAB.Deps

/-!
# A minimal normal `p`-subgroup is elementary abelian

`Work.PSTAB.MinimalNormalElemAb`: if `W` is a minimal normal subgroup of a finite group
`G` and `W` is a `p`-group, then `W` is elementary abelian of exponent `p`.

Mathematically this is two steps.

* `W` is a `p`-group, hence finite and nilpotent, hence solvable; so Isaacs' Theorem 3.11
  (`OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable`) applies and
  produces a prime `q` with `W` elementary abelian of exponent `q`.
* The prime `q` must be `p`: `W ≠ ⊥` (minimal normal), so there is `x ≠ 1` in `W`; from
  `x ^ q = 1` we get `orderOf x = q` (`q` prime and `x ≠ 1`), while `IsPGroup p` gives
  `orderOf x = p ^ k` with `k ≠ 0`, so `p ∣ q` and `p = q`.

Note the exponent form of elementary abelianness used here
(`OddOrder.GroupTheory.IsElementaryAbelian`) is `(∀ x y, x * y = y * x) ∧ (∀ x, x ^ p = 1)`,
so the abelianness of `W` is part of the conclusion, not an input.
-/

namespace Work.PSTAB

open Subgroup

set_option linter.style.haveILetI false

theorem MinimalNormalElemAb {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {W : Subgroup G}
    (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal W) (hWp : IsPGroup p ↥W) :
    OddOrder.GroupTheory.IsElementaryAbelian p ↥W := by
  classical
  -- `W` is a finite `p`-group, hence nilpotent, hence solvable.
  have hsol : Group.IsSolvable ↥W := by
    haveI : Group.IsNilpotent ↥W := IsPGroup.isNilpotent hWp
    infer_instance
  haveI : Group.IsSolvable ↥W := hsol
  -- Isaacs Theorem 3.11: `W` is elementary abelian of exponent some prime `q`.
  obtain ⟨q, hq, hElem⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hMin
  -- The prime `q` is the given prime `p`, because `W` is a nontrivial `p`-group.
  have hqeqp : q = p := by
    have hWne : W ≠ ⊥ := hMin.2.1
    haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥W)
    -- `x ^ q = 1` forces `orderOf x = q`.
    have hqdvd : orderOf x ∣ q :=
      orderOf_dvd_iff_pow_eq_one.mpr
        ((show OddOrder.GroupTheory.IsElementaryAbelian q ↥W from hElem).pow_eq_one x)
    have hqx : orderOf x = q := by
      rcases (Nat.dvd_prime hq).mp hqdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx
      · exact h
    -- `IsPGroup p` gives `orderOf x = p ^ k` with `k ≠ 0`, so `p ∣ orderOf x = q`.
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hWp x
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hx (orderOf_eq_one_iff.mp hk)
    have hpdvd : p ∣ q := by
      rw [← hqx, hk]
      exact dvd_pow_self p hk0
    exact ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hpdvd).symm
  rw [← hqeqp]
  exact hElem

end Work.PSTAB
