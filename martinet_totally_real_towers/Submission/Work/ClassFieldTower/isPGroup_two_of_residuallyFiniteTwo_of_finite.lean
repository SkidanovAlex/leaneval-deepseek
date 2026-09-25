import Mathlib
import Submission.Work.ClassFieldTower.ProTwoDefs

/-!
# A finite residually-(finite `2`-group) group is a `2`-group

`Work.ClassFieldTower.ResiduallyFiniteTwoGroup G` says that every nontrivial element of `G`
survives in some quotient of `G` by a normal subgroup with a finite `2`-group quotient.
For a **finite** `G` this forces `G` itself to be a `2`-group: if an odd prime `q` divided
`|G|`, Cauchy's theorem would give an element of order `q`, whose image in any finite `2`-group
quotient is trivial (its order divides both `q` and a power of `2`) -- contradicting the
residual condition.  Equivalently, every prime divisor of `Nat.card G` equals `2`, so that
`Nat.card G` is a power of `2`.

This is the group-theoretic reason why the (pro-`2`) tower groups of the arithmetic interface
`Submission.Work.ClassFieldTower.ProTwoDefs` are either infinite or finite `2`-groups.
-/

set_option linter.style.haveILetI false

namespace Work.ClassFieldTower

/-- **A finite residually-(finite `2`-group) group is a `2`-group.**

If `G` is finite and every nontrivial element survives in a finite `2`-group quotient, then
every prime divisor of `Nat.card G` is `2`; hence `Nat.card G` is a power of `2` and `G` is a
`2`-group. -/
theorem isPGroup_two_of_residuallyFiniteTwo_of_finite {G : Type*} [Group G]
    (hres : ResiduallyFiniteTwoGroup G) (hfin : Finite G) : IsPGroup 2 G := by
  classical
  haveI : Finite G := hfin
  rw [isPGroup_iff_primeFactors_card_subset (p := 2) (by norm_num)]
  intro q hq
  -- Every prime `q` dividing `Nat.card G` is equal to `2`.
  have hq2 : q = 2 := by
    by_contra hqne
    obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    -- Cauchy: an element of order `q`.
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqprime⟩) hqdvd
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg
      exact hqprime.ne_one hg.symm
    -- the residual condition: an admissible quotient in which `g` survives
    obtain ⟨N, hNnorm, -, hNp, hNne⟩ := hres g hg1
    haveI := hNnorm
    have hgq : g ^ q = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hg]
    -- the image of `g` has order dividing `q` ...
    have hyq : orderOf (QuotientGroup.mk' N g) ∣ q := by
      rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hgq, map_one]
    -- ... and dividing a power of `2`, because the quotient is a `2`-group.
    obtain ⟨k, hk⟩ := hNp.exists_orderOf_dvd_pow (QuotientGroup.mk' N g)
    have hcop : q.Coprime (2 ^ k) :=
      ((Nat.coprime_primes hqprime Nat.prime_two).mpr hqne).pow_right k
    have hdiv : orderOf (QuotientGroup.mk' N g) ∣ 1 := by
      have h := Nat.dvd_gcd hyq hk
      rwa [Nat.Coprime.gcd_eq_one hcop] at h
    -- so the image is trivial, contradicting the choice of `N`
    exact hNne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv))
  rw [hq2]
  exact Nat.prime_two.mem_primeFactors dvd_rfl (by norm_num)

end Work.ClassFieldTower
