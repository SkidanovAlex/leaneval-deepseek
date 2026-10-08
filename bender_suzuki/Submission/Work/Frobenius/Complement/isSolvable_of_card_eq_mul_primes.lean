import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Groups of order `p * q` are solvable

For primes `p` and `q`, every finite group `A` with `Nat.card A = p * q` is solvable.

* If `p = q` then `|A| = p ^ 2`, and a group of order `p ^ 2` is abelian, hence solvable.
* If `p ≠ q`, assume `s < r` are the two primes. The number `n_r` of Sylow `r`-subgroups
  divides the index `s` of a Sylow `r`-subgroup `P` (which equals `s` because `|P| = r`),
  and `n_r ≡ 1 [MOD r]`; since `s < r` this forces `n_r = 1`, so `P` is normal. Its order is
  the prime `r` and the order of `A ⧸ P` is the prime `s`, so both `P` and `A ⧸ P` are cyclic,
  hence solvable, and `A` is solvable by the subgroup-quotient criterion.
-/

namespace Work.Frobenius.Complement

/-- A finite group of order `r * s`, where `r` and `s` are primes with `s < r`, is solvable.
The Sylow `r`-subgroup is normal (its index is the prime `s`), it has order `r`, and the quotient
has order `s`; both are cyclic. -/
theorem isSolvable_of_card_eq_mul_of_lt {A : Type*} [Group A] [Finite A] {r s : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hlt : s < r) (hcard : Nat.card A = r * s) :
    Group.IsSolvable A := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact s.Prime := ⟨hs⟩
  -- `r` occurs to the first power in `r * s`, because `r ∤ s`.
  have hfac : (Nat.card A).factorization r = 1 := by
    have hnotdvd : ¬ r ∣ s := by
      intro h
      rcases (Nat.dvd_prime hs).mp h with h1 | h1
      · exact hr.ne_one h1
      · exact hlt.ne' h1
    rw [hcard, Nat.factorization_mul hr.ne_zero hs.ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_self hr, Nat.factorization_eq_zero_of_not_dvd hnotdvd, add_zero]
  obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := A)
  -- A Sylow `r`-subgroup has order exactly `r`.
  have hcardP : Nat.card ↥(P : Subgroup A) = r := by
    rw [Sylow.card_eq_multiplicity P, hfac, pow_one]
  -- Hence there is exactly one Sylow `r`-subgroup, so it is normal.
  have hncard : Nat.card (Sylow r A) = 1 := by
    have hdvd : Nat.card (Sylow r A) ∣ (P : Subgroup A).index := Sylow.card_dvd_index P
    have hidx : (P : Subgroup A).index = s := by
      have h := Subgroup.card_mul_index (P : Subgroup A)
      rw [hcardP, hcard] at h
      exact Nat.mul_left_cancel hr.pos h
    rw [hidx] at hdvd
    have hle : Nat.card (Sylow r A) ≤ s := Nat.le_of_dvd hs.pos hdvd
    have hmod : Nat.card (Sylow r A) % r = 1 % r := card_sylow_modEq_one r A
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hle hlt), Nat.mod_eq_of_lt hr.one_lt] at hmod
    exact hmod
  haveI : Subsingleton (Sylow r A) := (Nat.card_eq_one_iff_unique.mp hncard).1
  have hnorm : (P : Subgroup A).Normal := Sylow.normal_of_subsingleton P
  haveI := hnorm
  -- The Sylow subgroup and the quotient both have prime order, hence are cyclic.
  haveI : IsCyclic ↥(P : Subgroup A) := isCyclic_of_prime_card hcardP
  have hquot : Nat.card (A ⧸ (P : Subgroup A)) = s := by
    rw [← Subgroup.index_eq_card (P : Subgroup A)]
    have h := Subgroup.card_mul_index (P : Subgroup A)
    rw [hcardP, hcard] at h
    exact Nat.mul_left_cancel hr.pos h
  haveI : IsCyclic (A ⧸ (P : Subgroup A)) := isCyclic_of_prime_card hquot
  exact Group.isSolvable_of_subgroup_quotient (P : Subgroup A)

theorem isSolvable_of_card_eq_mul_primes {A : Type*} [Group A] [Finite A] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hcard : Nat.card A = p * q) : Group.IsSolvable A := by
  rcases eq_or_ne p q with hpq | hpq
  · -- `p = q`: the group has order `p ^ 2`, hence is abelian.
    subst hpq
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : Nat.card A = p ^ 2 := by rw [hcard, sq]
    haveI : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq h2
    infer_instance
  · rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact isSolvable_of_card_eq_mul_of_lt hq hp hlt (by rw [hcard, Nat.mul_comm])
    · exact isSolvable_of_card_eq_mul_of_lt hp hq hlt hcard

end Work.Frobenius.Complement
