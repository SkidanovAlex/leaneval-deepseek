import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.Frobenius.Complement

set_option linter.style.haveILetI false in
/-- If a finite `p`-group `A` acts on a finite group `N` with `(|A|, |N|) = 1`, then for every
prime `r` there is an `A`-invariant Sylow `r`-subgroup of `N`.

The proof counts the orbits of the induced action of `A` on the (finite) set `Sylow r N`: since `A`
is a `p`-group, the number of fixed points is congruent to `|Sylow r N|` modulo `p`, and
`|Sylow r N|` divides `|N|`, hence is coprime to `p`; so a fixed point exists. -/
theorem exists_invariant_sylow_of_isPGroup {A N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N] {p : ℕ} (hp : p.Prime) (hAp : IsPGroup p A)
    (hcop : (Nat.card A).Coprime (Nat.card N)) {r : ℕ} (hr : r.Prime) :
    ∃ P : Sylow r N, ∀ a : A, ∀ x : N, (x ∈ (P : Subgroup N) ↔ a • x ∈ (P : Subgroup N)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hA1 : Nat.card A = 1
  · -- `A` is trivial, so the action is trivial and any Sylow subgroup works.
    haveI : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
    refine ⟨Classical.arbitrary (Sylow r N), ?_⟩
    intro a x
    rw [Subsingleton.elim a 1, one_smul]
  · -- `A` is a nontrivial `p`-group, so `p ∣ |A|`, hence `p ∤ |N|`.
    have hpdvd : p ∣ Nat.card A := by
      rcases hAp.card_eq_or_dvd with h | h
      · exact absurd h hA1
      · exact h
    have hpN : ¬ p ∣ Nat.card N := by
      intro hdiv
      have : p ∣ (Nat.card A).gcd (Nat.card N) := Nat.dvd_gcd hpdvd hdiv
      rw [hcop] at this
      exact hp.not_dvd_one this
    -- The number of Sylow `r`-subgroups of `N` divides `|N|`, hence is coprime to `p`.
    have hdvd : Nat.card (Sylow r N) ∣ Nat.card N :=
      dvd_trans (Sylow.card_dvd_index (Classical.arbitrary (Sylow r N)))
        (Subgroup.index_dvd_card _)
    have hnotdvd : ¬ p ∣ Nat.card (Sylow r N) := fun h => hpN (h.trans hdvd)
    -- Orbit counting: a `p`-group acting on a set of coprime cardinality has a fixed point.
    obtain ⟨P, hP⟩ := hAp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r N) hnotdvd
    refine ⟨P, ?_⟩
    have hfix : ∀ a : A, a • (P : Subgroup N) = (P : Subgroup N) := by
      intro a
      have h := (MulAction.mem_fixedPoints.mp hP) a
      have h' : ((a • P : Sylow r N) : Subgroup N) = (P : Subgroup N) := congrArg _ h
      rwa [Sylow.pointwise_smul_def] at h'
    intro a x
    rw [← Subgroup.mem_inv_pointwise_smul_iff (a := a), hfix a⁻¹]

end Work.Frobenius.Complement
