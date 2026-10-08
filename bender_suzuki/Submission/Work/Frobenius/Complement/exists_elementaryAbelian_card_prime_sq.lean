import Mathlib
import Submission.Work.Frobenius.Complement.basicGroup_of_commute

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Two subgroups of order `p` in a `p`-group span an elementary abelian group of order `p²`

Let `H` be a finite `p`-group and let `Q₁ ≠ Q₂` be two distinct subgroups of order `p`.  Then `H`
contains an elementary abelian subgroup of order `p²`, i.e. a subgroup `Q` with `Nat.card Q = p²`
which is commutative and in which every element has order dividing `p`; equivalently
`Q ≃* Multiplicative (ZMod p × ZMod p)`.

## Proof

Let `Z(H)` be the centre of `H`; it is nontrivial because `H` is a nontrivial `p`-group (it
contains `Q₁`, of order `p > 1`), hence it contains an element `w` of order `p`.  The subgroup
`N := ⟨w⟩ ≤ Z(H)` has order `p`, so it cannot be equal to both `Q₁` and `Q₂`; say `Q` is one of
them with `Q ≠ N`.  Picking `a ∈ Q` of order `p` (which exists as `Q` has order `p`), the element
`a` has order `p`, is not in `N = ⟨w⟩` (as `⟨a⟩ ≤ Q` has order `p` and `Q ≠ N`), and commutes with
`w` (which is central); so `basicGroup_of_commute` produces a subgroup isomorphic to
`Multiplicative (ZMod p × ZMod p)`, which is the desired subgroup.

Note that this works for all primes `p`, including `p = 2`; no use of the oddness of `p` is made.
-/

set_option linter.style.haveILetI false

namespace Work.Frobenius.Complement

/-- In a nontrivial finite `p`-group there is an element of order `p`. -/
private lemma exists_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) [Nontrivial G] : ∃ x : G, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn, hcard⟩ := hG.nontrivial_iff_card.mp (inferInstance : Nontrivial G)
  exact exists_prime_orderOf_dvd_card' p (by rw [hcard]; exact dvd_pow_self p hn.ne')

lemma exists_elementaryAbelian_card_prime_sq {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hH : IsPGroup p H) {Q₁ Q₂ : Subgroup H} (hQ₁ : Nat.card Q₁ = p)
    (hQ₂ : Nat.card Q₂ = p) (hne : Q₁ ≠ Q₂) :
    ∃ Q : Subgroup H, Nat.card Q = p ^ 2 ∧ IsMulCommutative Q ∧ ∀ x : Q, x ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- An element of order `p` in `Q₁`, hence in `H`: in particular `H` is nontrivial.
  obtain ⟨a₁, ha₁⟩ := exists_prime_orderOf_dvd_card' p (G := Q₁) (by rw [hQ₁])
  have ha₁H : orderOf (a₁ : H) = p := by rw [Subgroup.orderOf_coe, ha₁]
  haveI : Nontrivial H :=
    ⟨⟨(a₁ : H), 1, fun hcon => hp.ne_one (by rw [← ha₁H, hcon, orderOf_one])⟩⟩
  -- The centre of `H` is nontrivial, so it contains an element `w` of order `p`.
  haveI : Nontrivial ↥(Subgroup.center H) := hH.center_nontrivial
  obtain ⟨w, hw⟩ := exists_orderOf_eq_prime hp (hH.to_subgroup (Subgroup.center H))
  have hzord : orderOf (w : H) = p := by rw [Subgroup.orderOf_coe, hw]
  have hzmem : (w : H) ∈ Subgroup.center H := w.2
  have hNz : Nat.card (Subgroup.zpowers (w : H)) = p := by rw [Nat.card_zpowers, hzord]
  -- At least one of `Q₁`, `Q₂` differs from `⟨w⟩`.
  have hchoose : Q₁ ≠ Subgroup.zpowers (w : H) ∨ Q₂ ≠ Subgroup.zpowers (w : H) := by
    by_cases h1 : Q₁ = Subgroup.zpowers (w : H)
    · right
      intro h2
      exact hne (h1.trans h2.symm)
    · exact Or.inl h1
  -- The key step: any subgroup `Q` of order `p` with `Q ≠ ⟨w⟩` yields the desired `Q'`.
  have key : ∀ Q : Subgroup H, Nat.card Q = p → Q ≠ Subgroup.zpowers (w : H) →
      ∃ Q' : Subgroup H, Nat.card Q' = p ^ 2 ∧ IsMulCommutative Q' ∧ ∀ x : Q', x ^ p = 1 := by
    intro Q hQ hQne
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (G := Q) (by rw [hQ])
    have haH : orderOf (a : H) = p := by rw [Subgroup.orderOf_coe, ha]
    have hcomm : (a : H) * (w : H) = (w : H) * (a : H) :=
      Subgroup.mem_center_iff.mp hzmem (a : H)
    have hcarda : Nat.card (Subgroup.zpowers (a : H)) = p := by rw [Nat.card_zpowers, haH]
    have hmem : (a : H) ∉ Subgroup.zpowers (w : H) := by
      intro hmem
      have h1 : Subgroup.zpowers (a : H) ≤ Subgroup.zpowers (w : H) :=
        Subgroup.zpowers_le.mpr hmem
      have h2 : Subgroup.zpowers (a : H) ≤ Q := Subgroup.zpowers_le.mpr a.2
      have he1 : Subgroup.zpowers (a : H) = Subgroup.zpowers (w : H) :=
        Subgroup.eq_of_le_of_card_ge h1 (by rw [hcarda, hNz])
      have he2 : Subgroup.zpowers (a : H) = Q :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [hcarda, hQ])
      exact hQne (he2 ▸ he1)
    obtain ⟨Q', ⟨e⟩⟩ := basicGroup_of_commute hp haH hzord hcomm hmem
    refine ⟨Q', ?_, ?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv,
        Nat.card_congr (Multiplicative.toAdd (α := ZMod p × ZMod p)), Nat.card_prod,
        Nat.card_zmod, pow_two]
    · refine IsMulCommutative.of_comm fun x y => e.injective ?_
      rw [map_mul, map_mul]
      exact isMulCommutative_iff.mp
        (inferInstance : IsMulCommutative (Multiplicative (ZMod p × ZMod p))) (e x) (e y)
    · intro x
      apply e.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
      have hzero : (p : ZMod p × ZMod p) = 0 := by
        ext <;> simp
      rw [hzero, zero_mul]
  rcases hchoose with h | h
  · exact key Q₁ hQ₁ h
  · exact key Q₂ hQ₂ h

end Work.Frobenius.Complement
