import Mathlib
import Submission.Work.ThreePoints.exists_prime_index_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- Descent data for the induction of Peterfalvi I Ch. II §4 Prop. 1 (a): for a nontrivial odd-order
solvable subgroup `X` of the finite group `G` there are a prime `p`, a normal subgroup `Y ≤ X` with
`Y ≠ X` and a `p`-subgroup `P ≤ X` with `Y ⊔ P = X` (i.e. `X = Y·P`).  Construction: take
`N ⊴ ↥X` of prime index `p` (`Work.ThreePoints.exists_prime_index_normal`), put
`Y := N.map X.subtype` and `P` the image of a Sylow `p`-subgroup of `↥X`; then `P ⊄ Y`
(the `p`-part of `|Y| = |X|/p` is `p^{a-1}`, that of `P` is `p^a`) and `|X : Y| = p`, so
`Y ⊔ P = X`. -/
lemma exists_descent_odd_solvable {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : X ≠ ⊥) (hodd : Odd (Nat.card X)) (hsol : Group.IsSolvable ↥X) :
    ∃ (p : ℕ) (Y P : Subgroup G), p.Prime ∧ p ≠ 2 ∧ Y ≤ X ∧ (Y.subgroupOf X).Normal ∧ Y ≠ X ∧
      IsPGroup p P ∧ P ≤ X ∧ Y ⊔ P = X := by
  have hntX : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX
  -- A normal subgroup `N ⊴ X` of prime index `p`.
  obtain ⟨p, N, hNnorm, hpprime, hNindex⟩ := exists_prime_index_normal hntX hsol
  -- `p` divides the odd number `|X|`, so `p` is odd.
  have hpodd : Odd p := by
    have hdvd : p ∣ Nat.card ↥X := by
      rw [← hNindex]
      exact Subgroup.index_dvd_card N
    exact Odd.of_dvd_nat hodd hdvd
  have hpne2 : p ≠ 2 := by
    intro h2
    obtain ⟨k, hk⟩ := hpodd
    omega
  -- A Sylow `p`-subgroup `S` of `X`.
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥X)
  -- `N` and `S` generate `X`: `(N ⊔ S).index` divides `N.index = p`, and it cannot be `p`,
  -- since that would force `S ≤ N` and hence `p ∣ S.index`, contradicting Sylow.
  have htop : N ⊔ (S : Subgroup ↥X) = ⊤ := by
    by_contra hne
    have hdvd : (N ⊔ (S : Subgroup ↥X)).index ∣ N.index := Subgroup.index_dvd_of_le le_sup_left
    rw [hNindex] at hdvd
    have hne1 : (N ⊔ (S : Subgroup ↥X)).index ≠ 1 := fun h1 =>
      hne (Subgroup.index_eq_one.mp h1)
    have hidx : (N ⊔ (S : Subgroup ↥X)).index = p := by
      rcases (Nat.dvd_prime hpprime).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hc1 := Subgroup.card_mul_index (N ⊔ (S : Subgroup ↥X))
    have hc2 := Subgroup.card_mul_index N
    rw [hidx] at hc1
    rw [hNindex] at hc2
    have hcard : Nat.card ↥(N ⊔ (S : Subgroup ↥X)) = Nat.card ↥N :=
      Nat.mul_right_cancel hpprime.pos (by rw [hc1, hc2])
    have hEq : N = N ⊔ (S : Subgroup ↥X) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hcard)
    have hSle : (S : Subgroup ↥X) ≤ N := by rw [hEq]; exact le_sup_right
    have hdvdp : N.index ∣ (S : Subgroup ↥X).index := Subgroup.index_dvd_of_le hSle
    rw [hNindex] at hdvdp
    exact @Sylow.not_dvd_index p ↥X _ (Fact.mk hpprime) S _ hdvdp
  refine ⟨p, N.map X.subtype, (S : Subgroup ↥X).map X.subtype, hpprime, hpne2, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le N
  · -- `Y.subgroupOf X = N` is normal
    have hY : (Subgroup.map X.subtype N).subgroupOf X = N :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective N
    rw [hY]
    exact hNnorm
  · -- `Y ≠ X`, as `N ≠ ⊤` has index a prime
    intro h
    have hmap : Subgroup.map X.subtype N = Subgroup.map X.subtype ⊤ := by
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
    have hNtop : N = ⊤ := Subgroup.map_injective X.subtype_injective hmap
    have := hNindex
    rw [hNtop, Subgroup.index_top] at this
    exact hpprime.ne_one this.symm
  · exact IsPGroup.map S.isPGroup' X.subtype
  · exact Subgroup.map_subtype_le (S : Subgroup ↥X)
  · -- `Y ⊔ P = (N ⊔ S).map X.subtype = X`
    have h2 : Subgroup.map X.subtype (N ⊔ (S : Subgroup ↥X)) = X := by
      rw [htop, Subgroup.map_top, Subgroup.range_subtype]
    rwa [Subgroup.map_sup] at h2

end Work.ThreePoints
