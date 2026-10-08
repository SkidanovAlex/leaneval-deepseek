import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- Auxiliary group-theoretic fact: in a finite group `T`, if `A` is a normal subgroup of odd
index, then `1` is the only element whose order is `2`.

Indeed, if `x ∈ T` has `orderOf x = 2`, then its image `q x` in the quotient `T ⧸ A` has order
dividing `gcd 2 |T ⧸ A| = 1` (the order divides both `orderOf x` and the order `|T ⧸ A| = A.index`
of the quotient, which is odd); hence `q x = 1` and `x ∈ A`. -/
lemma mem_of_orderOf_eq_two_of_odd_index {T : Type*} [Group T] [Finite T]
    {A : Subgroup T} [A.Normal] (hodd : Odd A.index) {x : T} (hx2 : orderOf x = 2) :
    x ∈ A := by
  let q : T →* T ⧸ A := QuotientGroup.mk' A
  -- The order of `q x` divides `2` and also the odd number `|T ⧸ A| = A.index`.
  have hxdvd : orderOf (q x) ∣ 2 := by
    have h := orderOf_map_dvd q x
    rwa [hx2] at h
  have hqdvd : orderOf (q x) ∣ Nat.card (T ⧸ A) := orderOf_dvd_natCard (q x)
  have hcop : Nat.gcd 2 (Nat.card (T ⧸ A)) = 1 := by
    rw [← Subgroup.index_eq_card A]
    exact hodd.coprime_two_left
  -- Hence `orderOf (q x) = 1`, i.e. `q x = 1`, i.e. `x ∈ ker q = A`.
  have hone : orderOf (q x) = 1 := by
    have hg := Nat.dvd_gcd hxdvd hqdvd
    rw [hcop] at hg
    exact Nat.dvd_one.mp hg
  have hqone : q x = 1 := orderOf_eq_one_iff.mp hone
  have : x ∈ q.ker := MonoidHom.mem_ker.mpr hqone
  rwa [QuotientGroup.ker_mk' A] at this

theorem involutions_eq_of_odd_index {G : Type} [Group G] [Finite G] {F N H S D : Subgroup G}
    (hsup : S ⊔ (D ⊓ N) = H ⊓ N)
    (hnorm : H ⊓ N ≤ Subgroup.normalizer (S : Set G))
    (hcard : Nat.card ↥(H ⊓ N) = Nat.card ↥S * Nat.card ↥(D ⊓ N))
    (hDodd : Odd (Nat.card ↥D))
    (hSle : S ≤ F ⊓ H) (hFleN : F ≤ N) :
    ({x : G | x ∈ (F ⊓ H : Subgroup G) ∧ orderOf x = 2} : Set G) =
      {x : G | x ∈ (H ⊓ N : Subgroup G) ∧ orderOf x = 2} := by
  -- `S ≤ H ⊓ N`.
  have hSleT : S ≤ H ⊓ N :=
    le_inf (hSle.trans inf_le_right) (hSle.trans (inf_le_left.trans hFleN))
  -- `S` is normal in `H ⊓ N`.
  have hAnormal : (S.subgroupOf (H ⊓ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSleT).mpr hnorm
  -- `|D ⊓ N|` is odd.
  have hoddB : Odd (Nat.card ↥(D ⊓ N)) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le (inf_le_left : D ⊓ N ≤ D))
  -- The index of `S` in `H ⊓ N` equals `|D ⊓ N|`, hence is odd.
  have hindex : (S.subgroupOf (H ⊓ N)).index = Nat.card ↥(D ⊓ N) := by
    have h1 : (S.subgroupOf (H ⊓ N)).index * Nat.card ↥(S.subgroupOf (H ⊓ N))
        = Nat.card ↥(H ⊓ N) := Subgroup.index_mul_card _
    have h2 : Nat.card ↥(S.subgroupOf (H ⊓ N)) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleT).toEquiv
    rw [h2, hcard] at h1
    exact Nat.mul_left_cancel Nat.card_pos (by rw [mul_comm]; exact h1)
  have hodd : Odd (S.subgroupOf (H ⊓ N)).index := by rw [hindex]; exact hoddB
  -- Every involution of `H ⊓ N` lies in `S`.
  have hkey : ∀ x ∈ H ⊓ N, orderOf x = 2 → x ∈ S := by
    intro x hxT hx2
    have hy2 : orderOf (⟨x, hxT⟩ : ↥(H ⊓ N)) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨x, hxT⟩ : ↥(H ⊓ N))]
      exact hx2
    have hmem : (⟨x, hxT⟩ : ↥(H ⊓ N)) ∈ S.subgroupOf (H ⊓ N) :=
      mem_of_orderOf_eq_two_of_odd_index hodd hy2
    exact (Subgroup.mem_subgroupOf).mp hmem
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hFleN (Subgroup.mem_inf.mp hx).1⟩, ho⟩
  · rintro ⟨hx, ho⟩
    exact ⟨hSle (hkey x hx ho), ho⟩

end Work.NormalComplement
