import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Odd-order subgroups of the automorphism group of a group of order `8`

Let `P` be a nonabelian group of order `8` (so `P` is `D₈` or `Q₈`) and let
`A ≤ MulAut P` be a subgroup of odd order.  Then `|A| = 1` or `|A| = 3`.

The proof does not classify `P`.  Write `Z = Z(P)`; for a nonabelian group of order `8`
the centre has order `2` (`center_card_eq_two`).  Any automorphism of `P` preserves `Z`,
hence induces an automorphism of `Q = P ⧸ Z`, giving a monoid homomorphism
`quotCenterHom : MulAut P →* MulAut Q`.  Since `|Z| = 2`, the centre is an elementary
abelian group of exponent `2`, and one shows that an automorphism of odd order that is
trivial on `Q` is trivial on `P` (`quotCenterHom_eq_one_imp`): if `α(g) g⁻¹ ∈ Z` for all
`g`, then `α² = 1`, and as `orderOf α` is odd, `α = 1`.  Hence `A` embeds into `MulAut Q`,
and `|MulAut Q| ∣ |Equiv.Perm Q| = (|Q|)! = 4! = 24`.  So `|A| ∣ 24`; being odd,
`|A| ∈ {1, 3}`.

## Main result

* `Work.ThmF.Prove.Step6.card_eq_one_or_three_of_odd_order_subgroup_mulAut`
-/

namespace Work.ThmF.Prove.Step6

open Subgroup

/-- In a group with exactly two elements, any two nonidentity elements coincide. -/
lemma eq_of_ne_one_of_card_two {G : Type*} [Group G] [Finite G] (h : Nat.card G = 2)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hcard : Fintype.card G = 2 := by rw [← Nat.card_eq_fintype_card]; exact h
  have huniv : ({1, a} : Finset G) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm ha), hcard]
  have hb' : b ∈ ({1, a} : Finset G) := by rw [huniv]; exact Finset.mem_univ b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
  rcases hb' with h1 | h2
  · exact absurd h1 hb
  · exact h2.symm

/-- The automorphism group of a group with exactly two elements is trivial. -/
lemma mulAut_eq_one_of_card_two {G : Type*} [Group G] [Finite G] (h : Nat.card G = 2)
    (f : MulAut G) : f = 1 := by
  ext x
  by_cases hx : x = 1
  · rw [hx, map_one, MulAut.one_apply]
  · have hfx : f x ≠ 1 := by
      intro hc
      exact hx (f.injective (by rw [hc, map_one]))
    exact eq_of_ne_one_of_card_two h hfx hx

/-- An injective homomorphism of finite groups gives a divisibility of cardinalities. -/
lemma card_dvd_card_of_injective {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Injective f) : Nat.card G ∣ Nat.card H := by
  have h : Nat.card G = Nat.card ↥(f.range) :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  rw [h]
  exact Subgroup.card_subgroup_dvd_card f.range

/-- The centre of a nonabelian group of order `8` has order `2`. -/
lemma center_card_eq_two {P : Type} [Group P] [Finite P] (h8 : Nat.card P = 8)
    (hnab : ¬ IsMulCommutative P) : Nat.card ↥(Subgroup.center P) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZdiv : Nat.card ↥(Subgroup.center P) ∣ 8 :=
    h8 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center P)
  obtain ⟨k, _hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 2) (n := 3)
    (G := P) (by rw [h8]; norm_num) (by norm_num)
  have hk3 : k ≤ 3 := by
    have h2 : 2 ^ k ∣ 2 ^ 3 := by rw [hk] at hZdiv; simpa using hZdiv
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
  have hk2 : k ≠ 2 := by
    intro hk2
    have hcard : Nat.card ↥(Subgroup.center P) = 4 := by rw [hk, hk2]; norm_num
    have hq : Nat.card (P ⧸ Subgroup.center P) = 2 := by
      have hci := Subgroup.card_mul_index (Subgroup.center P)
      rw [Subgroup.index_eq_card, hcard, h8] at hci
      omega
    have hcyc : IsCyclic (P ⧸ Subgroup.center P) := isCyclic_of_prime_card (p := 2) hq
    exact hnab (isMulCommutative_of_isCyclic_quotient_center_self P)
  have hk3' : k ≠ 3 := by
    intro hk3
    have hcard : Nat.card ↥(Subgroup.center P) = 8 := by rw [hk, hk3]; norm_num
    have htop : Subgroup.center P = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, h8])
    exact hnab ((Subgroup.center_eq_top_iff).mp htop)
  have : k = 1 := by omega
  rw [hk, this]; norm_num

/-- The induced automorphism of `P ⧸ Z(P)`. -/
noncomputable def quotCenterAut {P : Type} [Group P] (α : MulAut P) :
    MulAut (P ⧸ Subgroup.center P) :=
  QuotientGroup.congr (Subgroup.center P) (Subgroup.center P) (α : P ≃* P)
    (Subgroup.map_center_eq (f := (α : P ≃* P)))

/-- The map sending an automorphism of `P` to the induced automorphism of `P ⧸ Z(P)`
is a monoid homomorphism. -/
noncomputable def quotCenterHom {P : Type} [Group P] :
    MulAut P →* MulAut (P ⧸ Subgroup.center P) where
  toFun := quotCenterAut
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) x
    simp only [quotCenterAut, QuotientGroup.congr_mk', MulAut.one_apply]
  map_mul' α β := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) x
    simp only [quotCenterAut, QuotientGroup.congr_mk', MulAut.mul_apply]

/-- If the centre of `P` has order `2`, then every automorphism of `P` fixes the centre
pointwise. -/
lemma fixOnCenter {P : Type} [Group P] [Finite P] (hZ : Nat.card ↥(Subgroup.center P) = 2)
    (α : MulAut P) : ∀ z : ↥(Subgroup.center P), α (z : P) = (z : P) := by
  intro z
  have hmap : (Subgroup.center P).map (α : P →* P) = Subgroup.center P :=
    Subgroup.map_center_eq α
  let σ : MulAut ↥(Subgroup.center P) :=
    ((α : P ≃* P).subgroupMap (Subgroup.center P)).trans (MulEquiv.subgroupCongr hmap)
  have hσ : σ = 1 := mulAut_eq_one_of_card_two hZ σ
  have hz : σ z = z := by rw [hσ]; rfl
  have hcoe : ((σ z : ↥(Subgroup.center P)) : P) = α (z : P) := by
    simp [σ, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]
  rw [← hcoe, hz]

/-- An automorphism whose order is odd and which is trivial on `P ⧸ Z(P)` (where the centre
has order `2`) is trivial. -/
lemma quotCenterHom_eq_one_imp {P : Type} [Group P] [Finite P]
    (hZ : Nat.card ↥(Subgroup.center P) = 2) (α : MulAut P)
    (hα : quotCenterHom α = 1) (hodd : Odd (orderOf α)) : α = 1 := by
  have hk : ∀ g : P, (QuotientGroup.mk' (Subgroup.center P) (α g))
      = (QuotientGroup.mk' (Subgroup.center P) g) := by
    intro g
    have h := DFunLike.congr_fun hα (QuotientGroup.mk' (Subgroup.center P) g)
    simpa [quotCenterHom, quotCenterAut, QuotientGroup.congr_mk'] using h
  have hdiv : ∀ g : P, α g * g⁻¹ ∈ Subgroup.center P := by
    intro g
    have h1 : (α g : P ⧸ Subgroup.center P) = (g : P ⧸ Subgroup.center P) := hk g
    have h2 := QuotientGroup.eq_iff_div_mem.mp h1
    rwa [div_eq_mul_inv] at h2
  haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
  have hsq : ∀ g : P, (α g * g⁻¹) ^ 2 = 1 := by
    intro g
    have h2card : Fintype.card ↥(Subgroup.center P) = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hZ
    have hp : (⟨α g * g⁻¹, hdiv g⟩ : ↥(Subgroup.center P)) ^
        Fintype.card ↥(Subgroup.center P) = 1 := pow_card_eq_one
    rw [h2card] at hp
    have := congrArg (Subtype.val) hp
    simpa using this
  have hsqr : α ^ 2 = 1 := by
    ext g
    show α (α g) = g
    have hαg : α g = (α g * g⁻¹) * g := by group
    have hfix : α (α g * g⁻¹) = α g * g⁻¹ := fixOnCenter hZ α ⟨α g * g⁻¹, hdiv g⟩
    calc α (α g)
        = α ((α g * g⁻¹) * g) := congrArg α hαg
      _ = α (α g * g⁻¹) * α g := by rw [map_mul]
      _ = (α g * g⁻¹) * α g := by rw [hfix]
      _ = (α g * g⁻¹) * ((α g * g⁻¹) * g) := congrArg (fun x => (α g * g⁻¹) * x) hαg
      _ = g := by rw [← mul_assoc, ← sq, hsq g, one_mul]
  have hdvd : orderOf α ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsqr
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd; exact absurd hodd (by decide)

theorem card_eq_one_or_three_of_odd_order_subgroup_mulAut {P : Type} [Group P] [Finite P]
    (h8 : Nat.card P = 8) (hnab : ¬ IsMulCommutative P) (A : Subgroup (MulAut P))
    (hodd : Odd (Nat.card A)) : Nat.card A = 1 ∨ Nat.card A = 3 := by
  classical
  have hZ : Nat.card ↥(Subgroup.center P) = 2 := center_card_eq_two h8 hnab
  haveI : Fintype ↥A := Fintype.ofFinite _
  -- every element of `A` has odd order
  have hoddel : ∀ z : ↥A, Odd (orderOf ((z : MulAut P))) := by
    intro z
    have hdvd : orderOf z ∣ Nat.card ↥A := by
      rw [Nat.card_eq_fintype_card]
      exact orderOf_dvd_card (x := z)
    have hoddz : Odd (orderOf z) := Odd.of_dvd_nat hodd hdvd
    rw [Subgroup.orderOf_coe]
    exact hoddz
  -- the induced map `A →* MulAut (P ⧸ Z(P))` is injective
  let φ : ↥A →* MulAut (P ⧸ Subgroup.center P) := quotCenterHom.comp A.subtype
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hφ1 : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hφ1' : quotCenterHom ((x * y⁻¹ : ↥A) : MulAut P) = 1 := hφ1
    have hz : ((x * y⁻¹ : ↥A) : MulAut P) = 1 :=
      quotCenterHom_eq_one_imp hZ _ hφ1' (hoddel (x * y⁻¹))
    exact mul_inv_eq_one.mp (Subtype.ext hz)
  have hdvd1 : Nat.card ↥A ∣ Nat.card (MulAut (P ⧸ Subgroup.center P)) :=
    card_dvd_card_of_injective φ hφinj
  have hQ : Nat.card (P ⧸ Subgroup.center P) = 4 := by
    have hci := Subgroup.card_mul_index (Subgroup.center P)
    rw [Subgroup.index_eq_card, hZ, h8] at hci
    omega
  have hpermeq : Nat.card (Equiv.Perm (P ⧸ Subgroup.center P)) = 24 := by
    haveI : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
    have hQf : Fintype.card (P ⧸ Subgroup.center P) = 4 := by
      rw [← Nat.card_eq_fintype_card]; exact hQ
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hQf]
    norm_num
  have hdvd2 : Nat.card (MulAut (P ⧸ Subgroup.center P)) ∣ 24 := by
    have hinj : Function.Injective (MulAut.toPerm (P ⧸ Subgroup.center P)) := by
      intro f g h
      ext x
      have := DFunLike.congr_fun h x
      exact this
    have h := card_dvd_card_of_injective (MulAut.toPerm (P ⧸ Subgroup.center P)) hinj
    rwa [hpermeq] at h
  have hdvd : Nat.card ↥A ∣ 24 := hdvd1.trans hdvd2
  -- `|A|` is odd and divides `24 = 2^3 · 3`, hence divides `3`
  have hcop : Nat.Coprime (Nat.card ↥A) 8 := by
    have h2 : Nat.Coprime (Nat.card ↥A) 2 := Nat.coprime_two_right.mpr hodd
    simpa using h2.pow_right 3
  have hdiv3 : Nat.card ↥A ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
  · exact Or.inl h
  · exact Or.inr h

end Work.ThmF.Prove.Step6
