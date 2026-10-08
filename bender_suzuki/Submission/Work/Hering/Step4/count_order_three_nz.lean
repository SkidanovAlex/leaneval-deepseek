import Mathlib
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.Step4.card_six_mul_centralizer
import Submission.Work.Hering.Step4.perm_eq_one_of_card_three
import Submission.Work.Hering.Step3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Step 4: counting the elements of order `3`

Peterfalvi I §2, Step 4 (see `Work.Hering.Step4.card_four_false`): with `V = Inv(G) ∪ {1}` of
order `4` and `C = C_G(V)` a `2`-group, the elements of order `3` of `G` are exactly the `2 * |C|`
elements of the two cosets of `C` consisting of the elements that induce a `3`-cycle of `V#`.

The proof fixes an element `z` of order `3` (which exists since `3 ∣ |G| = 6 * |C|`) and exhibits
the bijection

`↥C × Bool → {g : G // orderOf g = 3}`, `(c, false) ↦ c * z`, `(c, true) ↦ c * z ^ 2`.

Everything rests on the conjugation action `ρ` of `G` on the three involutions of `G`:

* its kernel is `C` (`ker_toPermHom_involutions_eq_centralizer`), so `ρ` identifies `G/C` with a
  subgroup of the symmetric group of a three-element set, of order `6 ≤ 8`;
* `orderOf (ρ g) = 3 ↔ orderOf g = 3`: an element of order `3` does not lie in the `2`-group `C`,
  while conversely `ρ g` of order `3` is a fixed-point-free permutation, so that `g ^ 3 ∈ C`
  would give an involution commuting with `g`;
* by `eq_or_eq_sq_of_orderOf_eq_three_of_card_le_eight`, the elements of order `3` of that
  symmetric group are just `ρ z` and `(ρ z) ^ 2`, whence `S = C·z ⊔ C·z ^ 2`.
-/

set_option autoImplicit false

namespace Work.Hering.Step4

open LeanEval.GroupTheory.Defs Work.Hering

/-- The set of involutions of `G`, carrying the conjugation action of `G` from
`Work.Hering.Step3.instMulActionInvolutions`.  Private, to avoid clashing with neighbouring files
of the area. -/
private abbrev InvSet (G : Type*) [Group G] : Type _ := {x : G // x ∈ involutions G}

/-- The two exponents `1` and `2` of a generator of a group of order `3`. -/
private def expo : Bool → ℕ
  | false => 1
  | true => 2

/-- In a finite group `H` of order at most `8`, two elements of order `3` are equal or inverse to
each other: the subgroups they generate have order `3`, and distinct such subgroups intersect
trivially, so their product would have `9 > 8` elements. -/
theorem eq_or_eq_sq_of_orderOf_eq_three_of_card_le_eight {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H ≤ 8) {z h : H} (hz : orderOf z = 3) (hh : orderOf h = 3) :
    h = z ∨ h = z ^ 2 := by
  have hz3 : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz]
  have hh3 : Nat.card ↥(Subgroup.zpowers h) = 3 := by rw [Nat.card_zpowers, hh]
  have hmem : h ∈ Subgroup.zpowers z := by
    by_contra hnot
    have hinf : ∀ y : H, y ∈ Subgroup.zpowers z → y ∈ Subgroup.zpowers h → y = 1 := by
      intro y hyz hyh
      by_contra hy1
      have hdvd : orderOf y ∣ 3 := by
        rw [← hz]
        exact orderOf_dvd_of_mem_zpowers hyz
      have hyord : orderOf y = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hy1
        · exact h1
      have hzy : Subgroup.zpowers y = Subgroup.zpowers z := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyz) ?_
        rw [hz3, Nat.card_zpowers, hyord]
      have hhy : Subgroup.zpowers y = Subgroup.zpowers h := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyh) ?_
        rw [hh3, Nat.card_zpowers, hyord]
      exact hnot (by rw [← hzy, hhy]; exact Subgroup.mem_zpowers h)
    have hinj : Function.Injective
        (fun p : ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers h) => (p.1 : H) * (p.2 : H)) := by
      rintro ⟨a1, a2⟩ ⟨b1, b2⟩ heq
      have heq' : (a1 : H) * (a2 : H) = (b1 : H) * (b2 : H) := heq
      have h1 : ((b1 : H))⁻¹ * (a1 : H) = (b2 : H) * ((a2 : H))⁻¹ := by
        calc ((b1 : H))⁻¹ * (a1 : H)
            = ((b1 : H))⁻¹ * ((a1 : H) * (a2 : H)) * ((a2 : H))⁻¹ := by group
          _ = ((b1 : H))⁻¹ * ((b1 : H) * (b2 : H)) * ((a2 : H))⁻¹ := by rw [heq']
          _ = (b2 : H) * ((a2 : H))⁻¹ := by group
      have h2 : ((b1 : H))⁻¹ * (a1 : H) = 1 :=
        hinf _ ((Subgroup.zpowers z).mul_mem ((Subgroup.zpowers z).inv_mem b1.2) a1.2)
          (by rw [h1]
              exact (Subgroup.zpowers h).mul_mem b2.2 ((Subgroup.zpowers h).inv_mem a2.2))
      have ha1 : (a1 : H) = (b1 : H) := by
        calc (a1 : H) = (b1 : H) * (((b1 : H))⁻¹ * (a1 : H)) := by group
          _ = (b1 : H) := by rw [h2, mul_one]
      have ha2 : (a2 : H) = (b2 : H) := by
        calc (a2 : H) = ((a1 : H))⁻¹ * ((a1 : H) * (a2 : H)) := by group
          _ = ((a1 : H))⁻¹ * ((b1 : H) * (b2 : H)) := by rw [heq']
          _ = (b2 : H) := by rw [ha1]; group
      exact Prod.ext (Subtype.ext ha1) (Subtype.ext ha2)
    have hle := Nat.card_le_card_of_injective
      (fun p : ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers h) => (p.1 : H) * (p.2 : H)) hinj
    rw [Nat.card_prod, hz3, hh3] at hle
    omega
  -- `z` has order `3`, so `1`, `z` and `z ^ 2` are the three elements of `⟨z⟩`
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz2 : z ^ 2 ≠ 1 := by
    intro h1
    have h2 : orderOf z ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact h1
    rw [hz] at h2
    exact absurd h2 (by norm_num)
  have hzz : z ≠ z ^ 2 := by
    intro h1
    have h2 : z * 1 = z * z := by
      rw [mul_one, ← pow_two]
      exact h1
    exact hz1 (mul_left_cancel h2).symm
  have hnc : ({1, z, z ^ 2} : Set H).ncard = 3 := by
    rw [show ({1, z, z ^ 2} : Set H) = insert (1 : H) (insert z ({z ^ 2} : Set H)) from rfl]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1.symm, hz2.symm⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      exact hzz)]
    rw [Set.ncard_singleton]
  have hw : (Subgroup.zpowers z : Set H).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hz3
  have hsubset : ({1, z, z ^ 2} : Set H) ⊆ (Subgroup.zpowers z : Set H) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h1 | h2 | h3
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h2]; exact Subgroup.mem_zpowers z
    · rw [h3]; exact pow_mem (Subgroup.mem_zpowers z) 2
  have hset : (Subgroup.zpowers z : Set H) = {1, z, z ^ 2} :=
    (Set.eq_of_subset_of_ncard_le (s := ({1, z, z ^ 2} : Set H))
      (t := (Subgroup.zpowers z : Set H)) hsubset (by rw [hw, hnc])).symm
  have hmem' : h ∈ ({1, z, z ^ 2} : Set H) := by rw [← hset]; exact hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
  rcases hmem' with h1 | h1 | h1
  · exfalso
    rw [h1, orderOf_one] at hh
    exact absurd hh (by norm_num)
  · exact Or.inl h1
  · exact Or.inr h1

/-- The kernel of the conjugation action of `G` on its involutions is the centraliser of
`V = Inv(G) ∪ {1}`. -/
theorem ker_toPermHom_involutions_eq_centralizer {G : Type*} [Group G] {hDT : DTInv G}
    {h4 : HasFourGroup G} :
    (MulAction.toPermHom G (InvSet G)).ker
      = Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg y hy
    rcases (mem_invSubgroup hDT h4).mp hy with hy2 | hy1
    · have h1 : (MulAction.toPermHom G (InvSet G)) g ⟨y, hy2⟩ = ⟨y, hy2⟩ := by rw [hg]; rfl
      have h2 : g * y * g⁻¹ = y := congrArg (fun t : InvSet G => (t : G)) h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · rw [hy1, one_mul, mul_one]
  · intro hg
    ext x
    show g * (x : G) * g⁻¹ = (x : G)
    have hcomm : (x : G) * g = g * (x : G) :=
      hg (x : G) (involutions_subset_invSubgroup hDT h4 x.2)
    rw [← hcomm]
    group

theorem count_order_three_nz {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G}
    (hC : ∀ U : Subgroup G, U ≤ invSubgroup hDT h4 → Nat.card U = 4 →
      IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)))
    (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    Nat.card {g : G // orderOf g = 3}
      = 2 * Nat.card ↥(Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- the centraliser `C = C_G(V)` of `V = invSubgroup hDT h4`
  let C : Subgroup G := Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)
  have hCV : IsPGroup 2 ↥C := hC (invSubgroup hDT h4) le_rfl hV
  have hcardG : Nat.card G = 6 * Nat.card ↥C := card_six_mul_centralizer hV
  -- an element of order `3` exists, since `3 ∣ |G| = 6 * |C|`
  have h3dvd : 3 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, hcardG]
    exact ⟨2 * Nat.card ↥C, by ring⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 3 h3dvd
  -- `C` is a 2-group, so no element of order `3` lies in it
  have hnotmem : ∀ x : G, orderOf x = 3 → x ∉ C := by
    intro x hx hxC
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hCV) ⟨x, hxC⟩
    have hm' : orderOf x = 2 ^ m := (Subgroup.orderOf_coe (⟨x, hxC⟩ : ↥C)).trans hm
    rw [hx] at hm'
    have hdiv : 3 ∣ 2 ^ m := hm' ▸ dvd_refl 3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv) (by norm_num)
  -- the conjugation action of `G` on its involutions
  let ρ : G →* Equiv.Perm (InvSet G) := MulAction.toPermHom G (InvSet G)
  have hker : ρ.ker = C := ker_toPermHom_involutions_eq_centralizer
  have hcardInv : Fintype.card (InvSet G) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_involutions_eq_three hV
  have hcardInvPerm : Nat.card (Equiv.Perm (InvSet G)) ≤ 8 := by
    rw [Nat.card_perm, card_involutions_eq_three hV]
    norm_num
  -- an element inducing a permutation of order `3` has no fixed point
  have hnoFix : ∀ g : G, orderOf (ρ g) = 3 → ∀ x : InvSet G, (ρ g) x ≠ x := by
    intro g hg x hx
    have h1 : ρ g = 1 :=
      perm_eq_one_of_card_three hcardInv (by rw [← hg]; exact pow_orderOf_eq_one _) ⟨x, hx⟩
    rw [h1] at hg
    simp at hg
  have hρz : orderOf (ρ z) = 3 := by
    have hdvd : orderOf (ρ z) ∣ 3 := by rw [← hz]; exact orderOf_map_dvd ρ z
    have hne : ρ z ≠ 1 := by
      intro h1
      exact hnotmem z hz (by rw [← hker]; exact MonoidHom.mem_ker.mpr h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hne
    · exact h2
  have hρz_sq : orderOf ((ρ z) ^ 2) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have h3 : (ρ z) ^ 3 = 1 := by rw [← hρz]; exact pow_orderOf_eq_one _
      calc ((ρ z) ^ 2) ^ 3 = (ρ z) ^ (2 * 3) := (pow_mul (ρ z) 2 3).symm
        _ = (ρ z) ^ (3 * 2) := by rw [show 2 * 3 = 3 * 2 from rfl]
        _ = ((ρ z) ^ 3) ^ 2 := pow_mul (ρ z) 3 2
        _ = 1 := by rw [h3, one_pow]
    · intro h1
      have h2 : orderOf (ρ z) ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact h1
      rw [hρz] at h2
      exact absurd h2 (by norm_num)
  -- the elements of order `3` are exactly the elements inducing a `3`-cycle
  have hcrit : ∀ g : G, orderOf (ρ g) = 3 ↔ orderOf g = 3 := by
    intro g
    constructor
    · intro hg
      have hg3C : g ^ 3 ∈ C := by
        rw [← hker, MonoidHom.mem_ker, map_pow, ← hg, pow_orderOf_eq_one]
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hCV) ⟨g ^ 3, hg3C⟩
      have hm' : orderOf (g ^ 3) = 2 ^ m :=
        (Subgroup.orderOf_coe (⟨g ^ 3, hg3C⟩ : ↥C)).trans hm
      cases m with
      | zero =>
        have h1 : g ^ 3 = 1 := by rw [← orderOf_eq_one_iff, hm', pow_zero]
        have hne : g ≠ 1 := by
          intro h
          rw [h, map_one] at hg
          simp at hg
        have hdvd : orderOf g ∣ 3 := by rw [orderOf_dvd_iff_pow_eq_one]; exact h1
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h2 | h2
        · exact absurd (orderOf_eq_one_iff.mp h2) hne
        · exact h2
      | succ m' =>
        -- `t = (g ^ 3) ^ (2 ^ m')` is an involution commuting with `g`
        exfalso
        set t : G := (g ^ 3) ^ (2 ^ m') with ht_def
        have ht_sq : t * t = 1 := by
          rw [ht_def, ← pow_two, ← pow_mul,
            show 2 ^ m' * 2 = 2 ^ (m' + 1) from (pow_succ 2 m').symm, ← hm',
            pow_orderOf_eq_one]
        have ht_ne : t ≠ 1 := by
          intro h1
          rw [ht_def] at h1
          have hd : orderOf (g ^ 3) ∣ 2 ^ m' := by
            rw [orderOf_dvd_iff_pow_eq_one]; exact h1
          rw [hm'] at hd
          have hle : 2 ^ (m' + 1) ≤ 2 ^ m' := Nat.le_of_dvd (pow_pos (by norm_num) m') hd
          have hlt : 2 ^ m' < 2 ^ (m' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        have ht_inv : t ∈ involutions G := by
          rw [mem_involutions]
          exact orderOf_eq_two_of_sq_eq_one ht_sq ht_ne
        have ht_pow : t = g ^ (3 * 2 ^ m') := by rw [ht_def, ← pow_mul]
        have ht_comm : g * t = t * g := by
          rw [ht_pow]
          exact (pow_succ' g (3 * 2 ^ m')).symm.trans (pow_succ g (3 * 2 ^ m'))
        have hfix : (ρ g) ⟨t, ht_inv⟩ = ⟨t, ht_inv⟩ := by
          apply Subtype.ext
          show g * t * g⁻¹ = t
          rw [ht_comm]
          group
        exact hnoFix g hg ⟨t, ht_inv⟩ hfix
    · intro hg
      have hdvd : orderOf (ρ g) ∣ 3 := by rw [← hg]; exact orderOf_map_dvd ρ g
      have hne : ρ g ≠ 1 := by
        intro h1
        exact hnotmem g hg (by rw [← hker]; exact MonoidHom.mem_ker.mpr h1)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) hne
      · exact h2
  have hzC : z ∉ C := hnotmem z hz
  -- the map `(c, b) ↦ c * z ^ (expo b)`
  have hPsi_mem : ∀ (c : ↥C) (b : Bool), orderOf ((c : G) * z ^ (expo b)) = 3 := by
    intro c b
    have hρc : ρ (c : G) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact c.2
    have hgoal : orderOf (ρ ((c : G) * z ^ (expo b))) = 3 := by
      rw [map_mul, map_pow, hρc, one_mul]
      cases b
      · rw [show expo false = 1 from rfl, pow_one]
        exact hρz
      · rw [show expo true = 2 from rfl]
        exact hρz_sq
    exact (hcrit _).mp hgoal
  let Ψ : ↥C × Bool → {g : G // orderOf g = 3} :=
    fun p => ⟨(p.1 : G) * z ^ (expo p.2), hPsi_mem p.1 p.2⟩
  have hΨ_apply : ∀ (c : ↥C) (b : Bool), (Ψ (c, b)).1 = (c : G) * z ^ (expo b) := by
    intro c b
    rfl
  have hPsi_inj : Function.Injective Ψ := by
    rintro ⟨⟨c, hc⟩, b⟩ ⟨⟨d, hd⟩, b'⟩ heq
    have hmain : (c : G) * z ^ (expo b) = (d : G) * z ^ (expo b') := by
      have h1 := congrArg Subtype.val heq
      rwa [hΨ_apply ⟨c, hc⟩ b, hΨ_apply ⟨d, hd⟩ b'] at h1
    cases b <;> cases b'
    · rw [show expo false = 1 from rfl, pow_one] at hmain
      have hcd : (c : G) = (d : G) := mul_right_cancel hmain
      exact Prod.ext (Subtype.ext hcd) rfl
    · exfalso
      rw [show expo false = 1 from rfl, pow_one, show expo true = 2 from rfl] at hmain
      have h3 : (d : G)⁻¹ * (c : G) * z = z ^ 2 := by
        calc (d : G)⁻¹ * (c : G) * z = (d : G)⁻¹ * ((c : G) * z) := by group
          _ = (d : G)⁻¹ * ((d : G) * z ^ 2) := by rw [hmain]
          _ = z ^ 2 := by group
      have h2 : (d : G)⁻¹ * (c : G) * z = z * z := by rw [h3, pow_two]
      have hzc : (d : G)⁻¹ * (c : G) = z := mul_right_cancel h2
      exact hzC (by rw [← hzc]; exact C.mul_mem (C.inv_mem hd) hc)
    · exfalso
      rw [show expo true = 2 from rfl, show expo false = 1 from rfl, pow_one] at hmain
      have h3 : (d : G)⁻¹ * (c : G) * z ^ 2 = z := by
        calc (d : G)⁻¹ * (c : G) * z ^ 2 = (d : G)⁻¹ * ((c : G) * z ^ 2) := by group
          _ = (d : G)⁻¹ * ((d : G) * z) := by rw [hmain]
          _ = z := by group
      have h2 : (d : G)⁻¹ * (c : G) * z = 1 := by
        calc (d : G)⁻¹ * (c : G) * z = ((d : G)⁻¹ * (c : G) * z ^ 2) * z⁻¹ := by group
          _ = z * z⁻¹ := by rw [h3]
          _ = 1 := mul_inv_cancel z
      have hzc : (d : G)⁻¹ * (c : G) = z⁻¹ := by
        calc (d : G)⁻¹ * (c : G) = (d : G)⁻¹ * (c : G) * z * z⁻¹ := by group
          _ = 1 * z⁻¹ := by rw [h2]
          _ = z⁻¹ := one_mul _
      have hmem : (d : G)⁻¹ * (c : G) ∈ C := C.mul_mem (C.inv_mem hd) hc
      have hzmem : z⁻¹ ∈ C := by rw [← hzc]; exact hmem
      exact hzC (by simpa using C.inv_mem hzmem)
    · rw [show expo true = 2 from rfl] at hmain
      have hcd : (c : G) = (d : G) := mul_right_cancel hmain
      exact Prod.ext (Subtype.ext hcd) rfl
  have hPsi_surj : Function.Surjective Ψ := by
    rintro ⟨g, hg⟩
    have hρg : orderOf (ρ g) = 3 := (hcrit g).mpr hg
    rcases eq_or_eq_sq_of_orderOf_eq_three_of_card_le_eight hcardInvPerm hρz hρg with
      hcase | hcase
    · have hmem : g * z⁻¹ ∈ C := by
        rw [← hker, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [hcase, mul_inv_cancel]
      refine ⟨(⟨g * z⁻¹, hmem⟩, false), ?_⟩
      apply Subtype.ext
      rw [hΨ_apply]
      show (g * z⁻¹) * z ^ (expo false) = g
      rw [show expo false = 1 from rfl, pow_one]
      group
    · have hmem : g * (z ^ 2)⁻¹ ∈ C := by
        rw [← hker, MonoidHom.mem_ker]
        simp only [map_mul, map_inv, map_pow]
        rw [hcase]
        simp
      refine ⟨(⟨g * (z ^ 2)⁻¹, hmem⟩, true), ?_⟩
      apply Subtype.ext
      rw [hΨ_apply]
      show (g * (z ^ 2)⁻¹) * z ^ (expo true) = g
      rw [show expo true = 2 from rfl]
      group
  have hcard : Nat.card {g : G // orderOf g = 3} = Nat.card (↥C × Bool) :=
    (Nat.card_congr (Equiv.ofBijective Ψ ⟨hPsi_inj, hPsi_surj⟩)).symm
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  show Nat.card {g : G // orderOf g = 3} = 2 * Nat.card ↥C
  rw [hcard, Nat.card_prod, hbool, Nat.mul_comm]

end Work.Hering.Step4
