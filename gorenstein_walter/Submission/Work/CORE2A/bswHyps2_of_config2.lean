import Mathlib
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.Extra
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.DSTR.dihedralSubgroup

/-!
# `CORE2A`: the configuration of Lemma 2.2 produces `BSWHyps2`
-/

open scoped MatrixGroups

namespace Work.GW2

/-- Spellings: the statement of `Work.CORE2A.bswHyps2_of_config2` uses the name `invset`.
It is the same set as `Work.GW2.invSet`, whose definition is the one in use in the area. -/
def invset {G : Type*} [Group G] (K : Subgroup G) (s : G) : Set G := invSet K s

end Work.GW2

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. Elementary facts about a join `U ⊔ S₀` whose factors commute -/

/-- If `s` inverts `K`, then `K` is commutative. -/
theorem isMulCommutative_of_inverts {G : Type*} [Group G] {s : G} {K : Subgroup G}
    (h : Inverts s K) : IsMulCommutative K := by
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  have h1 : s * (a : G) * s⁻¹ = (a : G)⁻¹ := h a a.2
  have h2 : s * (b : G) * s⁻¹ = (b : G)⁻¹ := h b b.2
  have h3 : s * ((a : G) * (b : G)) * s⁻¹ = ((a : G) * (b : G))⁻¹ := h _ (K.mul_mem a.2 b.2)
  rw [mul_inv_rev] at h3
  have h4 : s * ((a : G) * (b : G)) * s⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
    rw [← h1, ← h2]; group
  rw [h4] at h3
  have h5 := congrArg Inv.inv h3
  simpa using h5.symm

/-- Commutativity is preserved by a multiplicative equivalence. -/
theorem isMulCommutative_of_mulEquiv {M N : Type*} [Mul M] [Mul N] (e : M ≃* N)
    [IsMulCommutative M] : IsMulCommutative N := by
  refine IsMulCommutative.of_comm fun a b => ?_
  calc a * b = e (e.symm (a * b)) := (e.apply_symm_apply _).symm
    _ = e (e.symm a * e.symm b) := congrArg e (map_mul e.symm a b)
    _ = e (e.symm b * e.symm a) := congrArg e (mul_comm' (e.symm a) (e.symm b))
    _ = e (e.symm (b * a)) := congrArg e (map_mul e.symm b a).symm
    _ = b * a := e.apply_symm_apply _

/-- An element of a cyclic group lies in `{1, t}` when `t` is an involution of that group. -/
theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {s t : G}
    (ht : orderOf t = 2) (h : s ∈ Subgroup.zpowers t) : s = 1 ∨ s = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have h2 : t ^ (2 : ℕ) = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have h1 : t ^ k = t ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k h2
  rw [h1]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [hk, zpow_zero]
  · right; rw [hk]; norm_num

/-- If every element of `U` commutes with every element of `S₀`, then every element of the
join `U ⊔ S₀` is a product `u * g` with `u ∈ U`, `g ∈ S₀`. -/
theorem exists_mul_eq_of_mem_sup_of_comm {G : Type*} [Group G] {U S0 : Subgroup G}
    (hcomm : ∀ u ∈ U, ∀ g ∈ S0, u * g = g * u) {x : G} (hx : x ∈ U ⊔ S0) :
    ∃ u ∈ U, ∃ g ∈ S0, u * g = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, S0.one_mem, by simp⟩
    · exact ⟨1, U.one_mem, y, hy, by simp⟩
  · exact ⟨1, U.one_mem, 1, S0.one_mem, by simp⟩
  · rintro a b _ _ ⟨u1, hu1, g1, hg1, h1⟩ ⟨u2, hu2, g2, hg2, h2⟩
    refine ⟨u1 * u2, U.mul_mem hu1 hu2, g1 * g2, S0.mul_mem hg1 hg2, ?_⟩
    calc (u1 * u2) * (g1 * g2) = ((u1 * u2) * g1) * g2 := by group
      _ = (u1 * (u2 * g1)) * g2 := by group
      _ = (u1 * (g1 * u2)) * g2 := by rw [hcomm u2 hu2 g1 hg1]
      _ = ((u1 * g1) * u2) * g2 := by group
      _ = (u1 * g1) * (u2 * g2) := by group
      _ = a * b := by rw [h1, h2]
  · rintro a _ ⟨u, hu, g, hg, h⟩
    refine ⟨u⁻¹, U.inv_mem hu, g⁻¹, S0.inv_mem hg, ?_⟩
    rw [← h, mul_inv_rev]
    simpa using (congrArg Inv.inv (hcomm u hu g hg)).symm

/-- In a join `U ⊔ S₀` whose factors commute, with `U` of odd order and `S₀` cyclic containing
the involution `t`, the only involutions are `1` and `t`. -/
theorem eq_one_or_eq_of_sq_eq_one_of_comm_sup {G : Type*} [Group G] [Finite G]
    (U S0 : Subgroup G) {t : G} (hcomm : ∀ u ∈ U, ∀ g ∈ S0, u * g = g * u)
    (hUodd : Odd (Nat.card U)) (hdisj : U ⊓ S0 = ⊥) (hcyc : IsCyclic S0)
    (ht : t ∈ S0) (ht2 : orderOf t = 2) :
    ∀ x ∈ U ⊔ S0, x ^ 2 = 1 → x = 1 ∨ x = t := by
  intro x hx hx2
  obtain ⟨u, hu, g, hg, hug⟩ := exists_mul_eq_of_mem_sup_of_comm hcomm hx
  have hc : Commute u g := hcomm u hu g hg
  have hcalc : x ^ 2 = u ^ 2 * g ^ 2 := by rw [← hug, hc.mul_pow 2]
  have hx2' : u ^ 2 * g ^ 2 = 1 := by rw [← hcalc]; exact hx2
  have hg2mem : g ^ 2 ∈ U ⊓ S0 := by
    refine Subgroup.mem_inf.mpr ⟨?_, S0.pow_mem hg 2⟩
    have hgeq : g ^ 2 = (u ^ 2)⁻¹ := by
      have h := congrArg Inv.inv (eq_inv_of_mul_eq_one_left hx2')
      simpa using h.symm
    rw [hgeq]
    exact U.inv_mem (U.pow_mem hu 2)
  have hg2 : g ^ 2 = 1 := by
    have h := hg2mem
    rw [hdisj] at h
    simpa using h
  have hu2 : u ^ 2 = 1 := by
    have h := hx2'; rw [hg2, mul_one] at h; exact h
  have hu1 : u = 1 := by
    have hdvd : orderOf u ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hu
    have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr (h ▸ hdvd))
  rw [← hug, hu1, one_mul]
  have hdvd3 : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd3 with h | h
  · left; exact orderOf_eq_one_iff.mp h
  · right
    haveI : IsCyclic ↥S0 := hcyc
    exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic
      (a := (⟨g, hg⟩ : ↥S0)) (b := (⟨t, ht⟩ : ↥S0))
      (by rw [Subgroup.orderOf_mk]; exact h) (by rw [Subgroup.orderOf_mk]; exact ht2))

/-- An element of odd order in a join `U ⊔ S₀` whose factors commute (with `S₀` a 2-group) lies
in `U`. -/
theorem mem_left_of_odd_orderOf_of_comm_sup {G : Type*} [Group G]
    (U S0 : Subgroup G) (hcomm : ∀ u ∈ U, ∀ g ∈ S0, u * g = g * u) (hdisj : U ⊓ S0 = ⊥)
    (hS0 : IsPGroup 2 S0) {x : G} (hx : x ∈ U ⊔ S0) (hodd : Odd (orderOf x)) : x ∈ U := by
  obtain ⟨u, hu, g, hg, hug⟩ := exists_mul_eq_of_mem_sup_of_comm hcomm hx
  have hc : Commute u g := hcomm u hu g hg
  have hxpow : u ^ orderOf x * g ^ orderOf x = 1 := by
    rw [← hc.mul_pow (orderOf x), hug]
    exact pow_orderOf_eq_one x
  have hgmem : g ^ orderOf x ∈ U ⊓ S0 := by
    refine Subgroup.mem_inf.mpr ⟨?_, S0.pow_mem hg _⟩
    have hgeq : g ^ orderOf x = (u ^ orderOf x)⁻¹ := by
      have h := congrArg Inv.inv (eq_inv_of_mul_eq_one_left hxpow)
      simpa using h.symm
    rw [hgeq]
    exact U.inv_mem (U.pow_mem hu _)
  have hgpow : g ^ orderOf x = 1 := by
    have h := hgmem
    rw [hdisj] at h
    simpa using h
  have hdvd : orderOf g ∣ orderOf x := orderOf_dvd_iff_pow_eq_one.mpr hgpow
  have hoddg : Odd (orderOf g) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hodd))
  obtain ⟨k, hk⟩ := hS0 (⟨g, hg⟩ : ↥S0)
  have hdvd2 : orderOf g ∣ 2 ^ k := by
    have h1 : orderOf (⟨g, hg⟩ : ↥S0) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    rwa [Subgroup.orderOf_mk] at h1
  have hone : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd
    ((Nat.coprime_two_right.mpr hoddg).pow_right k) hdvd2
  have hg1 : g = 1 := orderOf_eq_one_iff.mp hone
  rw [← hug, hg1, mul_one]
  exact hu

/-- If `H = U ⊔ S` with `U ⊴ H` and `S` a 2-group, then every element of `H` of odd order
lies in `U` (as `H/U` is a 2-group). -/
theorem mem_of_odd_orderOf_of_sup_normal {G : Type*} [Group G] [Finite G]
    (H U S : Subgroup G) (hUle : U ≤ H) (hSle : S ≤ H) (hUS : U ⊔ S = H)
    (hUnorm : (U.subgroupOf H).Normal) (hS2 : IsPGroup 2 S)
    {x : G} (hx : x ∈ H) (hodd : Odd (orderOf x)) : x ∈ U := by
  set U' : Subgroup ↥H := U.subgroupOf H with hU'def
  set S' : Subgroup ↥H := S.subgroupOf H with hS'def
  haveI : U'.Normal := hUnorm
  set x' : ↥H := ⟨x, hx⟩ with hx'def
  have htop : U' ⊔ S' = ⊤ := by
    rw [hU'def, hS'def, ← Subgroup.subgroupOf_sup hUle hSle, hUS, Subgroup.subgroupOf_self]
  set φ : ↥H →* (↥H ⧸ U') := QuotientGroup.mk' U' with hφ
  have hker : ∀ z : ↥H, φ z = 1 ↔ z ∈ U' := by
    intro z
    rw [← MonoidHom.mem_ker, hφ, QuotientGroup.ker_mk']
  have hx'top : x' ∈ U' ⊔ S' := by rw [htop]; exact Subgroup.mem_top x'
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left (s := U') (t := S')).mp hx'top
  have hφa : φ a = 1 := (hker a).mpr ha
  have hphib : φ x' = φ b := by rw [← hab, map_mul, hφa, one_mul]
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  have hS'card : Nat.card ↥S' = 2 ^ k := by
    rw [hS'def, ← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv
  have hdvd1 : orderOf (φ x') ∣ orderOf x := by
    have h := orderOf_map_dvd φ x'
    have hxord : orderOf x' = orderOf x := by rw [hx'def, Subgroup.orderOf_mk]
    rwa [hxord] at h
  have hoddφ : Odd (orderOf (φ x')) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_left hdvd1 (Nat.coprime_two_right.mpr hodd))
  have hdvd2 : orderOf (φ x') ∣ 2 ^ k := by
    have hdvb : orderOf (φ x') ∣ orderOf b := by rw [hphib]; exact orderOf_map_dvd φ b
    have hdb : orderOf b ∣ Nat.card ↥S' := Subgroup.orderOf_dvd_natCard S' hb
    rw [hS'card] at hdb
    exact dvd_trans hdvb hdb
  have hone : orderOf (φ x') = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr hoddφ).pow_right k) hdvd2
  have hx'U : x' ∈ U' := (hker x').mp (orderOf_eq_one_iff.mp hone)
  rw [hU'def] at hx'U
  exact Subgroup.mem_subgroupOf.mp hx'U

/-- `O_{2'}(H)` is normal in `H`. -/
theorem oddCoreIn_subgroupOf_normal {G : Type*} [Group G] (H : Subgroup G) :
    ((oddCoreIn H).subgroupOf H).Normal := by
  have hmap : ((oddCore ↥H).map H.subtype).subgroupOf H = oddCore ↥H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact Subgroup.map_subtype_le (oddCore ↥H)
  rw [oddCoreIn, hmap]
  infer_instance

/-! ## 2. The dihedral input: an element of `S \ S₀` inverts `S₀` -/

/-- In `DihedralGroup n` (`n ≥ 2`) an element outside a cyclic subgroup of index two inverts
that subgroup. -/
theorem dihedral_outside_inverts_aux (n : ℕ) (hn : 2 ≤ n) (T : Subgroup (DihedralGroup n))
    (hcyc : IsCyclic T) (hidx : T.relIndex ⊤ = 2) {y : DihedralGroup n} (hy : y ∉ T)
    {z : DihedralGroup n} (hz : z ∈ T) : y * z * y⁻¹ = z⁻¹ := by
  classical
  have hcardT : Nat.card T = n := by
    have h := Subgroup.relIndex_mul_card T ⊤
    rw [hidx, inf_top_eq, Subgroup.card_top, DihedralGroup.nat_card] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  rcases eq_or_ne n 2 with hn2 | hn2
  · subst hn2
    haveI : IsMulCommutative (DihedralGroup 2) := IsKleinFour.isMulCommutative
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [mul_comm' y z]
      _ = z := by group
      _ = z⁻¹ := (IsKleinFour.inv_eq_self z).symm
  · have hn3 : 3 ≤ n := by omega
    haveI : NeZero n := ⟨by omega⟩
    have hTrot : T = Work.Dihedral.rot n := by
      obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top T).mp hcyc
      have hordg : orderOf g = n := by rw [← Nat.card_zpowers g, hg, hcardT]
      have hgR : g ∈ Work.Dihedral.rot n := by
        rcases Work.Dihedral.eq_r_or_sr g with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact Work.Dihedral.r_mem_rot i
        · rw [DihedralGroup.orderOf_sr] at hordg; omega
      have hTR : T ≤ Work.Dihedral.rot n := by
        rw [← hg]; exact Subgroup.zpowers_le.mpr hgR
      exact Subgroup.eq_of_le_of_card_ge hTR (by rw [Work.Dihedral.nat_card_rot, hcardT])
    have hyr : y ∉ Work.Dihedral.rot n := by rw [← hTrot]; exact hy
    have hzr : z ∈ Work.Dihedral.rot n := by rw [← hTrot]; exact hz
    obtain ⟨u, hu⟩ := Work.Dihedral.notMem_rot.mp hyr
    obtain ⟨t, ht⟩ := Work.Dihedral.mem_rot.mp hzr
    subst hu; subst ht
    have h := (Work.DSTR.DihHelp.dih_sr_conj_rot u ⟨t, rfl⟩).1
    rw [h]; group

/-- **Dihedral inversion.** If `S ≅ DihedralGroup n` (`n ≥ 2`), `S₀ ≤ S` is cyclic of index
two, then every `s ∈ S \ S₀` inverts `S₀`. -/
theorem inverts_of_dihedral_cyclic_index_two {G : Type} [Group G] (n : ℕ) (hn : 2 ≤ n)
    (S S0 : Subgroup G) (hD : Nonempty (S ≃* DihedralGroup n)) (hS0 : S0 ≤ S)
    (hcyc : IsCyclic S0) (hidx : S0.relIndex S = 2) :
    ∀ s ∈ S, s ∉ S0 → Work.GW2.Inverts s S0 := by
  classical
  obtain ⟨e⟩ := hD
  intro s hsS hs0
  have hcardS : Nat.card S = 2 * n := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS0 : Nat.card S0 = n := by
    have h := Subgroup.relIndex_mul_card S0 S
    rw [hidx, inf_eq_left.mpr hS0] at h
    rw [hcardS] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  set T : Subgroup (DihedralGroup n) := (S0.subgroupOf S).map e.toMonoidHom with hT
  have hcycT : IsCyclic T := by
    rw [hT]
    exact (Subgroup.equivMapOfInjective (S0.subgroupOf S) e.toMonoidHom e.injective).isCyclic.mp
      ((Subgroup.subgroupOfEquivOfLe hS0).isCyclic.mpr hcyc)
  have hidxT : T.relIndex ⊤ = 2 := by
    rw [hT]
    have hcardMap : Nat.card ((S0.subgroupOf S).map e.toMonoidHom) = n := by
      rw [← Nat.card_congr
            (Subgroup.equivMapOfInjective (S0.subgroupOf S) e.toMonoidHom e.injective).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0).toEquiv]
      exact hcardS0
    have h := Subgroup.relIndex_mul_card ((S0.subgroupOf S).map e.toMonoidHom) ⊤
    rw [inf_top_eq, Subgroup.card_top, DihedralGroup.nat_card, hcardMap] at h
    exact Nat.mul_right_cancel (by omega : 0 < n) h
  have hy : e ⟨s, hsS⟩ ∉ T := by
    rw [hT, Subgroup.mem_map]
    rintro ⟨y, hy, hye⟩
    rw [Subgroup.mem_subgroupOf] at hy
    rw [e.injective hye] at hy
    exact hs0 hy
  intro x hx
  have hxS : x ∈ S := hS0 hx
  have hzT : e ⟨x, hxS⟩ ∈ T := by
    rw [hT, Subgroup.mem_map]
    exact ⟨⟨x, hxS⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
  have key := dihedral_outside_inverts_aux n hn T hcycT hidxT hy hzT
  have hmem : s * x * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS hxS) (S.inv_mem hsS)
  have hxinv : x⁻¹ ∈ S := S.inv_mem hxS
  have heq : (⟨s * x * s⁻¹, hmem⟩ : ↥S) = ⟨s, hsS⟩ * ⟨x, hxS⟩ * (⟨s, hsS⟩ : ↥S)⁻¹ := by
    ext; simp [mul_assoc]
  have hgoal : (⟨s * x * s⁻¹, hmem⟩ : ↥S) = ⟨x⁻¹, hxinv⟩ := by
    apply e.injective
    have hxinv' : (⟨x⁻¹, hxinv⟩ : ↥S) = (⟨x, hxS⟩ : ↥S)⁻¹ := by ext; simp
    rw [hxinv', map_inv, heq, map_mul, map_mul, map_inv]
    exact key
  exact congrArg Subtype.val hgoal

/-! ## 3. `G` simple non-abelian has no normal subgroup of index two -/

theorem no_normal_index_two_of_simple_nonab {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hN2
  haveI : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h] at hN2
    rw [Subgroup.index_bot] at hN2
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have ha2 : a ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [← hN2]; exact orderOf_dvd_natCard a)
    have hb2 : b ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [← hN2]; exact orderOf_dvd_natCard b)
    have hab2 : (a * b) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [← hN2]; exact orderOf_dvd_natCard (a * b))
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ha2)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hb2)
    have hh : (a * b) * (a * b) = 1 := by simpa [pow_two] using hab2
    rw [eq_inv_of_mul_eq_one_left hh, mul_inv_rev, hai, hbi]
  · rw [h] at hN2
    rw [Subgroup.index_top] at hN2
    exact absurd hN2 (by norm_num)

/-! ## 4. The main theorem -/

theorem bswHyps2_of_config2 (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (hdihed : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) (s : G) (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (hsord : orderOf s = 2) (hI : (B.U : Set G) = Work.GW2.invset B.U s) (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G)) (hNX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ B.U → Subgroup.normalizer (X : Set G) ≤ B.H) : Work.GW2.BSWHyps2 G B.t s (B.U ⊔ B.S0) := by
  classical
  haveI : IsSimpleGroup G := hctx.simple
  obtain ⟨n, hn2, hD⟩ := hdihed
  -- `s` inverts `U`
  have hU_inv : Work.GW2.Inverts s B.U := by
    intro x hx
    have hx' : x ∈ Work.GW2.invset B.U s := hI ▸ hx
    exact hx'.2
  have hU_comm : IsMulCommutative B.U := isMulCommutative_of_inverts hU_inv
  have hS0_comm : IsMulCommutative B.S0 := by
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    infer_instance
  have hK_comm : IsMulCommutative ↥(B.U ⊔ B.S0) :=
    isMulCommutative_sup_of_le_centralizer hS0C hU_comm hS0_comm
  have hcomm_elem : ∀ u ∈ B.U, ∀ g ∈ B.S0, u * g = g * u :=
    fun u hu g hg => Subgroup.mem_centralizer_iff.mp (hS0C hg) u hu
  have hS0_inv : Work.GW2.Inverts s B.S0 :=
    inverts_of_dihedral_cyclic_index_two n hn2 (B.S : Subgroup G) B.S0 hD B.S0_le B.S0_cyclic
      B.S0_index s hsS hs0
  -- `U ⊓ S₀ = ⊥`
  have hS0_2 : IsPGroup 2 ↥B.S0 := (B.S.isPGroup').to_le B.S0_le
  have hU_inf_S0 : B.U ⊓ B.S0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxU, hxS0⟩
    have hodd : Odd (orderOf x) := by
      have hdvd : orderOf x ∣ Nat.card B.U := Subgroup.orderOf_dvd_natCard B.U hxU
      exact Nat.coprime_two_right.mp
        (Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr (bSetup_U_odd B)))
    obtain ⟨k, hk⟩ := hS0_2 (⟨x, hxS0⟩ : ↥B.S0)
    have hdvd2 : orderOf x ∣ 2 ^ k := by
      have h1 : orderOf (⟨x, hxS0⟩ : ↥B.S0) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
      rwa [Subgroup.orderOf_mk] at h1
    have hone : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr hodd).pow_right k) hdvd2
    exact orderOf_eq_one_iff.mp hone
  -- `S₀ ⊔ ⟨s⟩ = S`
  have hS_eq : B.S0 ⊔ Subgroup.zpowers s = (B.S : Subgroup G) := by
    have hle : B.S0 ⊔ Subgroup.zpowers s ≤ (B.S : Subgroup G) :=
      sup_le B.S0_le (Subgroup.zpowers_le.mpr hsS)
    have hcardS : Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := bSetup_card_S_eq B
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hmul := Subgroup.relIndex_mul_card B.S0 (B.S0 ⊔ Subgroup.zpowers s)
    rw [inf_eq_left.mpr le_sup_left] at hmul
    have hcardle : Nat.card ↥(B.S0 ⊔ Subgroup.zpowers s) ≤ 2 * Nat.card B.S0 := by
      rw [← hcardS]
      exact Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hcpos : 0 < Nat.card B.S0 := by
      haveI : Nonempty ↥B.S0 := ⟨⟨1, B.S0.one_mem⟩⟩
      exact Nat.card_pos
    have hne1 : B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers s) ≠ 1 := by
      intro h1
      have h2 : B.S0 ⊔ Subgroup.zpowers s ≤ B.S0 := Subgroup.relIndex_eq_one.mp h1
      exact hs0 (h2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
    have hle2 : B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers s) ≤ 2 := by
      have h2 : B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers s) * Nat.card B.S0
          ≤ 2 * Nat.card B.S0 := by
        rw [hmul]; exact hcardle
      exact Nat.le_of_mul_le_mul_right h2 hcpos
    have hrpos : B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers s) ≠ 0 := by
      intro h0
      have hTne : Nat.card ↥(B.S0 ⊔ Subgroup.zpowers s) ≠ 0 := by
        haveI : Nonempty ↥(B.S0 ⊔ Subgroup.zpowers s) :=
          ⟨⟨1, Subgroup.mem_sup_left B.S0.one_mem⟩⟩
        exact (Nat.card_ne_zero (α := ↥(B.S0 ⊔ Subgroup.zpowers s))).mpr
          ⟨inferInstance, inferInstance⟩
      apply hTne
      rw [← hmul, h0, zero_mul]
    have hr : B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers s) = 2 := by omega
    rw [hcardS, ← hmul, hr]
  -- `H = U ⊔ S`
  have hcomm_St : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := by
    intro x hx
    have hxb := bSetup_S_le_H B hx
    rw [Subgroup.mem_centralizer_iff] at hxb
    exact (hxb B.t (by simp)).symm
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H :=
    T.split G B.S n hn2 hD B.t (B.S0_le B.t_mem) B.t_order hcomm_St
  have hUS_le_H : B.U ≤ B.H := bSetup_U_le_H B
  have hUnorm : (B.U.subgroupOf B.H).Normal := oddCoreIn_subgroupOf_normal B.H
  -- `s` inverts `K = U ⊔ S₀`
  have hinv : Work.GW2.Inverts s (B.U ⊔ B.S0) := by
    intro x hx
    obtain ⟨u, hu, g, hg, hug⟩ := exists_mul_eq_of_mem_sup_of_comm hcomm_elem hx
    have h2 : (u * g)⁻¹ = g⁻¹ * u⁻¹ := mul_inv_rev u g
    rw [← hug, h2]
    have h1 : s * (u * g) * s⁻¹ = (s * u * s⁻¹) * (s * g * s⁻¹) := by group
    rw [h1, hU_inv u hu, hS0_inv g hg]
    simpa using (mul_comm' (⟨u⁻¹, (B.U ⊔ B.S0).inv_mem (Subgroup.mem_sup_left hu)⟩ :
      ↥(B.U ⊔ B.S0)) ⟨g⁻¹, (B.U ⊔ B.S0).inv_mem (Subgroup.mem_sup_right hg)⟩)
  -- witness that `t` centralizes `s`
  have hts : s * B.t = B.t * s := hcomm_St s hsS
  -- `K ⊓ C(s) = ⟨t⟩`
  have hBt_cent : B.t ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hts
  have hinf : (B.U ⊔ B.S0) ⊓ Subgroup.centralizer ({s} : Set G) = Subgroup.zpowers B.t := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxK, hxCs⟩ := Subgroup.mem_inf.mp hx
      have hx2 : x ^ 2 = 1 := by
        have h1 : s * x * s⁻¹ = x⁻¹ := hinv x hxK
        have h2 : s * x = x * s := (Subgroup.mem_centralizer_iff.mp hxCs) s (by simp)
        have h3 : s * x * s⁻¹ = x := by rw [h2]; group
        have hxx : x⁻¹ = x := by rw [← h1, h3]
        have h4 : x ^ 2 = x * x⁻¹ := by rw [pow_two, hxx]
        rw [h4, mul_inv_cancel]
      rcases eq_one_or_eq_of_sq_eq_one_of_comm_sup B.U B.S0 hcomm_elem (bSetup_U_odd B)
        hU_inf_S0 B.S0_cyclic B.t_mem B.t_order x hxK hx2 with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right B.t_mem, hBt_cent⟩
  -- `s ∉ K`
  have hsK : s ∉ B.U ⊔ B.S0 := by
    intro hsK'
    have hsCs : s ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; rfl
    have hmem : s ∈ (B.U ⊔ B.S0) ⊓ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hsK', hsCs⟩
    rw [hinf] at hmem
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two B.t_order hmem with h | h
    · rw [h, orderOf_one] at hsord
      exact absurd hsord (by norm_num)
    · rw [h] at hs0; exact hs0 B.t_mem
  -- TI
  have hTI : ∀ g : G, g ∉ Subgroup.centralizer ({B.t} : Set G) →
      (B.U ⊔ B.S0) ⊓ conjSub g (B.U ⊔ B.S0) = ⊥ := by
    intro g hg
    rw [Subgroup.eq_bot_iff_forall]
    rintro y hy
    obtain ⟨hyK, hyKg⟩ := Subgroup.mem_inf.mp hy
    by_contra hyne
    rcases eq_or_ne (orderOf y % 2) 0 with heven_mod | hodd_mod
    · have heven : Even (orderOf y) := by
        rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]; exact heven_mod
      obtain ⟨k, hk⟩ := heven
      have hordne : orderOf y ≠ 0 := by
        intro h0
        have hd : 0 ∣ Nat.card G := by rw [← h0]; exact orderOf_dvd_natCard y
        have hne : Nat.card G ≠ 0 :=
          (Nat.card_ne_zero (α := G)).mpr ⟨⟨1⟩, inferInstance⟩
        exact hne (Nat.zero_dvd.mp hd)
      have hkpos : 0 < k := by
        have : 0 < orderOf y := Nat.pos_of_ne_zero hordne
        omega
      have hk2 : k * 2 = orderOf y := by omega
      have hz2 : (y ^ k) ^ 2 = 1 := by
        rw [← pow_mul, hk2, pow_orderOf_eq_one]
      have hzne : y ^ k ≠ 1 := by
        intro h1
        have hdvd : orderOf y ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
        exact absurd (Nat.le_of_dvd hkpos hdvd) (by omega)
      have hzK : y ^ k ∈ B.U ⊔ B.S0 := (B.U ⊔ B.S0).pow_mem hyK k
      have hzt : y ^ k = B.t := by
        rcases eq_one_or_eq_of_sq_eq_one_of_comm_sup B.U B.S0 hcomm_elem (bSetup_U_odd B)
          hU_inf_S0 B.S0_cyclic B.t_mem B.t_order (y ^ k) hzK hz2 with h | h
        · exact absurd h hzne
        · exact h
      have hzKg : y ^ k ∈ conjSub g (B.U ⊔ B.S0) := (conjSub g (B.U ⊔ B.S0)).pow_mem hyKg k
      have hzg' : g⁻¹ * (y ^ k) * g ∈ B.U ⊔ B.S0 := mem_conjSub_iff.mp hzKg
      have hzg'2 : (g⁻¹ * (y ^ k) * g) ^ 2 = 1 := by
        have hord : orderOf (g⁻¹ * (y ^ k) * g) = orderOf (y ^ k) := by
          have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective (y ^ k)
          simpa [MulAut.conj_apply] using h
        have h2 : orderOf (g⁻¹ * (y ^ k) * g) = 2 := by
          rw [hord]
          have hd : orderOf (y ^ k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h3 | h3
          · exact absurd (orderOf_eq_one_iff.mp h3) hzne
          · exact h3
        rw [← h2, pow_orderOf_eq_one]
      have hzg't : g⁻¹ * (y ^ k) * g = B.t := by
        rcases eq_one_or_eq_of_sq_eq_one_of_comm_sup B.U B.S0 hcomm_elem (bSetup_U_odd B)
          hU_inf_S0 B.S0_cyclic B.t_mem B.t_order (g⁻¹ * (y ^ k) * g) hzg' hzg'2 with h | h
        · exfalso
          have h1 : y ^ k = 1 := by
            have h2 := congrArg (fun z => g * z * g⁻¹) h
            simpa [mul_assoc] using h2
          exact hzne h1
        · exact h
      have hconjgt : g⁻¹ * B.t * g = B.t := hzt ▸ hzg't
      have hgc : B.t * g = g * B.t := by
        have h2 := congrArg (fun z => g * z) hconjgt
        rw [show g * (g⁻¹ * B.t * g) = B.t * g from by group] at h2
        exact h2
      exact hg (by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hgc)
    · have hodd : Odd (orderOf y) := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
        exact hodd_mod
      have hyU : y ∈ B.U :=
        mem_left_of_odd_orderOf_of_comm_sup B.U B.S0 hcomm_elem hU_inf_S0 hS0_2 hyK hodd
      have hyKgK : g⁻¹ * y * g ∈ B.U ⊔ B.S0 := mem_conjSub_iff.mp hyKg
      have hodd' : Odd (orderOf (g⁻¹ * y * g)) := by
        have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
        have h1 : orderOf (g⁻¹ * y * g) = orderOf y := by
          simpa [MulAut.conj_apply] using h
        rw [h1]; exact hodd
      have hyU' : g⁻¹ * y * g ∈ B.U :=
        mem_left_of_odd_orderOf_of_comm_sup B.U B.S0 hcomm_elem hU_inf_S0 hS0_2 hyKgK hodd'
      have hy_convU : y ∈ conjSub g B.U := mem_conjSub_iff.mpr hyU'
      have hXU : Subgroup.zpowers y ≤ B.U := Subgroup.zpowers_le.mpr hyU
      have hXne : Subgroup.zpowers y ≠ ⊥ := by
        intro hb
        have : y ∈ (⊥ : Subgroup G) := hb ▸ Subgroup.mem_zpowers y
        exact hyne (by simpa using this)
      have hKg_le_H : conjSub g (B.U ⊔ B.S0) ≤ B.H := by
        haveI : IsMulCommutative ↥(B.U ⊔ B.S0) := hK_comm
        haveI : IsMulCommutative ↥(conjSub g (B.U ⊔ B.S0)) :=
          isMulCommutative_of_mulEquiv (Subgroup.equivMapOfInjective (B.U ⊔ B.S0)
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
        have hXKg : Subgroup.zpowers y ≤ conjSub g (B.U ⊔ B.S0) := Subgroup.zpowers_le.mpr hyKg
        have hcomm_vw : ∀ v ∈ conjSub g (B.U ⊔ B.S0),
            ∀ w ∈ (Subgroup.zpowers y : Subgroup G), v * w * v⁻¹ = w := by
          intro v hv w hw
          have hwK := hXKg hw
          have hvw : v * w = w * v := by
            have hcv := congrArg Subtype.val (mul_comm'
              (⟨v, hv⟩ : ↥(conjSub g (B.U ⊔ B.S0))) ⟨w, hwK⟩)
            simpa using hcv
          rw [hvw]; group
        have hN : conjSub g (B.U ⊔ B.S0) ≤
            Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
          intro v hv
          rw [Subgroup.mem_normalizer_iff]
          intro w
          constructor
          · intro hw; rw [hcomm_vw v hv w hw]; exact hw
          · intro hw
            have hv' : v⁻¹ ∈ conjSub g (B.U ⊔ B.S0) := (conjSub g (B.U ⊔ B.S0)).inv_mem hv
            have h := hcomm_vw v⁻¹ hv' (v * w * v⁻¹) hw
            have heq : v⁻¹ * (v * w * v⁻¹) * (v⁻¹)⁻¹ = w := by group
            rw [heq] at h
            rw [h]; exact hw
        exact le_trans hN (hNX (Subgroup.zpowers y) hXne hXU)
      have hUg_le_U : conjSub g B.U ≤ B.U := by
        intro w hw
        have hwH : w ∈ B.H := hKg_le_H (conjSub_mono le_sup_left g hw)
        have hmem : g⁻¹ * w * g ∈ B.U := mem_conjSub_iff.mp hw
        have hoddw : Odd (orderOf w) := by
          have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective w
          have h1 : orderOf (g⁻¹ * w * g) = orderOf w := by
            simpa [MulAut.conj_apply] using h
          have h2 : Odd (orderOf (g⁻¹ * w * g)) :=
            Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_left
              (Subgroup.orderOf_dvd_natCard B.U hmem)
              (Nat.coprime_two_right.mpr (bSetup_U_odd B)))
          rwa [h1] at h2
        exact mem_of_odd_orderOf_of_sup_normal B.H B.U (B.S : Subgroup G) hUS_le_H
          (bSetup_S_le_H B) hsplit hUnorm B.S.isPGroup' hwH hoddw
      have hUg_eq : conjSub g B.U = B.U :=
        Subgroup.eq_of_le_of_card_ge hUg_le_U (le_of_eq (card_conjSub g B.U).symm)
      have hyUmem : y ∈ B.U := hUg_eq ▸ hy_convU
      have hUne : B.U ≠ ⊥ := by
        intro hbot
        rw [hbot] at hyUmem
        exact hyne (by simpa using hyUmem)
      have hgN : g ∈ Subgroup.normalizer (B.U : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          have hm : (MulAut.conj g) h ∈ conjSub g B.U := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
          rw [hUg_eq] at hm
          simpa [MulAut.conj_apply] using hm
        · intro hh
          have hm : (MulAut.conj g) h ∈ conjSub g B.U := by
            rw [hUg_eq]; simpa [MulAut.conj_apply] using hh
          obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp hm
          have hzh : z = h := (MulAut.conj g).injective hze
          rw [hzh] at hz
          exact hz
      exact hg (hNX B.U hUne le_rfl hgN)
  -- centralizer
  have hcent : B.H = (B.U ⊔ B.S0) ⊔ Subgroup.zpowers s := by
    rw [← hsplit, ← hS_eq, sup_assoc]
  -- one class of involutions
  have hconj : ∀ x : G, orderOf x = 2 → IsConj x B.t := by
    intro x hx
    exact (T.fus G B.S n hn2 hD (no_normal_index_two_of_simple_nonab hctx.nonab)).1 x B.t hx
      B.t_order
  exact ⟨B.t_order, hsord, Subgroup.mem_sup_right B.t_mem, hsK, hK_comm, hcent, hinv, hinf,
    hTI, hconj⟩

end Work.CORE2A
