import Mathlib
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.Step3.Defs
import Submission.Work.Hering.Step4.perm_eq_one_of_card_three
import Submission.Work.Hering.Step4.mem_zpowers_of_commute_of_card_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step4

open LeanEval.GroupTheory.Defs Work.Hering
open Work.Hering.Step3

/-- The type of involutions of `G`, carrying the conjugation action of `G`
(`Work.Hering.Step3.instMulActionInvolutions`).  Private, to avoid clashing with
neighbouring files of the area. -/
private abbrev InvSet (G : Type*) [Group G] : Type _ := {x : G // x ∈ involutions G}

/-! ## The involution set of `G` has three elements when `|V| = 4` -/

/-- `V = Inv(G) ∪ {1}` has cardinality `4`, so `G` has exactly three involutions. -/
theorem card_involutions_eq_three {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G} (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    Nat.card {x : G // x ∈ involutions G} = 3 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have e : {x : G // x ∈ involutions G} ≃ {x : ↥(invSubgroup hDT h4) // x ≠ 1} :=
  { toFun := fun x =>
      ⟨⟨x.1, (mem_invSubgroup hDT h4).2 (Or.inl x.2)⟩,
        fun h => ne_one_of_mem_involutions x.2 ((Subgroup.mk_eq_one _).1 h)⟩
    invFun := fun y =>
      ⟨(y.1 : G), orderOf_eq_two_of_sq_eq_one
        (pow_two_eq_one_of_mem_invSubgroup hDT h4 y.1.2) (by simpa using y.2)⟩
    left_inv := fun x => Subtype.ext rfl
    right_inv := fun y => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : ↥(invSubgroup hDT h4) => x = 1),
      Fintype.card_subtype_eq (1 : ↥(invSubgroup hDT h4))]
  have hV' : Fintype.card ↥(invSubgroup hDT h4) = 4 := by
    rw [Nat.card_eq_fintype_card] at hV
    exact hV
  omega

/-- If `V = invSubgroup hDT h4` has cardinality `4` and `C_G(V)` is a 2-group, then every element
`z` of order `3` has `|C_G(z)| = 3`: `z` acts on `V` by a 3-cycle, so `C_G(z)` contains no
involution, hence has odd order, and that order divides `|G| = 6 * |C_G(V)|`. -/
theorem centralizer_card_three {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G}
    (hC : ∀ U : Subgroup G, U ≤ invSubgroup hDT h4 → Nat.card U = 4 →
      IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)))
    (hV : Nat.card ↥(invSubgroup hDT h4) = 4) {z : G} (hz : orderOf z = 3) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 3 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set H : Subgroup G := Subgroup.centralizer ({z} : Set G) with hHdef
  have memH : ∀ t : G, t ∈ H ↔ z * t = t * z := by
    intro t
    rw [hHdef, Subgroup.mem_centralizer_iff]
    constructor
    · intro h; exact h z rfl
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  -- `C_G(V)` is a 2-group, so `z ∉ C_G(V)`
  have hzC : z ∉ Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G) := by
    intro hzC
    have hCV :
        IsPGroup 2 ↥(Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G)) :=
      hC (invSubgroup hDT h4) le_rfl hV
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hCV
    have hdvd :
        orderOf (⟨z, hzC⟩ :
            ↥(Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G))) ∣
          Nat.card ↥(Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G)) := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact pow_card_eq_one'
    rw [hn, Subgroup.orderOf_mk, hz] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  -- the conjugation action of `G` on its involutions
  set ρ : G →* Equiv.Perm (InvSet G) := MulAction.toPermHom G (InvSet G) with hρdef
  have hρ_apply : ∀ (g : G) (x : InvSet G), ρ g x = g • x := by
    intro g x
    rw [hρdef, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  have hcardX : Fintype.card (InvSet G) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_involutions_eq_three hV
  have hρz_pow : ρ z ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  have hρz_ne : ρ z ≠ 1 := by
    intro h
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases eq_or_ne y 1 with rfl | hy1
    · simp
    · have hy2 : y ∈ involutions G :=
        mem_involutions.mpr (((mem_invSubgroup hDT h4).1 hy).resolve_right hy1)
      have hfix : z • (⟨y, hy2⟩ : InvSet G) = ⟨y, hy2⟩ := by
        rw [← hρ_apply z ⟨y, hy2⟩, h]
        rfl
      have hconj : z * y * z⁻¹ = y := by
        have h1 := congrArg (fun (s : InvSet G) => (s : G)) hfix
        simpa only [coe_smul_involutions] using h1
      have hcomm : z * y = y * z := by
        have := congrArg (fun t => t * z) hconj
        simpa [mul_assoc] using this
      exact hcomm.symm
  -- `z` acts on the three involutions without fixed points
  have hnoFix : ∀ x : InvSet G, z • x ≠ x := by
    intro x hx
    have hfix : ρ z x = x := by rw [hρ_apply z x]; exact hx
    exact hρz_ne (perm_eq_one_of_card_three hcardX hρz_pow ⟨x, hfix⟩)
  -- hence `C_G(z) ∩ V = 1`
  have hHV : ∀ x : G, x ∈ H → x ∈ invSubgroup hDT h4 → x = 1 := by
    intro x hxH hxV
    rcases eq_or_ne x 1 with rfl | hx1
    · rfl
    · have hx2 : x ∈ involutions G :=
        mem_involutions.mpr (((mem_invSubgroup hDT h4).1 hxV).resolve_right hx1)
      have hzx : z * x = x * z := (memH x).mp hxH
      have hconj : z * x * z⁻¹ = x := by rw [hzx]; group
      have hsm : z • (⟨x, hx2⟩ : InvSet G) = ⟨x, hx2⟩ := by
        apply Subtype.ext
        simpa only [coe_smul_involutions] using hconj
      exact absurd hsm (hnoFix ⟨x, hx2⟩)
  -- so `C_G(z)` has no element of order two, hence odd order
  have hH_odd : Odd (Nat.card ↥H) := by
    by_contra hodd
    have h2 : 2 ∣ Nat.card ↥H := by
      rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
      exact hodd
    rw [Nat.card_eq_fintype_card] at h2
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 2 h2
    have hu2 : orderOf (u : G) = 2 := by
      rw [Subgroup.orderOf_coe u, hu]
    have huV : (u : G) ∈ invSubgroup hDT h4 := (mem_invSubgroup hDT h4).2 (Or.inl hu2)
    have huH : (u : G) ∈ H := u.2
    have h1 : (u : G) = 1 := hHV (u : G) huH huV
    rw [h1, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  -- the conjugation action restricted to `C_G(z)`
  set f : ↥H →* Equiv.Perm (InvSet G) := ρ.comp H.subtype with hfdef
  have hft : ∀ t : ↥H, f t = ρ (t : G) := by
    intro t
    rw [hfdef]
    rfl
  have hzH : z ∈ H := (memH z).mpr rfl
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    have ht1 : ρ (t : G) = 1 := by
      rw [← hft t]
      exact MonoidHom.mem_ker.mp ht
    -- `t` centralises every involution, hence all of `V`
    have htC : (t : G) ∈ Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases eq_or_ne y 1 with rfl | hy1
      · simp
      · have hy2 : y ∈ involutions G :=
          mem_involutions.mpr (((mem_invSubgroup hDT h4).1 hy).resolve_right hy1)
        have hfix : (t : G) • (⟨y, hy2⟩ : InvSet G) = ⟨y, hy2⟩ := by
          rw [← hρ_apply (t : G) ⟨y, hy2⟩, ht1]
          rfl
        have hconj : (t : G) * y * (t : G)⁻¹ = y := by
          have h1 := congrArg (fun (s : InvSet G) => (s : G)) hfix
          simpa only [coe_smul_involutions] using h1
        have hcomm : (t : G) * y = y * (t : G) := by
          have := congrArg (fun s => s * (t : G)) hconj
          simpa [mul_assoc] using this
        exact hcomm.symm
    -- the order of `t` divides both `|C_G(V)| = 2 ^ n` and the odd number `|C_G(z)|`
    have hCV :
        IsPGroup 2 ↥(Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G)) :=
      hC (invSubgroup hDT h4) le_rfl hV
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hCV
    have hdvd1 : orderOf t ∣ 2 ^ n := by
      have hle :
          orderOf (⟨(t : G), htC⟩ :
              ↥(Subgroup.centralizer ((invSubgroup hDT h4 : Subgroup G) : Set G))) ∣
            Nat.card ↥(Subgroup.centralizer
              ((invSubgroup hDT h4 : Subgroup G) : Set G)) := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact pow_card_eq_one'
      rw [hn, Subgroup.orderOf_mk (t : G) htC, Subgroup.orderOf_coe t] at hle
      exact hle
    have hdvd2 : orderOf t ∣ Nat.card ↥H := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact pow_card_eq_one'
    have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥H) :=
      (Nat.coprime_two_left.mpr hH_odd).pow_left n
    have hone : orderOf t ∣ 1 := by
      have := Nat.dvd_gcd hdvd1 hdvd2
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  -- the image of `C_G(z)` is the group generated by `ρ z`
  have hrange : f.range = Subgroup.zpowers (ρ z) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨t, rfl⟩
      have hc : Commute (ρ (t : G)) (ρ z) := by
        have hcz : Commute ((t : ↥H) : G) z := ((memH (t : G)).mp t.2).symm
        exact hcz.map ρ
      rw [hft]
      exact mem_zpowers_of_commute_of_card_three hcardX hρz_pow hρz_ne hc
    · rw [Subgroup.zpowers_le, hfdef]
      exact ⟨⟨z, hzH⟩, rfl⟩
  have hrange_card : Nat.card ↥f.range = 3 := by
    rw [hrange, Nat.card_zpowers, orderOf_eq_prime hρz_pow hρz_ne]
  -- first isomorphism theorem
  have hmul := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at hmul
  rw [hker, Subgroup.card_bot (G := ↥H), hrange_card, one_mul] at hmul
  exact hmul.symm

end Work.Hering.Step4
