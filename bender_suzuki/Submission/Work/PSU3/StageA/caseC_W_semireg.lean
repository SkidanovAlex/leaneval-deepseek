import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.chVI_prop
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.Layers.card_dvd_card_sub_one_of_map_xi_eq
import Submission.Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThreePoints.involutions_commute_of_below
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.Higman.typeB
import Submission.Work.Higman.Layers.card_dvd_card_sub_one_of_map_xi_eq
import Submission.Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseC_W_semireg`

Case c) of Peterfalvi II, Ch. VI §1: `|Q| = q³` (`q = |Q₀| = |Inv(H)| + 1`).  The group
`W = C_V(K) = D ⊓ C_G(Inv H)` acts **semiregularly** on `Q/Q₀`:

> for `w ∈ W`, `w ≠ 1`, and `x ∈ Q` with `w x = x w` one has `x ∈ Q₀ = Q0sub H`.

Route (avoiding the classification of `F/Z(F)` of Ch. V §2 Lemma 2 c):

* WLOG `W ≠ ⊥`.  Then `K = Ksub H t = Kset H t` is cyclic (`Ksub_eq_Kset_of_W_ne_bot`) and acts
  on `Q`; writing `q = |Q₀|`, the pair `(Q, [K])` is a Suzuki 2-group of order `q³`, and
  `Z(Q) = Ω₁(Q) = Q₀` (Higman), `|Q| = |Z(Q)|³`, `K#` acts fixed-point-freely on `Q`.
* `Q` is not abelian: otherwise `W` centralizes `Q`, hence lies in `C_D(Q) = 1`.
* Let `w ∈ W#` and let `A` be the conjugation by `w` on `↥Q`; `A` has odd order, commutes with
  the cyclic `ξ` generating the `K`-action and fixes `Z(Q)` pointwise.  Put `C = C_Q(A)`;
  `C` is `ξ`-invariant, so `q - 1 ∣ |C| - 1`, and `|C| ∈ {q, q², q³}`.  `|C| = q³` forces
  `A = 1` (i.e. `w ∈ C_D(Q) = 1`) and `|C| = q²` is excluded by the cocycle
  `θ(x) = A(x) x⁻¹` (`A` has odd order, `Q` has class 2).  Hence `C = Z(Q) = Q₀`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

namespace Work.PSU3.StageA

open Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## §1. `Kset H t` is transitive on the involutions of `H` -/

/-- `K = Kset H t` is transitive on `Inv(H)`: Peterfalvi I, Ch. I §2 Prop. 2 (b) with the
witness taken in `K` (the proof of `Work.ThmF.Bender.DTransitiveInv` exhibits it there). -/
theorem Kset_transitive_involutions (hH : IsStronglyEmbedded H) (ht2 : orderOf t = 2)
    (htH : t ∉ H) :
    ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ k ∈ Kset H t, k * a * k⁻¹ = b := by
  intro a ha b hb
  have hcard : (Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hH ht2 htH
  have hmaps : ∀ x ∈ Kset H t, x * a * x⁻¹ ∈ involutions (H : Set G) := by
    intro x hx
    have hxH : x ∈ H := (Work.Models.mem_twoPoint_iff.mp (Kset_subset H t hx)).1
    exact ⟨H.mul_mem (H.mul_mem hxH ha.1) (H.inv_mem hxH),
      by rw [Work.ThmF.Bender.orderOf_conj_eq, ha.2]⟩
  have hinj : Set.InjOn (fun x => x * a * x⁻¹) (Kset H t) :=
    Work.ThmF.Bender.Kset_conj_injective hH ht2 htH ha.1 ha.2
  have himg : ((fun x => x * a * x⁻¹) '' (Kset H t)).ncard
      = (involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hcard]
  have hsub : (fun x => x * a * x⁻¹) '' (Kset H t) ⊆ involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps x hx
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq himg.symm)
  have hb' : b ∈ (fun x => x * a * x⁻¹) '' (Kset H t) := by rw [heq]; exact hb
  obtain ⟨k, hk, hkb⟩ := hb'
  exact ⟨k, hk, hkb⟩

/-! ## §2. Elementary facts about `H = Q ⋊ D` -/

section Split

variable (h : IsSplitRankOne H Q t)

include h

/-- Every involution of `H` lies in `Q` (since `H/Q ≅ D` has odd order). -/
theorem inv_mem_Q : ∀ u ∈ involutions (H : Set G), u ∈ Q := by
  intro u hu
  haveI : (Q.subgroupOf H).Normal := Work.ThmF.split_Q_normal_in_H h
  have hQHindex : (Q.subgroupOf H).index = Nat.card ↥(twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
    rw [h1, Work.ThmF.split_card_H h] at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  have hu2 : orderOf (⟨u, hu.1⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hu.2
  have hmem : (⟨u, hu.1⟩ : ↥H) ∈ Q.subgroupOf H :=
    Work.ThreePoints.mem_of_orderOf_eq_two_of_odd_index
      (L := Q.subgroupOf H) (by rw [hQHindex]; exact Work.ThmF.split_odd_card_twoPoint h) hu2
  exact Subgroup.mem_subgroupOf.mp hmem

/-- The involutions of `H` and of `Q` coincide (as subsets of `G`). -/
theorem involutions_H_eq_Q :
    involutions (H : Set G) = involutions (Q : Set G) := by
  ext u
  constructor
  · intro hu
    exact ⟨inv_mem_Q h u hu, hu.2⟩
  · intro hu
    exact ⟨h.le hu.1, hu.2⟩

end Split

/-! ## §3. The elementary abelian group `Q₀ = Q0sub H` and the centre of `Q` -/

/-- The involutions of `H` commute with each other (Peterfalvi II, Ch. V §1 Prop. 1 (c)). -/
theorem involutions_H_commute (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
  intro u hu v hv
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hDtr : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
  have hnil : Group.IsNilpotent ↥Q := hS.two.isNilpotent
  have hcent := Work.ThmF.ChV12.prop1c hS.situation H Q t hsplit hDtr hnil
  have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcent u hu)
  have h2 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcent v hv)
  exact h1.2 v h2.1

/-- `Q₀ = Q0sub H` is elementary abelian, normal in `H`, and its non-identity elements are
exactly the involutions of `H`. -/
theorem Q0sub_structure (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    (∀ x ∈ Work.ThmF.Q0sub H, x * x = 1) ∧
    (∀ x ∈ Work.ThmF.Q0sub H, ∀ y ∈ Work.ThmF.Q0sub H, x * y = y * x) ∧
    (∀ h ∈ H, ∀ x ∈ Work.ThmF.Q0sub H, h * x * h⁻¹ ∈ Work.ThmF.Q0sub H) ∧
    (∀ x ∈ Work.ThmF.Q0sub H, x ≠ 1 → x ∈ involutions (H : Set G)) :=
  Work.ThmF.ChV12.Q0sub_elementary H (involutions_H_commute hS hC4)

/-- `Q₀ = Q0sub H` consists of elements of order `≤ 2`, so it is a `2`-group. -/
theorem Q0sub_isPGroup (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) : IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
  intro x
  have hx2 : ((x : ↥(Work.ThmF.Q0sub H)) : G) ^ 2 = 1 := by
    rw [pow_two]; exact (Q0sub_structure hS hC4).1 x x.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  simpa using hx2

/-- The order of `Q₀` is a power of `2`. -/
theorem exists_card_Q0sub_eq_two_pow (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∃ n : ℕ, Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n :=
  (Q0sub_isPGroup hS hC4).exists_card_eq

/-- `Q₀ ≤ C_Q(Q)`: the involutions of `H` are central in `Q`. -/
theorem Q0sub_le_centerOf (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    Work.ThmF.Q0sub H ≤ Work.ThmF.centerOf Q := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hDtr : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
  have hnil : Group.IsNilpotent ↥Q := hS.two.isNilpotent
  have hcent := Work.ThmF.ChV12.prop1c hS.situation H Q t hsplit hDtr hnil
  rw [Work.ThmF.Q0sub]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases Work.ThmF.mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
  · exact hcent x ⟨hxH, hx2⟩
  · exact (Work.ThmF.centerOf Q).one_mem

/-- `W ≤ C_G(Q₀)`: `W = C_V(K) = D ⊓ C_G(Inv H)` centralises `Q₀` (Ch. II §4 Prop. 4). -/
theorem W_le_centralizer_Q0sub (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    Work.ThmF.W H t ≤ Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hW : Work.ThmF.W H t =
      twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) :=
    (hC4 G hS.situation H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.2.2.2.1
  intro w hw
  rw [hW] at hw
  have hwc : w ∈ Subgroup.centralizer (involutions (H : Set G)) := (Subgroup.mem_inf.mp hw).2
  have hwc' : ∀ x ∈ involutions (H : Set G), x * w = w * x :=
    fun x hx => Subgroup.mem_centralizer_iff.mp hwc x hx
  have hle : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Work.ThmF.Q0sub]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases Work.ThmF.mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hwc' x ⟨hxH, hx2⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
  exact Subgroup.mem_centralizer_iff.mpr
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx))

/-- `D` acts faithfully on `Q`: an element of `D = H ∩ H^t` centralising `Q` is trivial
(Peterfalvi II, Ch. V §2 Lemma 1 (c): `𝒩(G) = C_D(Q)`, and `𝒩(G) = 1` as `G` is simple). -/
theorem eq_one_of_centralizes_Q (hS : Work.PSU3.PSU3Hyp H Q t) {d : G}
    (hd : d ∈ twoPoint H t) (hdc : ∀ q ∈ Q, d * q = q * d) : d = 1 := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  haveI : IsSimpleGroup G := hS.simple
  -- the distinguished involution `s` of the structure identity
  obtain ⟨⟨s, r⟩, ⟨hsQ, hs2, hrQ, hsr⟩, -⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
  -- `t * t = 1`, so the structure identity can be put in the form `t s t = (r⁻¹)⁻¹ t r⁻¹`
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [hsplit.invol] at h; simpa [pow_two] using h
  have hsr' : t * s * t = (r⁻¹)⁻¹ * t * r⁻¹ := by
    rw [inv_inv]
    have h1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    simpa [h1] using hsr
  have hV := centD_eq_centralizer_s hS hsQ hs2 (Q.inv_mem hrQ) hsr'
  -- `d` centralises `s ∈ Q`, hence lies in `V = C_D(s)`, hence commutes with `t`
  have hds : d ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hdc s hsQ)
  have hdD : d ∈ centD H t := by
    rw [hV]; exact Subgroup.mem_inf.mpr ⟨hd, hds⟩
  have hdt : t * d = d * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdD).2).symm
  -- `d` centralises `Q` and `t`, and `⟨Q, t⟩ = ⊤`
  have htop : Subgroup.closure ((Q : Set G) ∪ {t}) = ⊤ :=
    Work.RankOneUniqueness.closure_Q_t_eq_top hsplit
  have hcent : d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [← htop]
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with hy | hy
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hdc y hy).symm
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr hdt
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  -- the centre of a simple group with a proper strongly embedded subgroup of even order is trivial
  have hZbot : Subgroup.center G = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple (Subgroup.center G) (inferInstance) with h | h
    · exact h
    · exfalso
      have hHcenter : H ≤ Subgroup.center G := by rw [h]; exact le_top
      have hHnorm : H.Normal := ⟨fun a ha b => by
        have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact ha⟩
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple H hHnorm with hb | ht
      · have heven : Even (Nat.card H) := hsplit.stronglyEmbedded.2.1
        rw [hb, Subgroup.card_bot] at heven
        exact absurd heven (by norm_num)
      · exact hsplit.stronglyEmbedded.1 ht
  rw [hZbot] at hcent
  exact Subgroup.mem_bot.mp hcent

/-! ## §4. The conjugation action of `N_G(Q)` on `Q`, and `Q` as a Suzuki 2-group -/

/-- Conjugation by an element of `N_G(Q)`, as an automorphism of `↥Q`. -/
noncomputable def cwConj (Q : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (Q : Set G)) :
    MulAut ↥Q where
  toFun x := ⟨k * (x : G) * k⁻¹, (Subgroup.mem_normalizer_iff.mp hk (x : G)).mp x.2⟩
  invFun x := ⟨k⁻¹ * (x : G) * (k⁻¹)⁻¹,
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set G)).inv_mem hk) (x : G)).mp x.2⟩
  left_inv x := by apply Subtype.ext; group
  right_inv x := by apply Subtype.ext; group
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem cwConj_apply (Q : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (Q : Set G))
    (x : ↥Q) : ((cwConj Q k hk x : ↥Q) : G) = k * (x : G) * k⁻¹ := rfl

theorem cwConj_pow_apply (Q : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (Q : Set G))
    (n : ℕ) (x : ↥Q) :
    (((cwConj Q k hk) ^ n) x : G) = k ^ n * (x : G) * (k ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((cwConj Q k hk) ^ (n + 1)) x = (cwConj Q k hk) (((cwConj Q k hk) ^ n) x) := by
      rw [pow_succ', MulAut.mul_apply]
    rw [h1, cwConj_apply, ih, pow_succ', mul_inv_rev]
    group

theorem cwConj_eq_one_iff (Q : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (Q : Set G)) :
    cwConj Q k hk = 1 ↔ ∀ x : ↥Q, k * (x : G) * k⁻¹ = (x : G) := by
  constructor
  · intro h x
    have hx := congrArg (fun f : MulAut ↥Q => ((f x : ↥Q) : G)) h
    simpa [cwConj_apply] using hx
  · intro h
    ext x
    rw [cwConj_apply]
    simpa using h x

section Suzuki

variable (hS : Work.PSU3.PSU3Hyp H Q t)

include hS

/-- `K = Ksub H t` is a subgroup of `N_G(Q)`. -/
theorem Ksub_le_normalizer : Work.ThmF.Ksub H t ≤ Subgroup.normalizer (Q : Set G) :=
  (Work.ThmF.ChV12.Ksub_le_H H t).trans hS.split.normal

/-- `K = Ksub H t ⊆ D = twoPoint H t`. -/
theorem Ksub_le_twoPoint : Work.ThmF.Ksub H t ≤ twoPoint H t :=
  (Subgroup.closure_le _).mpr (Work.ThmF.Kset_subset H t)

end Suzuki

section Suzuki2

variable (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)

include hS hC4

/-- `Q₀ = Q0sub H = {1} ∪ Inv(H)` as subsets of `G`. -/
theorem Q0sub_eq_insert :
    (Work.ThmF.Q0sub H : Set G) = insert 1 (involutions (H : Set G)) := by
  ext x
  constructor
  · intro hx
    rcases eq_or_ne x 1 with rfl | hx1
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact Set.mem_insert_iff.mpr (Or.inr ((Q0sub_structure hS hC4).2.2.2 x hx hx1))
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (Work.ThmF.Q0sub H).one_mem
    · exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hx.1, hx.2⟩))

/-- `|Q₀| = |Inv(H)| + 1`. -/
theorem card_Q0sub_eq :
    Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 := by
  have h0 : Nat.card ↥(Work.ThmF.Q0sub H) = (Work.ThmF.Q0sub H : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h1 : (1 : G) ∉ involutions (H : Set G) := by
    rintro ⟨-, h⟩
    simp at h
  rw [h0, Q0sub_eq_insert hS hC4, Set.ncard_insert_of_notMem h1]

/-- `|K| = |Q₀| - 1` in case `c)` (`K = J(D,t)` has `|Inv(H)| = q - 1` elements). -/
theorem card_Ksub_eq (hW : Work.ThmF.W H t ≠ ⊥) :
    Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
  have hKset := (Ksub_eq_Kset_of_W_ne_bot hS hC4 hW).1
  have h1 : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
    have h0 : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Ksub H t : Set G).ncard :=
      Nat.card_coe_set_eq _
    rw [h0, hKset]
  have h2 : (Work.ThmF.Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hS.split.stronglyEmbedded hS.split.invol hS.split.not_mem
  rw [h1, h2, card_Q0sub_eq hS hC4]
  omega

end Suzuki2

section Gen

variable (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hW : Work.ThmF.W H t ≠ ⊥)

include hS hC4 hW

/-- A generator of `K`, viewed in `G`, together with `K = ⟨k⟩`. -/
theorem exists_generator_Ksub :
    ∃ k : G, k ∈ Work.ThmF.Ksub H t ∧ Subgroup.zpowers k = Work.ThmF.Ksub H t := by
  haveI hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t) := (Ksub_eq_Kset_of_W_ne_bot hS hC4 hW).2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Work.ThmF.Ksub H t))
  refine ⟨(g : G), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact (Work.ThmF.Ksub H t).zpow_mem g.2 n
  · intro hx
    have h1 : (⟨x, hx⟩ : ↥(Work.ThmF.Ksub H t)) ∈ Subgroup.zpowers g := hg ⟨x, hx⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩

/-- `|K| = orderOf k` for a generator `k` of `K`. -/
theorem orderOf_generator {k : G} (hkK : k ∈ Work.ThmF.Ksub H t)
    (hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t) :
    orderOf k = Nat.card ↥(Work.ThmF.Ksub H t) := by
  have h1 : orderOf (⟨k, hkK⟩ : ↥(Work.ThmF.Ksub H t)) = Nat.card ↥(Work.ThmF.Ksub H t) := by
    refine orderOf_eq_card_of_zpowers_eq_top ?_
    ext y
    constructor
    · intro _; trivial
    · intro _
      have hy : (y : G) ∈ Subgroup.zpowers k := by rw [hkgen]; exact y.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [← h1]
  exact Subgroup.orderOf_coe (⟨k, hkK⟩ : ↥(Work.ThmF.Ksub H t))

/-- `orderOf (cwConj k) = |Q₀| - 1` for a generator `k` of `K`. -/
theorem orderOf_conjQ {k : G} (hkK : k ∈ Work.ThmF.Ksub H t)
    (hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t) :
    orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))
      = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
  have hkm : k ^ (Nat.card ↥(Work.ThmF.Ksub H t)) = 1 := by
    rw [← orderOf_generator hS hC4 hW hkK hkgen]
    exact pow_orderOf_eq_one k
  have hdvd1 : orderOf (cwConj Q k (Ksub_le_normalizer hS hkK)) ∣ Nat.card ↥(Work.ThmF.Ksub H t) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    ext x
    rw [cwConj_pow_apply, hkm]
    simp
  have hdvd2 : Nat.card ↥(Work.ThmF.Ksub H t) ∣ orderOf (cwConj Q k (Ksub_le_normalizer hS hkK)) := by
    have hfix : ∀ x ∈ Q,
        k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))) * x *
          (k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))))⁻¹ = x := by
      intro x hx
      have h1 : ((cwConj Q k (Ksub_le_normalizer hS hkK)) ^
          orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))) ⟨x, hx⟩
          = (1 : MulAut ↥Q) ⟨x, hx⟩ := by rw [pow_orderOf_eq_one]
      have h2 := congrArg (fun z : ↥Q => (z : G)) h1
      rw [cwConj_pow_apply] at h2
      simpa using h2
    have hcent : ∀ x ∈ Q,
        (k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK)))) * x =
          x * (k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK)))) := by
      intro x hx
      have h1 := hfix x hx
      have h2 := congrArg (fun z => z * (k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))))) h1
      simpa [mul_assoc] using h2
    have hknD : k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))) ∈ twoPoint H t :=
      Ksub_le_twoPoint hS ((Work.ThmF.Ksub H t).pow_mem hkK _)
    have hkn1 : k ^ (orderOf (cwConj Q k (Ksub_le_normalizer hS hkK))) = 1 :=
      eq_one_of_centralizes_Q hS hknD hcent
    rw [← orderOf_generator hS hC4 hW hkK hkgen]
    exact orderOf_dvd_iff_pow_eq_one.mpr hkn1
  rw [← card_Ksub_eq hS hC4 hW]
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- `cwConj k` is fixed-point-free on `Q ∖ {1}` for every non-trivial power. -/
theorem cwConj_pow_fpf {k : G} (hkK : k ∈ Work.ThmF.Ksub H t)
    (hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t) :
    ∀ n : ℕ, (cwConj Q k (Ksub_le_normalizer hS hkK)) ^ n ≠ 1 →
      ∀ x : ↥Q, ((cwConj Q k (Ksub_le_normalizer hS hkK)) ^ n) x = x → x = 1 := by
  intro n hn x hx
  have hknK : k ^ n ∈ Work.ThmF.Ksub H t := (Work.ThmF.Ksub H t).pow_mem hkK n
  have hknKset : k ^ n ∈ Work.ThmF.Kset H t := by
    rw [← (Ksub_eq_Kset_of_W_ne_bot hS hC4 hW).1]; exact hknK
  have hne : k ^ n ≠ 1 := by
    intro h1
    refine hn ?_
    ext z
    rw [cwConj_pow_apply, h1]
    simp
  have hcomm : (x : G) * (k ^ n) = (k ^ n) * (x : G) := by
    have h2 : k ^ n * (x : G) * (k ^ n)⁻¹ = (x : G) := by
      have hc := congrArg (fun z : ↥Q => (z : G)) hx
      rwa [cwConj_pow_apply] at hc
    have h3 := congrArg (fun z => z * (k ^ n)) h2
    exact (by simpa [mul_assoc] using h3 : (k ^ n) * (x : G) = (x : G) * (k ^ n)).symm
  have hq : (x : G) = 1 :=
    Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split (k ^ n) hknKset hne (x : G) x.2 hcomm
  exact Subtype.ext hq

/-- `cwConj k` is transitive on the involutions of `Q` for a generator `k` of `K`. -/
theorem cwConj_pow_trans {k : G} (hkK : k ∈ Work.ThmF.Ksub H t)
    (hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t) :
    ∀ x y : ↥Q, orderOf x = 2 → orderOf y = 2 →
      ∃ n : ℕ, ((cwConj Q k (Ksub_le_normalizer hS hkK)) ^ n) x = y := by
  intro x y hx hy
  have hxH : (x : G) ∈ involutions (H : Set G) :=
    ⟨hS.split.le x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hyH : (y : G) ∈ involutions (H : Set G) :=
    ⟨hS.split.le y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  obtain ⟨j, hjk, hjy⟩ := Kset_transitive_involutions hS.split.stronglyEmbedded
    hS.split.invol hS.split.not_mem (x : G) hxH (y : G) hyH
  have hjK : j ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hjk
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hkgen]; exact hjK)
  obtain ⟨r, hr⟩ := Work.ThmF.ChV12.exists_nat_pow_eq_of_zpow_eq hn
  refine ⟨r, ?_⟩
  apply Subtype.ext
  rw [cwConj_pow_apply, hr, hjy]

end Gen


section Main

variable (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hWne : Work.ThmF.W H t ≠ ⊥)

include hS hC4 hHig hWne

/-- `Q` has at least two involutions: `Q₀` is elementary abelian of order `≥ 4`. -/
theorem manyInvol_Q :
    ∃ x y : ↥Q, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y := by
  obtain ⟨n, hn2, hncard⟩ := caseC_Q0sub_card hS hC4 hWne
  have h4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hncard]
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn2
  have hsetcard : ((Work.ThmF.Q0sub H : Set G)).ncard = Nat.card ↥(Work.ThmF.Q0sub H) :=
    (Nat.card_coe_set_eq (Work.ThmF.Q0sub H : Set G)).symm
  have hmem1 : (1 : G) ∈ (Work.ThmF.Q0sub H : Set G) := (Work.ThmF.Q0sub H).one_mem
  have hlt : 1 < ((Work.ThmF.Q0sub H : Set G) \ {1}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem hmem1, hsetcard]
    omega
  obtain ⟨z1, hz1, hz1ne⟩ := Set.exists_ne_of_one_lt_ncard hlt (1 : G)
  obtain ⟨z2, hz2, hz2ne⟩ := Set.exists_ne_of_one_lt_ncard hlt z1
  have hz1Q0 : z1 ∈ Work.ThmF.Q0sub H := (Set.mem_sdiff z1).mp hz1 |>.1
  have hz2Q0 : z2 ∈ Work.ThmF.Q0sub H := (Set.mem_sdiff z2).mp hz2 |>.1
  have hz11 : z1 ≠ 1 := (Set.mem_sdiff z1).mp hz1 |>.2
  have hz21 : z2 ≠ 1 := (Set.mem_sdiff z2).mp hz2 |>.2
  have hsq1 : z1 * z1 = 1 := (Q0sub_structure hS hC4).1 z1 hz1Q0
  have hsq2 : z2 * z2 = 1 := (Q0sub_structure hS hC4).1 z2 hz2Q0
  refine ⟨⟨z1, Q0sub_le_Q hS.split hz1Q0⟩, ⟨z2, Q0sub_le_Q hS.split hz2Q0⟩, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq1)
      (fun h => hz11 (Subtype.ext_iff.mp h))
  · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq2)
      (fun h => hz21 (Subtype.ext_iff.mp h))
  · intro h
    exact hz2ne (Subtype.ext_iff.mp h).symm

/-- `Q` is a Suzuki `2`-group in case c) (with the cyclic group `K = J(D,t)` acting regularly
on the involutions). -/
noncomputable def isSuzuki2Grp_Q (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Work.Higman.IsSuzuki2Grp ↥Q := by
  classical
  set k : G := (exists_generator_Ksub hS hC4 hWne).choose with hk
  have hkK : k ∈ Work.ThmF.Ksub H t := (exists_generator_Ksub hS hC4 hWne).choose_spec.1
  have hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t :=
    (exists_generator_Ksub hS hC4 hWne).choose_spec.2
  have hnc : ∃ x y : ↥Q, x * y ≠ y * x := by
    by_contra h
    push_neg at h
    exact hnab (fun x hx y hy => congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  have htr : ∀ x y : ↥Q, orderOf x = 2 → orderOf y = 2 →
      ∃ n : ℕ, ((cwConj Q k (Ksub_le_normalizer hS hkK)) ^ n) x = y :=
    fun x y hx hy => cwConj_pow_trans hS hC4 hWne hkK hkgen x y hx hy
  exact
    { isPGroup := hS.two
      noncomm := hnc
      manyInvol := manyInvol_Q hS hC4 hHig hWne
      xi := cwConj Q k (Ksub_le_normalizer hS hkK)
      trans := htr }

/-- Higman: the square of every element of a Suzuki `2`-group is central. -/
theorem sq_mem_center (hSuz : Work.Higman.IsSuzuki2Grp ↥Q) :
    ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q := by
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  exact (hHig ↥Q htwo).2.1

/-- Higman: every central element of a Suzuki `2`-group is an involution. -/
theorem center_sq_eq_one (hSuz : Work.Higman.IsSuzuki2Grp ↥Q) :
    ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → z ^ 2 = 1 := by
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  intro z hz
  exact ((hHig ↥Q htwo).1 z).mp hz

/-- Higman: `Q` has class `2`. -/
theorem comm_mem_center (hSuz : Work.Higman.IsSuzuki2Grp ↥Q) :
    ∀ x y : ↥Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥Q := by
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  intro x y
  have hc := (hHig ↥Q htwo).2.2.1
  have h1 : ⁅x, y⁆ ∈ commutator ↥Q :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  rw [hc] at h1
  show x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥Q
  exact h1

/-- `Z(Q) = Q₀` (as subgroups of `Q`). -/
theorem center_eq_subgroupOf (hSuz : Work.Higman.IsSuzuki2Grp ↥Q) :
    Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q := by
  have hZ := mem_Q0sub_iff_sq_eq_one hS hC4
  have hcent := Q0sub_le_centerOf hS hC4
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have h1 : x * x = 1 := by simpa [pow_two] using center_sq_eq_one hS hC4 hHig hWne hSuz x hx
    exact (hZ x).mpr h1
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcent hx)
    exact Subtype.ext (h1.2 (y : G) y.2).symm

/-- `FpfXi` for the automorphism induced by a generator of `K`. -/
theorem fpfXi_conjQ (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3)
    (hSuz : Work.Higman.IsSuzuki2Grp ↥Q)
    {k : G} (hkK : k ∈ Work.ThmF.Ksub H t)
    (hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t) :
    Work.Higman.FpfXi (cwConj Q k (Ksub_le_normalizer hS hkK)) := by
  have hc : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [center_eq_subgroupOf hS hC4 hHig hWne hSuz]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hS.split)).toEquiv
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; exact hcard
  · rw [orderOf_conjQ hS hC4 hWne hkK hkgen, hc]
  · intro n hn x hx
    exact cwConj_pow_fpf hS hC4 hWne hkK hkgen n hn x hx

/-- The main semiregularity statement, in case `Q` is not abelian. -/
theorem caseC_W_semireg_of_nonabelian
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) :
    ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w → x ∈ Work.ThmF.Q0sub H := by
  -- set-up: `ξ` generating the `K`-action and `A` the action of `w`
  obtain ⟨k, hkK, hkgen⟩ := exists_generator_Ksub hS hC4 hWne
  have hSuz := isSuzuki2Grp_Q hS hC4 hHig hWne hnab
  have hξ := fpfXi_conjQ hS hC4 hHig hWne hcard hSuz hkK hkgen
  have hZ := mem_Q0sub_iff_sq_eq_one hS hC4
  have hsq := sq_mem_center hS hC4 hHig hWne hSuz
  have hzsq := center_sq_eq_one hS hC4 hHig hWne hSuz
  have hcomm := comm_mem_center hS hC4 hHig hWne hSuz
  intro w hwW hw1 x hxQ hxcomm
  -- `A`, the conjugation by `w` on `↥Q`
  have hwD : w ∈ twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t (Work.ThmF.W_le_centD H t hwW)
  have hwN : w ∈ Subgroup.normalizer (Q : Set G) := hS.split.normal (Subgroup.mem_inf.mp hwD).1
  set A : MulAut ↥Q := cwConj Q w hwN with hAdef
  -- `A` commutes with `ξ`
  have hwK : ∀ c ∈ Work.ThmF.Kset H t, w * c = c * w := by
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwW).2 c hc).symm
  have hAc : A * cwConj Q k (Ksub_le_normalizer hS hkK)
      = cwConj Q k (Ksub_le_normalizer hS hkK) * A := by
    have hkk : w * k = k * w :=
      hwK k (by rw [← (Ksub_eq_Kset_of_W_ne_bot hS hC4 hWne).1]; exact hkK)
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    show w * (k * (z : G) * k⁻¹) * w⁻¹ = k * (w * (z : G) * w⁻¹) * k⁻¹
    have h1 : w * (k * (z : G) * k⁻¹) * w⁻¹ = (w * k) * (z : G) * (w * k)⁻¹ := by group
    have h2 : (w * k) * (z : G) * (w * k)⁻¹ = (k * w) * (z : G) * (k * w)⁻¹ := by rw [hkk]
    have h3 : (k * w) * (z : G) * (k * w)⁻¹ = k * (w * (z : G) * w⁻¹) * k⁻¹ := by group
    rw [h1, h2, h3]

  -- `A` fixes `Z(Q)` pointwise
  have hAfix : ∀ z ∈ Subgroup.center ↥Q, A z = z := by
    intro z hz
    have hz' : z ∈ (Work.ThmF.Q0sub H).subgroupOf Q :=
      center_eq_subgroupOf hS hC4 hHig hWne hSuz ▸ hz
    have hzQ0 : (z : G) ∈ Work.ThmF.Q0sub H := Subgroup.mem_subgroupOf.mp hz'
    have hzc := Subgroup.mem_centralizer_iff.mp (W_le_centralizer_Q0sub hS hC4 hwW) (z : G) hzQ0
    apply Subtype.ext
    rw [cwConj_apply, ← hzc, mul_assoc, mul_inv_cancel, mul_one]
  -- `A ≠ 1` and `orderOf A` is odd
  have hA1 : A ≠ 1 := by
    intro hA
    have hcent : ∀ q ∈ Q, w * q = q * w := fun q hq => by
      have h1 := (cwConj_eq_one_iff Q w hwN).mp hA ⟨q, hq⟩
      have h2 := congrArg (fun t => t * w) h1
      simpa [mul_assoc] using h2
    exact hw1 (eq_one_of_centralizes_Q hS hwD hcent)
  have hoddw : Odd (orderOf w) := by
    have h1 : orderOf (⟨w, hwD⟩ : ↥(twoPoint H t)) ∣ Nat.card ↥(twoPoint H t) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨w, hwD⟩ : ↥(twoPoint H t)) = orderOf w :=
      (Subgroup.orderOf_coe _).symm
    rw [← h2]
    exact (Work.ThmF.split_odd_card_twoPoint hS.split).of_dvd_nat h1
  have hoddA : Odd (orderOf A) := by
    have hdvd : orderOf A ∣ orderOf w := by
      rw [orderOf_dvd_iff_pow_eq_one, hAdef]
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [cwConj_pow_apply]
      simp
    exact hoddw.of_dvd_nat hdvd
  -- apply the Suzuki core lemma
  have hcore := Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center hSuz hξ hsq hzsq hcomm hoddA hAc
    hAfix hA1
  have hfix : A ⟨x, hxQ⟩ = ⟨x, hxQ⟩ := by
    apply Subtype.ext
    rw [cwConj_apply]
    have h2 : w * x = x * w := hxcomm
    rw [show w * x * w⁻¹ = x by rw [h2, mul_assoc, mul_inv_cancel, mul_one]]
  have hcenter := hcore ⟨x, hxQ⟩ hfix
  have hx' : (⟨x, hxQ⟩ : ↥Q) ∈ (Work.ThmF.Q0sub H).subgroupOf Q :=
    center_eq_subgroupOf hS hC4 hHig hWne hSuz ▸ hcenter
  exact Subgroup.mem_subgroupOf.mp hx'

end Main

theorem caseC_W_semireg {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) :
    ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w → x ∈ Work.ThmF.Q0sub H := by
  intro w hwW hw1 x hxQ hxcomm
  by_cases hW : Work.ThmF.W H t = ⊥
  · rw [hW] at hwW
    exact absurd (Subgroup.mem_bot.mp hwW) hw1
  · by_cases hab : Submission.Blueprint.IsAbelianSubgroup Q
    · rw [W_eq_bot_of_abelian hS hC4 hab] at hwW
      exact absurd (Subgroup.mem_bot.mp hwW) hw1
    · exact caseC_W_semireg_of_nonabelian hS hC4 hHig hW hab hcard w hwW hw1 x hxQ hxcomm
