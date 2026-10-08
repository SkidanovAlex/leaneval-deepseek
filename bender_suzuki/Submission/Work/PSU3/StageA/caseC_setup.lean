import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.chVI_prop
import Submission.Work.Higman.Defs
import Submission.Work.Higman.typeB
import Submission.Work.Higman.layers_card_dichotomy_alt
import Submission.Work.Higman.card_isXiLayer_eq
import Submission.Work.Higman.scalar_module_of_layers
import Submission.Work.Higman.BS.quot_elementary
import Submission.Work.Higman.BS.Defs
import Submission.Work.Higman.BS.fpf
import Submission.Work.PSU3.StageB.cocycle_prod_is_coboundary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Elementary consequences of `PSU3Hyp`

The two ingredients used throughout are Peterfalvi II Ch. V §1 Prop. 1: the involutions of `H`
commute (they are central in the normal `2`-subgroup `Q`), so that `Q₀sub H = Q₀ H` is
elementary abelian and central in `Q`. -/

/-- The involutions of `H` lie in `Q`. -/
theorem caseC_involutions_subset_Q (hsplit : IsSplitRankOne H Q t) :
    involutions (H : Set G) ⊆ (Q : Set G) :=
  fun _ hx => Q0sub_le_Q hsplit (Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hx))

/-- Every element of `Q₀sub H` is central in `Q`.

This is Peterfalvi II Ch. V §1 Prop. 1 (c) (`prop1c`: the involutions of `H` are central in `Q`,
as `Q` is nilpotent), transported to the closure `Q₀sub H = ⟨Inv H⟩`. -/
theorem caseC_Q0sub_central (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ z ∈ Work.ThmF.Q0sub H, ∀ x ∈ Q, z * x = x * z := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hnil : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent hS.two
  have hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
  have hcent : involutions (H : Set G) ⊆ (Work.ThmF.centerOf Q : Set G) :=
    fun u hu => Work.ThmF.ChV12.prop1c hS.situation H Q t hsplit hD hnil u hu
  have hQ0c : Work.ThmF.Q0 H ⊆ (Work.ThmF.centerOf Q : Set G) := by
    intro x hx
    rcases (Work.ThmF.mem_Q0_iff.mp hx) with ⟨hxH, hxo⟩ | rfl
    · exact hcent ⟨hxH, hxo⟩
    · exact (Work.ThmF.centerOf Q).one_mem
  have hle : Work.ThmF.Q0sub H ≤ Work.ThmF.centerOf Q :=
    (Subgroup.closure_le _).mpr hQ0c
  intro z hz x hx
  have hz' := hle hz
  rw [Work.ThmF.mem_centerOf] at hz'
  exact hz'.2 x hx

/-- The involutions of `H` commute pairwise (Peterfalvi II Ch. V §1 Prop. 1 (c)). -/
theorem caseC_involutions_comm (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
  have hcent := caseC_Q0sub_central hS hC4
  intro u hu v hv
  refine hcent u (Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hu)) v ?_
  exact Q0sub_le_Q hS.split (Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hv))

/-- `Q₀sub H = Q₀ H` as sets. -/
theorem caseC_Q0sub_eq_Q0 (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    (Work.ThmF.Q0sub H : Set G) = Work.ThmF.Q0 H := by
  have hcomm := caseC_involutions_comm hS hC4
  obtain ⟨-, -, -, hinv⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  refine Set.Subset.antisymm (fun x hx => ?_) (Work.ThmF.Q0_le_Q0sub H)
  by_cases h1 : x = 1
  · rw [h1]; exact Work.ThmF.one_mem_Q0 H
  · exact Work.ThmF.involutions_subset_Q0 H (hinv x hx h1)

/-- Every element of `Q₀sub H` is either `1` or an involution of `H`. -/
theorem caseC_mem_Q0sub_iff (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ x ∈ Work.ThmF.Q0sub H, x * x = 1 := by
  have hcomm := caseC_involutions_comm hS hC4
  exact (Work.ThmF.ChV12.Q0sub_elementary H hcomm).1

/-! ## `Ksub`, cardinalities, and the regular action on the involutions -/

theorem caseC_W_ne_bot {H Q : Subgroup G} {t : G} {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t)
    (hζ1 : ζ ≠ 1) :
    Work.ThmF.W H t ≠ ⊥ := by
  intro hbot
  rw [hbot] at hζ
  exact hζ1 (Subgroup.mem_bot.mp hζ)

/-- `Ksub H t = Kset H t` is cyclic (Ch. V §1 Prop. 2 in the case `W ≠ 1`, `chVI_prop.lean`). -/
theorem caseC_Ksub_cyc {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t ∧ IsCyclic ↥(Work.ThmF.Ksub H t) :=
  Ksub_eq_Kset_of_W_ne_bot hS hC4 hWne

theorem caseC_Q0sub_isPGroup {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) :
    IsPGroup 2 ↥(Work.ThmF.Q0sub H) :=
  hS.two.to_le (Q0sub_le_Q hS.split)

/-- `Q₀sub H = Inv H ∪ {1}` as a disjoint union. -/
theorem caseC_Q0sub_set {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    (Work.ThmF.Q0sub H : Set G) = involutions (H : Set G) ∪ {1} := by
  rw [caseC_Q0sub_eq_Q0 hS hC4]; rfl

theorem one_notMem_involutions {H : Subgroup G} :
    (1 : G) ∉ involutions (H : Set G) := by
  simp [Submission.Blueprint.involutions, orderOf_one]

/-- `|Q₀sub H| = |Inv H| + 1`. -/
theorem caseC_card_Q0sub_eq {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 := by
  have h1 : Nat.card ↥(Work.ThmF.Q0sub H) = (Work.ThmF.Q0sub H : Set G).ncard := by
    show Nat.card (Work.ThmF.Q0sub H : Set G) = _
    exact Nat.card_coe_set_eq _
  rw [h1, caseC_Q0sub_set hS hC4]
  rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr one_notMem_involutions),
    Set.ncard_singleton]

/-- `Ksub H t` has `|Inv H|` elements. -/
theorem caseC_card_Ksub (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    Nat.card ↥(Work.ThmF.Ksub H t) = (involutions (H : Set G)).ncard := by
  have hKset := (caseC_Ksub_cyc hS hC4 hWne).1
  have h1 : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
    have h1' : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Ksub H t : Set G).ncard := by
      show Nat.card (Work.ThmF.Ksub H t : Set G) = _
      exact Nat.card_coe_set_eq _
    rw [h1', hKset]
  rw [h1]
  exact Work.ThmF.Bender.cardKsetEqInv hS.split.stronglyEmbedded hS.split.invol hS.split.not_mem

theorem caseC_Ksub_ne_bot (hS : Work.PSU3.PSU3Hyp H Q t) :
    Work.ThmF.Ksub H t ≠ ⊥ := by
  obtain ⟨x, hx, hx1⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one hS.situation hS.split
  intro hbot
  have : x ∈ (⊥ : Subgroup G) := by
    rw [← hbot]; exact Work.ThmF.Kset_le_Ksub H t hx
  exact hx1 (Subgroup.mem_bot.mp this)

/-- `2 ≤ n` when `|Q₀sub H| = 2 ^ n`. -/
theorem caseC_Q0sub_card (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (caseC_Q0sub_isPGroup hS)
  have hcardK := caseC_card_Ksub hS hC4 hWne
  have hcardQ := caseC_card_Q0sub_eq hS hC4
  have h3 : 3 ≤ 2 ^ n := by
    have hK2 : 2 ≤ (involutions (H : Set G)).ncard := by
      obtain ⟨x, hx, hx1⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one hS.situation hS.split
      have hsub : ({1, x} : Set G) ⊆ Work.ThmF.Kset H t := by
        intro y hy
        rcases hy with rfl | rfl
        · exact Work.ThmF.one_mem_Kset H t
        · exact hx
      have h2 : ({1, x} : Set G).ncard = 2 := by
        rw [Set.ncard_insert_of_notMem (by simpa using hx1.symm), Set.ncard_singleton]
      have hKsetcard : (Work.ThmF.Kset H t).ncard = (involutions (H : Set G)).ncard :=
        Work.ThmF.Bender.cardKsetEqInv hS.split.stronglyEmbedded hS.split.invol
          hS.split.not_mem
      have := Set.ncard_le_ncard hsub
      omega
    omega
  refine ⟨n, ?_, hn⟩
  have hn0 : n ≠ 0 := by intro h; rw [h] at h3; simp at h3
  have hn1 : n ≠ 1 := by intro h; rw [h] at h3; norm_num at h3
  omega

/-- The regular action of `Kset H t` on the involutions of `H` (Peterfalvi I Ch. I §2). -/
theorem caseC_reg (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃! k : G, k ∈ Work.ThmF.Kset H t ∧ k * a * k⁻¹ = b := by
  intro a ha b hb
  have hH := hS.split.stronglyEmbedded
  have ht := hS.split.invol
  have htH := hS.split.not_mem
  have hcard := Work.ThmF.Bender.cardKsetEqInv hH ht htH
  have hinj := Work.ThmF.Bender.Kset_conj_injective hH ht htH ha.1 ha.2
  have himg : ∀ k ∈ Work.ThmF.Kset H t, k * a * k⁻¹ ∈ involutions (H : Set G) := by
    intro k hk
    have hkH : k ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hk)).1
    refine ⟨H.mul_mem (H.mul_mem hkH ha.1) (H.inv_mem hkH), ?_⟩
    rw [Work.ThmF.Bender.orderOf_conj_eq]
    exact ha.2
  have himg_sub : (fun k => k * a * k⁻¹) '' (Work.ThmF.Kset H t) ⊆ involutions (H : Set G) := by
    rintro y ⟨k, hk, rfl⟩
    exact himg k hk
  have heq : (fun k => k * a * k⁻¹) '' (Work.ThmF.Kset H t) = involutions (H : Set G) := by
    refine Set.eq_of_subset_of_ncard_le himg_sub ?_ (Set.toFinite _)
    rw [hinj.ncard_image, hcard]
  have hsurj : ∀ y ∈ involutions (H : Set G),
      ∃ k ∈ Work.ThmF.Kset H t, k * a * k⁻¹ = y := by
    intro y hy
    have : y ∈ (fun k => k * a * k⁻¹) '' (Work.ThmF.Kset H t) := by rw [heq]; exact hy
    obtain ⟨k, hk, hkf⟩ := this
    exact ⟨k, hk, hkf⟩
  obtain ⟨k, hkK, hkf⟩ := hsurj b hb
  refine ⟨k, ⟨hkK, hkf⟩, ?_⟩
  rintro k' ⟨hk'K, hk'b⟩
  exact hinj hk'K hkK (by show k' * a * k'⁻¹ = k * a * k⁻¹; rw [hk'b, hkf])

/-! ## The Suzuki `2`-group structure on `Q` -/

/-- Conjugation by an element of `N_G(Q)` as an automorphism of `Q`. -/
noncomputable def conjOnQ {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : MulAut ↥Q where
  toFun x := ⟨g * (x : G) * g⁻¹,
    (Subgroup.mem_normalizer_iff (H := Q) (g := g)).mp hg (x : G) |>.mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    have h := (Subgroup.mem_normalizer_iff (H := Q) (g := g⁻¹)).mp
      ((Subgroup.normalizer (Q : Set G)).inv_mem hg) (x : G) |>.mp x.2
    simpa using h⟩
  left_inv x := by ext; group
  right_inv x := by ext; group
  map_mul' x y := by
    apply Subtype.ext
    show g * ((x : G) * (y : G)) * g⁻¹ = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group

theorem conjOnQ_coe {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    ((conjOnQ g hg x : ↥Q) : G) = g * (x : G) * g⁻¹ := rfl

theorem conjOnQ_pow_coe {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (k : ℕ) (x : ↥Q) :
    (((conjOnQ g hg) ^ k) x : G) = g ^ k * (x : G) * (g ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, conjOnQ_coe, ih, pow_succ]
      group

theorem conjOnQ_eq_one_iff {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    conjOnQ g hg = 1 ↔ ∀ x ∈ Q, g * x * g⁻¹ = x := by
  constructor
  · intro h x hx
    have h1 : (conjOnQ g hg) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      have := congrArg (fun f : MulAut ↥Q => f ⟨x, hx⟩) h
      simpa using this
    have h2 := congrArg Subtype.val h1
    rw [conjOnQ_coe] at h2
    simpa using h2
  · intro h
    apply MulEquiv.ext
    intro x
    have hx : (conjOnQ g hg) x = x := Subtype.ext (by rw [conjOnQ_coe]; exact h x x.2)
    simpa using hx

/-- The element of `Ksub H t` generating it. -/
noncomputable def caseC_gen {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    ↥(Work.ThmF.Ksub H t) :=
  Classical.choose (isCyclic_iff_exists_zpowers_eq_top.mp (caseC_Ksub_cyc hS hC4 hWne).2)

theorem caseC_gen_spec {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    Subgroup.zpowers (caseC_gen hS hC4 hWne) = ⊤ :=
  Classical.choose_spec
    (isCyclic_iff_exists_zpowers_eq_top.mp (caseC_Ksub_cyc hS hC4 hWne).2)

theorem caseC_gen_mem_Kset {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ∈ Work.ThmF.Kset H t := by
  have hKset := (caseC_Ksub_cyc hS hC4 hWne).1
  have h : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ∈
      (Work.ThmF.Ksub H t : Set G) := (caseC_gen hS hC4 hWne).2
  rwa [hKset] at h

theorem caseC_gen_mem_normalizer {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ∈
      Subgroup.normalizer (Q : Set G) :=
  hS.split.normal
    (Subgroup.mem_inf.mp
      (Work.ThmF.Ksub_le_twoPoint (H := H) t (caseC_gen hS hC4 hWne).2)).1

theorem caseC_gen_ne_one {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    caseC_gen hS hC4 hWne ≠ 1 := by
  intro h
  apply caseC_Ksub_ne_bot hS
  refine le_antisymm ?_ bot_le
  intro x hx
  set x' : ↥(Work.ThmF.Ksub H t) := ⟨x, hx⟩ with hx'_def
  have hx'' : x' ∈ Subgroup.zpowers (caseC_gen hS hC4 hWne) := by
    rw [caseC_gen_spec hS hC4 hWne]; exact Subgroup.mem_top x'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx''
  rw [h] at hk
  simp at hk
  exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hk).symm

theorem caseC_gen_orderOf {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    orderOf (caseC_gen hS hC4 hWne) = Nat.card ↥(Work.ThmF.Ksub H t) :=
  orderOf_eq_card_of_zpowers_eq_top (caseC_gen_spec hS hC4 hWne)

/-- The automorphism of `Q` induced by a generator of `Ksub H t`. -/
noncomputable def caseC_xi {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) : MulAut ↥Q :=
  conjOnQ ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G)
    (caseC_gen_mem_normalizer hS hC4 hWne)

theorem caseC_xi_pow_coe {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) (k : ℕ)
    (x : ↥Q) :
    (((caseC_xi hS hC4 hWne) ^ k) x : G) =
      ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ k * (x : G) *
        (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ k)⁻¹ :=
  conjOnQ_pow_coe _ _ k x

theorem caseC_Ksub_inf_Q0sub {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) :
    Work.ThmF.Ksub H t ⊓ Work.ThmF.Q0sub H = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hxQ : x ∈ Q := Q0sub_le_Q hS.split hx.2
  have hxD : x ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.Ksub_le_twoPoint (H := H) t hx.1
  have : x ∈ Q ⊓ Submission.Blueprint.twoPoint H t := ⟨hxQ, hxD⟩
  rw [hS.split.inf_eq] at this
  exact this

theorem caseC_orderOf_two_iff {H Q : Subgroup G}
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1) (x : ↥Q) :
    orderOf x = 2 ↔ x ≠ 1 ∧ (x : G) ∈ Work.ThmF.Q0sub H := by
  have hx2 : x ^ 2 = 1 ↔ (x : G) ∈ Work.ThmF.Q0sub H := by
    rw [pow_two]; exact (hZ x).symm
  rw [← hx2]
  constructor
  · intro h
    exact ⟨fun h1 => by rw [h1] at h; simp at h,
      by rw [← h]; exact pow_orderOf_eq_one x⟩
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_prime h2 h1

theorem caseC_invH_of_orderOf_two {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1) {x : ↥Q}
    (h : orderOf x = 2) : (x : G) ∈ involutions (H : Set G) := by
  obtain ⟨hx1, hxQ0⟩ := (caseC_orderOf_two_iff hZ x).mp h
  have hcomm := caseC_involutions_comm hS hC4
  exact (Work.ThmF.ChV12.Q0sub_elementary H hcomm).2.2.2 (x : G) hxQ0
    (fun hh => hx1 (Subtype.ext hh))

/-- Any element of `⟨g⟩` is a natural power of `g` (finite order). -/
theorem pow_eq_of_mem_zpowers {G : Type} [Group G] {g x : G} (hg : 0 < orderOf g)
    (hx : x ∈ Subgroup.zpowers g) : ∃ j : ℕ, g ^ j = x := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨(m % (orderOf g : ℤ)).toNat, ?_⟩
  have hem : 0 ≤ m % (orderOf g : ℤ) := Int.emod_nonneg m (by exact_mod_cast hg.ne')
  have h1 : g ^ m = g ^ (m % (orderOf g : ℤ)) :=
    zpow_eq_zpow_emod' m (pow_orderOf_eq_one g)
  have h2 : g ^ ((m % (orderOf g : ℤ)).toNat) = g ^ (m % (orderOf g : ℤ)) := by
    conv_rhs => rw [← Int.toNat_of_nonneg hem, zpow_natCast]
  rw [← hm]
  exact h2.trans h1.symm

theorem caseC_many_invol {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hWne : Work.ThmF.W H t ≠ ⊥) :
    ∃ x y : ↥Q, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y := by
  obtain ⟨n, hn2, hncard⟩ := caseC_Q0sub_card hS hC4 hWne
  have hge : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hncard]; exact pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) hn2
  have hset : (Work.ThmF.Q0sub H : Set G).ncard = Nat.card ↥(Work.ThmF.Q0sub H) := by
    show _ = Nat.card (Work.ThmF.Q0sub H : Set G)
    rw [Nat.card_coe_set_eq]
  have hmem1 : (1 : G) ∈ (Work.ThmF.Q0sub H : Set G) :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
  have hdiff : 1 < ((Work.ThmF.Q0sub H : Set G) \ {1}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem hmem1, hset]; omega
  obtain ⟨z1, hz1, hz1ne⟩ := Set.exists_ne_of_one_lt_ncard hdiff (1 : G)
  obtain ⟨z2, hz2, hz2ne⟩ := Set.exists_ne_of_one_lt_ncard hdiff z1
  have hz1Q : z1 ∈ Work.ThmF.Q0sub H := (Set.mem_sdiff z1).mp hz1 |>.1
  have hz2Q : z2 ∈ Work.ThmF.Q0sub H := (Set.mem_sdiff z2).mp hz2 |>.1
  have hz11 : z1 ≠ 1 := (Set.mem_sdiff z1).mp hz1 |>.2
  have hz21 : z2 ≠ 1 := (Set.mem_sdiff z2).mp hz2 |>.2
  have hcomm := caseC_involutions_comm hS hC4
  have hsq1 : z1 * z1 = 1 := (Work.ThmF.ChV12.Q0sub_elementary H hcomm).1 z1 hz1Q
  have hsq2 : z2 * z2 = 1 := (Work.ThmF.ChV12.Q0sub_elementary H hcomm).1 z2 hz2Q
  refine ⟨⟨z1, Q0sub_le_Q hS.split hz1Q⟩, ⟨z2, Q0sub_le_Q hS.split hz2Q⟩, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq1)
      (fun h => hz11 (Subtype.ext_iff.mp h))
  · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq2)
      (fun h => hz21 (Subtype.ext_iff.mp h))
  · intro h
    exact hz2ne (Subtype.ext_iff.mp h).symm

theorem caseC_center_subgroupOf {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hHig : Submission.Blueprint.HigmanProp)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hSuz : Work.Higman.IsSuzuki2Grp ↥Q) :
    Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q := by
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  have h1 := (hHig ↥Q htwo).1
  ext x
  rw [h1, pow_two, Subgroup.mem_subgroupOf]
  exact (hZ x).symm

noncomputable def caseC_isSuzuki2Grp {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hWne : Work.ThmF.W H t ≠ ⊥) : Work.Higman.IsSuzuki2Grp ↥Q :=
  { isPGroup := hS.two
    noncomm := by
      by_contra h
      push_neg at h
      exact hnab (fun x hx y hy => congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
    manyInvol := caseC_many_invol hS hC4 hZ hWne
    xi := caseC_xi hS hC4 hWne
    trans := by
      intro x y hx2 hy2
      have hinvx := caseC_invH_of_orderOf_two hS hC4 hZ hx2
      have hinvy := caseC_invH_of_orderOf_two hS hC4 hZ hy2
      obtain ⟨k, ⟨hkK, hkk⟩, -⟩ := (caseC_reg hS hC4) (x : G) hinvx (y : G) hinvy
      set k' : ↥(Work.ThmF.Ksub H t) := ⟨k, Work.ThmF.Kset_le_Ksub H t hkK⟩ with hk'_def
      have hkzp' : k' ∈ Subgroup.zpowers (caseC_gen hS hC4 hWne) := by
        rw [caseC_gen_spec hS hC4 hWne]; exact Subgroup.mem_top k'
      have hkzp : k ∈ Subgroup.zpowers
          ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) := by
        have h3 : k ∈ Subgroup.map (Work.ThmF.Ksub H t).subtype
            (Subgroup.zpowers (caseC_gen hS hC4 hWne)) := ⟨k', hkzp', rfl⟩
        rwa [MonoidHom.map_zpowers] at h3
      have hpos : 0 < orderOf
          ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) := by
        rw [Subgroup.orderOf_coe, caseC_gen_orderOf hS hC4 hWne]
        exact Nat.card_pos
      obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers hpos hkzp
      refine ⟨j, ?_⟩
      apply Subtype.ext
      rw [caseC_xi_pow_coe hS hC4 hWne j x, hj, hkk] }


/-! ## The averaging (coboundary) tool for `Q₀sub` -/

/-- Commutation of conjugation by an involution: `t (xy) t = (txt)(tyt)`. -/
private lemma caseC_conj_mul_of_coboundary {G : Type} [Group G] {a x z p : G}
    (hxp : p⁻¹ * x * p = a * x) (hzp : p⁻¹ * z * p = a * z)
    (hxc : x * a = a * x) (ha2 : a * a = 1) :
    p⁻¹ * (x * z) * p = x * z := by
  rw [show p⁻¹ * (x * z) * p = (p⁻¹ * x * p) * (p⁻¹ * z * p) by group, hxp, hzp]
  calc (a * x) * (a * z) = a * (x * a) * z := by group
    _ = a * (a * x) * z := by rw [hxc]
    _ = x * z := by rw [← mul_assoc, ha2, one_mul]

/-- **A `P`-fixed point of `Q` outside `Q₀sub` from a fixed point modulo `Q₀sub`.**

If `x ∈ Q ∖ Q₀sub` is fixed modulo `Q₀sub` by the odd-order subgroup `P ≤ D = twoPoint H t`
(i.e. `p⁻¹ x p x⁻¹ ∈ Q₀sub` for all `p ∈ P`), then some `y ∈ Q ∖ Q₀sub` is fixed by `P` on the
nose.  (The crossed homomorphism `c p = p⁻¹ x p x⁻¹` with values in the exponent-`2` central
subgroup `Q₀sub` is a coboundary, `H¹(P, Q₀sub) = 0`.) -/
theorem caseC_exists_fixed_of_fixed_mod_Q0 {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPD : P ≤ Submission.Blueprint.twoPoint H t)
    (hPodd : Odd (Nat.card ↥P))
    {x : G} (hx : x ∈ Q) (hx0 : x ∉ Work.ThmF.Q0sub H)
    (hfix : ∀ p ∈ P, p⁻¹ * x * p * x⁻¹ ∈ Work.ThmF.Q0sub H) :
    ∃ y ∈ Q, y ∉ Work.ThmF.Q0sub H ∧ ∀ p ∈ P, p⁻¹ * y * p = y := by
  have hcomm := caseC_involutions_comm hS hC4
  have hel := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have hQ0norm : ∀ p ∈ P, ∀ a ∈ Work.ThmF.Q0sub H, p⁻¹ * a * p ∈ Work.ThmF.Q0sub H := by
    intro p hp a ha
    have hp1 : p ∈ H := (Subgroup.mem_inf.mp (hPD hp)).1
    simpa using hel.2.2.1 p⁻¹ (H.inv_mem hp1) a ha
  obtain ⟨z, hzA, hzact⟩ :=
    Work.PSU3.StageB.cocycle_prod_is_coboundary (P := P) (A := Work.ThmF.Q0sub H)
      hQ0norm hel.2.1 hel.1 hPodd (fun p => p⁻¹ * x * p * x⁻¹)
      (fun p hp => hfix p hp) (fun r hr p hp => by group)
  refine ⟨x * z, Q.mul_mem hx (Q0sub_le_Q hS.split hzA), ?_, ?_⟩
  · intro hcon
    exact hx0 (by
      have h : (x * z) * z⁻¹ ∈ Work.ThmF.Q0sub H :=
        (Work.ThmF.Q0sub H).mul_mem hcon ((Work.ThmF.Q0sub H).inv_mem hzA)
      simpa [mul_assoc] using h)
  · intro p hp
    have hxp : p⁻¹ * x * p = (p⁻¹ * x * p * x⁻¹) * x := by group
    have hzp : p⁻¹ * z * p = (p⁻¹ * x * p * x⁻¹) * z := hzact p hp
    have hxc : x * (p⁻¹ * x * p * x⁻¹) = (p⁻¹ * x * p * x⁻¹) * x :=
      (caseC_Q0sub_central hS hC4 _ (hfix p hp) x hx).symm
    have hcp2 : (p⁻¹ * x * p * x⁻¹) * (p⁻¹ * x * p * x⁻¹) = 1 := hel.1 _ (hfix p hp)
    exact caseC_conj_mul_of_coboundary hxp hzp hxc hcp2

/-- Conjugation by `w ∈ W H t` (which lies in `H ≤ N_G(Q)`) as an automorphism of `Q`. -/
noncomputable def caseC_conjW {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    {w : G} (hw : w ∈ Work.ThmF.W H t) : MulAut ↥Q :=
  conjOnQ w (hS.split.normal
    (Subgroup.mem_inf.mp (Work.ThmF.centD_le_twoPoint (H := H) t
      (Work.ThmF.W_le_centD H t hw))).1)

theorem conjOnQ_mul {Q : Subgroup G} (g₁ g₂ : G)
    (h₁ : g₁ ∈ Subgroup.normalizer (Q : Set G)) (h₂ : g₂ ∈ Subgroup.normalizer (Q : Set G))
    (h₁₂ : g₁ * g₂ ∈ Subgroup.normalizer (Q : Set G)) :
    conjOnQ (g₁ * g₂) h₁₂ = conjOnQ g₁ h₁ * conjOnQ g₂ h₂ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have h1 : (((conjOnQ (g₁ * g₂) h₁₂) x : ↥Q) : G) = g₁ * g₂ * (x : G) * (g₁ * g₂)⁻¹ :=
    conjOnQ_coe _ _ _
  rw [h1, MulAut.mul_apply, conjOnQ_coe, conjOnQ_coe]
  group

theorem conjOnQ_one {Q : Subgroup G} (h : (1 : G) ∈ Subgroup.normalizer (Q : Set G)) :
    conjOnQ 1 h = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [conjOnQ_coe]
  simp

theorem conjOnQ_zpow_coe {Q : Subgroup G} (g : G) (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (k : ℤ) (hgk : g ^ k ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    (((conjOnQ g hg) ^ k) x : G) = g ^ k * (x : G) * (g ^ k)⁻¹ := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn, zpow_natCast]; simpa using conjOnQ_pow_coe g hg n x
  · rw [hn]
    have h1 : (conjOnQ g hg) ^ (-(n : ℤ)) = ((conjOnQ g hg) ^ n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [h1, zpow_neg, zpow_natCast]
    have h3 : (x : G) = g ^ n * ((((conjOnQ g hg) ^ n)⁻¹ x : ↥Q) : G) * (g ^ n)⁻¹ := by
      have h5 : ((conjOnQ g hg) ^ n) (((conjOnQ g hg) ^ n)⁻¹ x) = x := by simp
      conv_lhs => rw [← h5]
      rw [conjOnQ_pow_coe]
    calc ((((conjOnQ g hg) ^ n)⁻¹ x : ↥Q) : G)
        = (g ^ n)⁻¹ * (g ^ n * ((((conjOnQ g hg) ^ n)⁻¹ x : ↥Q) : G) * (g ^ n)⁻¹) * g ^ n := by
          group
      _ = (g ^ n)⁻¹ * (x : G) * g ^ n := by rw [h3]
      _ = (g ^ n)⁻¹ * (x : G) * (g ^ n)⁻¹⁻¹ := by group

theorem caseC_xi_zpow_coe {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥) (k : ℤ)
    (x : ↥Q) :
    (((caseC_xi hS hC4 hWne) ^ k) x : G) =
      ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ k * (x : G) *
        (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ k)⁻¹ :=
  conjOnQ_zpow_coe _ _ k ((Subgroup.normalizer (Q : Set G)).zpow_mem
    (caseC_gen_mem_normalizer hS hC4 hWne) k) x

end Work.PSU3.StageA
