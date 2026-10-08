import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.Reductions.Defs
import Submission.Work.Endgame.Defs
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.ThreePoints.isStronglyEmbedded_inf_subgroupOf
import Submission.Work.ThreePoints.oddCore_quotient_oddCore
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-! ## Elementary helpers -/

/-- An element of order `2` lies in every normal subgroup of odd index. -/
theorem mem_of_orderOf_eq_two_of_odd_index {G : Type} [Group G] {L : Subgroup G} [L.Normal]
    (hidx : Odd L.index) {x : G} (hx : orderOf x = 2) : x ∈ L := by
  by_contra hxL
  have hdvd : orderOf (QuotientGroup.mk' L x) ∣ 2 := by
    rw [← hx]; exact orderOf_map_dvd (QuotientGroup.mk' L) x
  have hne1 : orderOf (QuotientGroup.mk' L x) ≠ 1 := by
    intro h
    refine hxL ?_
    have hker : x ∈ (QuotientGroup.mk' L).ker := by
      rw [MonoidHom.mem_ker]; exact (orderOf_eq_one_iff.mp h)
    rwa [QuotientGroup.ker_mk'] at hker
  have htwo : orderOf (QuotientGroup.mk' L x) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hne1
  have hdvd2 : 2 ∣ L.index := by
    rw [Subgroup.index_eq_card]
    exact htwo ▸ orderOf_dvd_natCard (QuotientGroup.mk' L x)
  exact Nat.not_even_iff_odd.mpr hidx (even_iff_two_dvd.mpr hdvd2)

/-- The image of an element of order `2` in the quotient by an odd-order normal subgroup has
order `2`. -/
theorem orderOf_mk'_eq_two {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    (hodd : Odd (Nat.card N)) {x : G} (hx : orderOf x = 2) :
    orderOf (QuotientGroup.mk' N x) = 2 := by
  have hxnot : x ∉ N := by
    intro hmem
    have h1 : orderOf x ∣ Nat.card ↥N := by
      rw [← Subgroup.orderOf_mk x hmem]; exact orderOf_dvd_natCard _
    have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd h1
    have h2dvd : 2 ∣ orderOf x := by rw [hx]
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2dvd)
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ 2 := by
    rw [← hx]; exact orderOf_map_dvd (QuotientGroup.mk' N) x
  have hne1 : orderOf (QuotientGroup.mk' N x) ≠ 1 := by
    intro h
    refine hxnot ?_
    have hker : x ∈ (QuotientGroup.mk' N).ker := by
      rw [MonoidHom.mem_ker]; exact (orderOf_eq_one_iff.mp h)
    rwa [QuotientGroup.ker_mk'] at hker
  exact (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hne1

/-- A four-group of `G` survives in the quotient by an odd-order normal subgroup. -/
theorem hasFourGroup_quotient_odd {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    (hodd : Odd (Nat.card N)) (hfour : HasFourGroup G) : HasFourGroup (G ⧸ N) := by
  obtain ⟨a, b, ha2, hb2, hne, hcomm⟩ := hfour
  have haa : a * a = 1 := by rw [← pow_two, ← ha2]; exact pow_orderOf_eq_one a
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2]; exact pow_orderOf_eq_one b
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [mul_assoc]
      _ = a * ((b * a) * b) := by rw [← mul_assoc b a b]
      _ = a * ((a * b) * b) := by rw [← hcomm]
      _ = a * (a * (b * b)) := by rw [mul_assoc a b b]
      _ = 1 := by rw [hbb, mul_one, haa]
  have habne : a * b ≠ 1 := by
    intro h
    refine hne ?_
    calc a = a * 1 := (mul_one a).symm
      _ = a * (a * b) := by rw [← h]
      _ = a * a * b := by rw [mul_assoc]
      _ = b := by rw [haa, one_mul]
  have habord : orderOf (a * b) = 2 := by
    have hdvd : orderOf (a * b) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hab2)
    exact (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left (by
      rwa [orderOf_eq_one_iff])
  refine ⟨QuotientGroup.mk' N a, QuotientGroup.mk' N b, orderOf_mk'_eq_two hodd ha2,
    orderOf_mk'_eq_two hodd hb2, ?_, ?_⟩
  · intro hab
    have hmem : a * b ∈ N := by
      have h1 : QuotientGroup.mk' N (a * b) = 1 := by
        have h2 : QuotientGroup.mk' N b * QuotientGroup.mk' N b = 1 := by
          rw [← map_mul, hbb, map_one]
        calc QuotientGroup.mk' N (a * b)
            = QuotientGroup.mk' N a * QuotientGroup.mk' N b := map_mul _ _ _
          _ = QuotientGroup.mk' N b * QuotientGroup.mk' N b := by rw [hab]
          _ = 1 := h2
      have hker : a * b ∈ (QuotientGroup.mk' N).ker := by
        rw [MonoidHom.mem_ker]; exact h1
      rwa [QuotientGroup.ker_mk'] at hker
    -- `a * b` has order `2` but lies in the odd-order subgroup `N`
    have h1 : orderOf (a * b) ∣ Nat.card ↥N := by
      rw [← Subgroup.orderOf_mk (a * b) hmem]; exact orderOf_dvd_natCard _
    have hodd' : Odd (orderOf (a * b)) := Odd.of_dvd_nat hodd h1
    have h2dvd : 2 ∣ orderOf (a * b) := by rw [habord]
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2dvd)
  · rw [← map_mul, ← map_mul, hcomm]

/-! ## The main theorem -/

/-- Peterfalvi I Ch. II §1, hypothesis **(B1-a)**: for a group `F` of 2-rank `≥ 2` of order `< n`
with a proper Bender (= strongly embedded) subgroup `H`, if `(B1)` holds for `n` then the
involutions of `H / O_{2'}(F)` commute pairwise, i.e. the commutator of two involutions of `H` lies
in `O_{2'}(F)`.  Derived from `ThmBBelow n` and `ModelFactsProp`. -/
theorem involutions_commute_of_below {F : Type} [Group F] [Finite F] (n : ℕ)
    (hB1 : Submission.Blueprint.ThmBBelow n) (hMod : Submission.Blueprint.ModelFactsProp)
    (hlt : Nat.card F < n) (hfour : Submission.Blueprint.HasFourGroup F)
    {H : Subgroup F} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {u v : F}
    (hu : u ∈ Submission.Blueprint.involutions (H : Set F))
    (hv : v ∈ Submission.Blueprint.involutions (H : Set F)) :
    u * v * u⁻¹ * v⁻¹ ∈ Submission.Blueprint.oddCore F := by
  classical
  have key : ∀ m : ℕ, m < n → ∀ (F : Type) [Group F] [Finite F], Nat.card F = m →
      HasFourGroup F → ∀ {H : Subgroup F}, IsStronglyEmbedded H → ∀ {u v : F},
      u ∈ involutions (H : Set F) → v ∈ involutions (H : Set F) →
      u * v * u⁻¹ * v⁻¹ ∈ oddCore F := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm F _ _ hcard hfour H hH u v hu hv
      obtain ⟨huH, hu2⟩ := hu
      obtain ⟨hvH, hv2⟩ := hv
      obtain ⟨L, hLnorm, hcoreL, hLidx, Y, hYgrp, φ, hφsurj, hφker, hY⟩ :=
        hB1 F (hcard.symm ▸ hm) ⟨hfour, ⟨H, hH⟩⟩
      letI : Group Y := hYgrp
      haveI : L.Normal := hLnorm
      by_cases hcorebot : oddCore F = ⊥
      · -- ## `O_{2'}(F) = 1`: then `L` itself is a simple Bender group
        have hker : φ.ker = ⊥ := by
          rw [hφker, hcorebot]
          simp
        have hinj : Function.Injective φ := MonoidHom.ker_eq_bot_iff φ |>.mp hker
        have e : ↥L ≃* Y := MulEquiv.ofBijective φ ⟨hinj, hφsurj⟩
        have hLmodel : IsSimpleBenderGroup ↥L :=
          Work.Endgame.IsSimpleBenderGroup.of_mulEquiv hY e.symm
        have huL : u ∈ L := mem_of_orderOf_eq_two_of_odd_index hLidx hu2
        have hvL : v ∈ L := mem_of_orderOf_eq_two_of_odd_index hLidx hv2
        -- `L` is not contained in `H`
        have hnotle : ¬ L ≤ H := by
          intro hLH
          obtain ⟨g, hgH⟩ : ∃ g : F, g ∉ H := by
            by_contra h
            push_neg at h
            exact hH.1 (top_le_iff.mp (fun x _ => h x))
          have hLle : L ≤ H ⊓ conj g H := by
            refine le_inf hLH ?_
            intro x hx
            rw [mem_conj_iff]
            exact hLH (by simpa using hLnorm.conj_mem x hx g⁻¹)
          have hdvd : Nat.card ↥L ∣ Nat.card ↥(H ⊓ conj g H) :=
            Subgroup.card_dvd_of_le hLle
          have hodd : Odd (Nat.card ↥(H ⊓ conj g H)) := hH.2.2 g hgH
          -- `u ∈ L` has order `2`, so `L` has even order
          have h2dvd : 2 ∣ Nat.card ↥L := by
            have h1 := orderOf_dvd_natCard (⟨u, huL⟩ : ↥L)
            rwa [Subgroup.orderOf_mk u huL, hu2] at h1
          exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (dvd_trans h2dvd hdvd))
        have hM : IsStronglyEmbedded ((H ⊓ L).subgroupOf L) :=
          isStronglyEmbedded_inf_subgroupOf hH hLnorm hLidx hnotle
        have huM : (⟨u, huL⟩ : ↥L) ∈
            involutions (((H ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
          refine ⟨Subgroup.mem_subgroupOf.mpr ⟨huH, huL⟩, ?_⟩
          rw [Subgroup.orderOf_mk u huL]; exact hu2
        have hvM : (⟨v, hvL⟩ : ↥L) ∈
            involutions (((H ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
          refine ⟨Subgroup.mem_subgroupOf.mpr ⟨hvH, hvL⟩, ?_⟩
          rw [Subgroup.orderOf_mk v hvL]; exact hv2
        have hcomm : (⟨u, huL⟩ : ↥L) * (⟨v, hvL⟩ : ↥L) =
            (⟨v, hvL⟩ : ↥L) * (⟨u, huL⟩ : ↥L) :=
          ((hMod ↥L hLmodel).2.2.2 _ hM).1 _ huM _ hvM
        have huv : u * v = v * u := by
          simpa using congrArg Subtype.val hcomm
        have hvan : u * v * u⁻¹ * v⁻¹ = 1 := by rw [huv]; group
        rw [hcorebot, hvan]
        exact Subgroup.one_mem ⊥
      · -- ## `O_{2'}(F) ≠ 1`: descend to `F ⧸ O_{2'}(F)` and use the induction hypothesis
        have hNH : oddCore F ≤ H := oddCore_le_of_stronglyEmbedded hH hfour
        have hoddN : Odd (Nat.card (oddCore F)) := Work.BrauerSuzuki.OddCore.oddCard_oddCore
        have hHbar : IsStronglyEmbedded (H.map (QuotientGroup.mk' (oddCore F))) :=
          isStronglyEmbedded_map_quotient (oddCore F) hoddN hNH hH
        have hfourQ : HasFourGroup (F ⧸ oddCore F) :=
          hasFourGroup_quotient_odd hoddN hfour
        have hNcard : 2 ≤ Nat.card (oddCore F) :=
          (Subgroup.one_lt_card_iff_ne_bot _).mpr hcorebot
        have hmul : Nat.card (oddCore F) * (oddCore F).index = Nat.card F :=
          Subgroup.card_mul_index _
        have hidxpos : 0 < (oddCore F).index :=
          Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        have hQlt : Nat.card (F ⧸ oddCore F) < m := by
          rw [← Subgroup.index_eq_card (oddCore F), ← hcard]
          calc (oddCore F).index < 2 * (oddCore F).index := by omega
            _ ≤ Nat.card (oddCore F) * (oddCore F).index := Nat.mul_le_mul_right _ hNcard
            _ = Nat.card F := hmul
        have huQ : QuotientGroup.mk' (oddCore F) u ∈
            involutions (H.map (QuotientGroup.mk' (oddCore F)) : Set (F ⧸ oddCore F)) :=
          ⟨Subgroup.mem_map.mpr ⟨u, huH, rfl⟩, orderOf_mk'_eq_two hoddN hu2⟩
        have hvQ : QuotientGroup.mk' (oddCore F) v ∈
            involutions (H.map (QuotientGroup.mk' (oddCore F)) : Set (F ⧸ oddCore F)) :=
          ⟨Subgroup.mem_map.mpr ⟨v, hvH, rfl⟩, orderOf_mk'_eq_two hoddN hv2⟩
        have hih := ih (Nat.card (F ⧸ oddCore F)) hQlt (lt_trans hQlt hm)
          (F ⧸ oddCore F) rfl hfourQ hHbar huQ hvQ
        rw [oddCore_quotient_oddCore] at hih
        have hvan : QuotientGroup.mk' (oddCore F) u * QuotientGroup.mk' (oddCore F) v *
            (QuotientGroup.mk' (oddCore F) u)⁻¹ * (QuotientGroup.mk' (oddCore F) v)⁻¹ = 1 :=
          Subgroup.mem_bot.mp hih
        have hker : u * v * u⁻¹ * v⁻¹ ∈ (QuotientGroup.mk' (oddCore F)).ker := by
          rw [MonoidHom.mem_ker]
          show QuotientGroup.mk' (oddCore F) (u * v * u⁻¹ * v⁻¹) = 1
          simpa only [map_mul, map_inv] using hvan
        rwa [QuotientGroup.ker_mk'] at hker
  exact key (Nat.card F) hlt F rfl hfour hH hu hv

end Work.ThreePoints
