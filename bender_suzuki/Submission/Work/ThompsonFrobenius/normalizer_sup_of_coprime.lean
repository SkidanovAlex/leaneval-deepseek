import Mathlib
import Submission.Work.HallHigman.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Frattini: `N_G(A ⊔ U) = N_G(A) ⊔ U` for a normal `p'`-subgroup `U`

Auxiliary Frattini computation used in step GT-2 of Theorem D.  Let `U ⊴ G` have order coprime to
`p` and let `A` be a `p`-subgroup of `N_G(U)`.  Then `A ⊓ U = 1`, so `A` is a Sylow `p`-subgroup of
`M = A ⊔ U` (`|M : A| = |U|` is coprime to `p`), and Frattini's argument applied inside `N_G(M)`
gives `N_G(M) = N_G(A)·M = N_G(A) ⊔ U`.  The reverse inclusion is immediate, since `N_G(A)` and `U`
both normalise `M = A ⊔ U`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.ThompsonFrobenius

theorem normalizer_sup_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A U : Subgroup G} (hU : U.Normal) (hUcop : (Nat.card ↥U).Coprime p)
    (hA : IsPGroup p A) (hAnorm : A ≤ Subgroup.normalizer (U : Set G)) :
    Subgroup.normalizer ((A ⊔ U : Subgroup G) : Set G) = Subgroup.normalizer (A : Set G) ⊔ U := by
  haveI := hU
  have hAU_bot : A ⊓ U = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk]
    exact hUcop.symm.pow_left k
  have hcardM : Nat.card ↥(A ⊔ U) = Nat.card ↥A * Nat.card ↥U := by
    have h := Work.HallHigman.card_sup_mul_card_inf A U
    rw [hAU_bot, Subgroup.card_bot, mul_one] at h
    exact h
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · -- `N_G(A ⊔ U) ≤ N_G(A) ⊔ U`
    intro x hx
    set M : Subgroup G := A ⊔ U with hMdef
    set X : Subgroup G := Subgroup.normalizer (M : Set G) with hXdef
    have hxX : x ∈ X := hx
    have hM_le_X : M ≤ X := Subgroup.le_normalizer
    have hA_le_M : A ≤ M := le_sup_left
    have hA_le_X : A ≤ X := by
      have h1 : A ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (U : Set G) :=
        le_inf Subgroup.le_normalizer hAnorm
      exact h1.trans (Subgroup.inf_normalizer_le_normalizer_sup A U)
    haveI : (M.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hM_le_X).mpr (le_of_eq hXdef)
    let L : Subgroup ↥X := M.subgroupOf X
    let AL : Subgroup ↥L := (A.subgroupOf X).subgroupOf L
    have hle : A.subgroupOf X ≤ L := Subgroup.subgroupOf_mono X hA_le_M
    have hALp : IsPGroup p AL :=
      IsPGroup.of_equiv (IsPGroup.of_equiv hA (Subgroup.subgroupOfEquivOfLe hA_le_X).symm)
        (Subgroup.subgroupOfEquivOfLe hle).symm
    have hALcard : Nat.card ↥AL = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_X).toEquiv)
    have hmax : ∀ {Q : Subgroup ↥L}, IsPGroup p Q → AL ≤ Q → Q = AL := by
      intro Q hQ hQle
      have hQGp : IsPGroup p ((Q.map L.subtype).map X.subtype) :=
        IsPGroup.map (IsPGroup.map hQ L.subtype) X.subtype
      have hQGM : (Q.map L.subtype).map X.subtype ≤ M := by
        rintro y ⟨z, hz, rfl⟩
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
        exact w.2
      have hQcard : Nat.card ↥Q ≤ Nat.card ↥AL := by
        obtain ⟨m, hm⟩ := hQGp.exists_card_eq
        have hdvd : p ^ m ∣ Nat.card ↥A * Nat.card ↥U := by
          rw [← hm, ← hcardM]
          exact Subgroup.card_dvd_of_le hQGM
        have hdvd2 : p ^ m ∣ Nat.card ↥A :=
          (hUcop.symm.pow_left m).dvd_of_dvd_mul_left (by rw [mul_comm]; exact hdvd)
        obtain ⟨k, hk⟩ := hA.exists_card_eq
        have hcardQ : Nat.card ↥Q = p ^ m := by
          rw [← hm]
          exact (Subgroup.card_map_of_injective (f := L.subtype)
              L.subtype_injective).symm.trans
            (Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective).symm
        rw [hcardQ, hALcard]
        calc p ^ m ≤ p ^ k := by
              rw [hk] at hdvd2
              exact Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos k) hdvd2
          _ = Nat.card ↥A := hk.symm
      exact (Subgroup.eq_of_le_of_card_ge hQle hQcard).symm
    let S : Sylow p ↥L :=
      { AL with isPGroup' := hALp, is_maximal' := fun {Q} hQ hQle => hmax hQ hQle }
    have htop : Subgroup.normalizer ((S : Subgroup ↥L).map L.subtype) ⊔ L = ⊤ :=
      Sylow.normalizer_sup_eq_top S
    have hSmap : (S : Subgroup ↥L).map L.subtype = A.subgroupOf X :=
      Subgroup.map_subgroupOf_eq_of_le hle
    have hmem : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.normalizer ((S : Subgroup ↥L).map L.subtype) ⊔ L := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨l, hl, n, hn, hln⟩ := hmem
    have hlG : (l : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [hSmap, ← Subgroup.subgroupOf_normalizer_eq hA_le_X] at hl
      exact hl
    have hnM : (n : G) ∈ M := hn
    obtain ⟨a, ha, u, hu, hau⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := A) (t := U)).mp hnM
    have hlnG : (l : G) * (n : G) = x := congrArg Subtype.val hln
    refine (Subgroup.mem_sup_of_normal_right (s := Subgroup.normalizer (A : Set G))
      (t := U)).mpr ⟨(l : G) * a, ?_, u, hu, ?_⟩
    · exact (Subgroup.normalizer (A : Set G)).mul_mem hlG (Subgroup.le_normalizer ha)
    · rw [mul_assoc, hau, hlnG]
  · -- `N_G(A) ≤ N_G(A ⊔ U)`
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    have hgU : U.map (↑(MulAut.conj g)) = U := by
      have h : g ∈ Subgroup.normalizer (U : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hU]
        exact Subgroup.mem_top g
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp h
    rw [Subgroup.map_sup, hg, hgU]
  · -- `U ≤ N_G(A ⊔ U)`
    exact le_trans le_sup_right Subgroup.le_normalizer

end Work.ThompsonFrobenius
