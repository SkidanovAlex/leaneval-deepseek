import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.ncard_involutions_eq_index
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE3.BCountSum
import Submission.Work.CORE3.SumMulBCount
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.Dihedral.Defs

open Work.GW2

namespace Work.CORE3

/-- An element of odd order with `u ^ 2 = 1` is trivial. -/
private lemma eq_one_of_mem_of_sq_eq_one {G : Type*} [Group G] {U : Subgroup G}
    (hodd : Odd (Nat.card U)) {u : G} (hu : u ∈ U) (h : u ^ 2 = 1) : u = 1 := by
  by_contra hne
  have hne' : (⟨u, hu⟩ : ↥U) ≠ 1 := fun hh => hne (by simpa using congrArg Subtype.val hh)
  have h2 : orderOf (⟨u, hu⟩ : ↥U) = 2 := by
    refine orderOf_eq_prime ?_ hne'
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h
  have hdvd : orderOf (⟨u, hu⟩ : ↥U) ∣ Nat.card ↥U := orderOf_dvd_natCard _
  rw [h2] at hdvd
  exact hodd.not_two_dvd_nat hdvd

/-- `u = u⁻¹` in a group of odd order forces `u = 1`. -/
private lemma eq_one_of_eq_inv_of_odd {G : Type*} [Group G] {U : Subgroup G}
    (hodd : Odd (Nat.card U)) {u : G} (hu : u ∈ U) (h : u = u⁻¹) : u = 1 := by
  refine eq_one_of_mem_of_sq_eq_one hodd hu ?_
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel u

/-- A minimal counterexample has `|G| ≠ 2`. -/
private lemma card_G_ne_two {G : Type} [Group G] [Finite G] (B : BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) :
    Nat.card G ≠ 2 := by
  obtain ⟨e⟩ := hdih
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hle : Nat.card (B.S : Subgroup G) ≤ Nat.card G := Subgroup.card_le_card_group _
  rw [hcardS] at hle
  omega

/-- A simple group of order `≠ 2` has no normal subgroup of index `2`. -/
private lemma no_normal_index_two {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : Nat.card G ≠ 2) : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hIdx
  have hbot : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot] at hIdx
    exact hcard hIdx
  have htop : N ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hIdx
    omega
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple N hN with h | h
  · exact hbot h
  · exact htop h

section STRUCT

variable {G : Type} [Group G] [Finite G]

/-- Bender 1981 §3: an involution of `H = C_G(t)` different from `t` is `u · ρ` with `u ∈ U` and
`ρ` a reflection of `S` inverting `u` (via `ρ u ρ⁻¹ = u⁻¹`). -/
private lemma H_inv_form (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) {x : G}
    (hxH : x ∈ B.H) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxne : x ≠ B.t) :
    ∃ u ∈ B.U, ∃ ρ ∈ (B.S : Subgroup G), ρ ∉ B.S0 ∧ x = u * ρ ∧ ρ * u * ρ⁻¹ = u⁻¹ := by
  have hUS : B.U ⊓ (B.S : Subgroup G) = ⊥ := Work.CORE2A.inf_U_S_eq_bot B
  have hH : B.U ⊔ (B.S : Subgroup G) = B.H := H_eq_U_sup_S G I.T hBc B
  have hUleH : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have hSleH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [Work.CORE2A.bSetup_U_eq B]
    exact Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H)
  have hSN : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := hSleH.trans hHN
  have hUnorm : ((B.U).subgroupOf B.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have hdec : ∀ y ∈ B.H, ∃ u ∈ B.U, ∃ σ ∈ (B.S : Subgroup G), u * σ = y :=
    Work.CORE2A.exists_mul_of_mem_sup_of_normal hUleH hSleH hUnorm hH
  obtain ⟨u, hu, σ, hσ, hux⟩ := hdec x hxH
  have hfac : u * σ * (u * σ) = u * (σ * u * σ⁻¹) * σ ^ 2 := by group
  have hmul : u * (σ * u * σ⁻¹) * σ ^ 2 = 1 := by rw [← hfac, hux, hx2]
  have hconjU : σ * u * σ⁻¹ ∈ B.U := (Subgroup.mem_normalizer_iff.mp (hSN hσ) u).mp hu
  have hA : u * (σ * u * σ⁻¹) ∈ B.U := B.U.mul_mem hu hconjU
  have hprod : u * (σ * u * σ⁻¹) = (σ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hmem : u * (σ * u * σ⁻¹) ∈ B.U ⊓ (B.S : Subgroup G) :=
    ⟨hA, by rw [hprod]; exact (B.S).inv_mem ((B.S).pow_mem hσ 2)⟩
  rw [hUS] at hmem
  have h1' : u * (σ * u * σ⁻¹) = 1 := Subgroup.mem_bot.mp hmem
  have hs2 : σ ^ 2 = 1 := by rw [h1', one_mul] at hmul; exact hmul
  have hu_inv : σ * u * σ⁻¹ = u⁻¹ := eq_inv_of_mul_eq_one_right h1'
  by_cases hσS0 : σ ∈ B.S0
  · exfalso
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have ha : (⟨σ, hσS0⟩ : ↥B.S0) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hs2
    have hb : (⟨B.t, B.t_mem⟩ : ↥B.S0) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← B.t_order]
      exact pow_orderOf_eq_one B.t
    rcases eq_or_ne (⟨σ, hσS0⟩ : ↥B.S0) 1 with hσ1 | hσ1
    · have hσ1' : σ = 1 := by simpa using congrArg Subtype.val hσ1
      have hxu : x = u := by rw [← hux, hσ1', mul_one]
      have huu : u ^ 2 = 1 := by rw [pow_two, ← hxu, hx2]
      exact hx1 (by rw [hxu]; exact eq_one_of_mem_of_sq_eq_one hUodd hu huu)
    · have hb1 : (⟨B.t, B.t_mem⟩ : ↥B.S0) ≠ 1 :=
        fun h => Work.CORE2A.bSetup_t_ne_one B (by simpa using congrArg Subtype.val h)
      have hσt : σ = B.t :=
        congrArg Subtype.val (Work.CORE2A.eq_of_sq_eq_one_of_isCyclic ha hb hσ1 hb1)
      have hut : B.t * u * B.t⁻¹ = u := by
        rw [show B.t * u = u * B.t from
          Subgroup.mem_centralizer_iff.mp (hUleH hu) B.t (Set.mem_singleton B.t)]
        group
      have hu_inv' : u = u⁻¹ := by rw [hσt, hut] at hu_inv; exact hu_inv
      have hu1 : u = 1 := eq_one_of_eq_inv_of_odd hUodd hu hu_inv'
      exact hxne (by rw [← hux, hσt, hu1, one_mul])
  · exact ⟨u, hu, σ, hσ, hσS0, hux.symm, hu_inv⟩

end STRUCT

end Work.CORE3

namespace Work.CORE3

section AUX

variable {G : Type} [Finite G]

private lemma ncard_four' (a b c d : G) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Set G).ncard = 4 := by
  have h1 : ({a, b, c, d} : Set G) = insert a (insert b (insert c {d})) := rfl
  rw [h1, Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
    Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
    Set.ncard_insert_of_notMem (by simpa using hcd), Set.ncard_singleton]

end AUX

end Work.CORE3

namespace Work.CORE3

section MAIN

variable {G : Type} [Group G] [Finite G]

theorem invCountHhat_aux (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G)
    (_h1 : Case1 B) (D : Case1bData B)
    (hH : (involutionSet B.H).ncard = 3 + 2 * Nat.card D.K) :
    (involutionSet B.Hhat).ncard = 3 + 6 * Nat.card D.K := by
  classical
  obtain ⟨_hOC, hSC, _hdisj2⟩ := I.h26 G I.T.ft hBc B
  have hV4 : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  obtain ⟨nsy, hnsy2, hdihsy⟩ := SylowDihedral G hBc B
  have hOutside := OutsideS0OrderTwo G hBc B nsy hnsy2 hdihsy
  have hVS : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by rw [← hSC]; exact inf_le_left
  have hVCU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← hSC]; exact inf_le_right
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hVleHhat : pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have htHhat : B.t ∈ B.Hhat := Work.CORE2A.bSetup_t_mem_Hhat B
  have htne : B.t ≠ 1 := Work.CORE2A.bSetup_t_ne_one B
  have hVncard : (pCoreIn 2 B.Hhat : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hV4.1
  -- commutativity inside `V`
  have hVcomm : ∀ x ∈ (pCoreIn 2 B.Hhat : Set G), ∀ y ∈ (pCoreIn 2 B.Hhat : Set G),
      x * y = y * x := by
    intro x hx y hy
    have hxy : x * y * (x * y) = 1 := by
      simpa [pow_two] using hV4.2 (x * y) ((pCoreIn 2 B.Hhat).mul_mem hx hy)
    have hy2 : y * y = 1 := by simpa [pow_two] using hV4.2 y hy
    have hx2 : x * x = 1 := by simpa [pow_two] using hV4.2 x hx
    have h1 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right hxy
    calc x * y = (x * y)⁻¹ := h1
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_left hy2, inv_eq_of_mul_eq_one_left hx2]
  -- `t ∈ V`
  have htV : B.t ∈ pCoreIn 2 B.Hhat := by
    rw [← hSC, Subgroup.mem_inf]
    exact ⟨Work.CORE2A.bSetup_t_mem_S B, Subgroup.mem_centralizer_iff.mpr (fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_U_le_H B hu) B.t
        (Set.mem_singleton B.t)).symm)⟩
  -- `V ∩ S₀ = {1, t}`
  have hcap : ∀ x : G, x ∈ (pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G) ↔ x = 1 ∨ x = B.t := by
    intro x
    constructor
    · rintro ⟨hxV, hxS0⟩
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · refine Or.inr ?_
        haveI : IsCyclic ↥B.S0 := B.S0_cyclic
        have ha : (⟨x, hxS0⟩ : ↥B.S0) ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hV4.2 x hxV
        have hb : (⟨B.t, B.t_mem⟩ : ↥B.S0) ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one, ← B.t_order]
          exact pow_orderOf_eq_one B.t
        have ha1 : (⟨x, hxS0⟩ : ↥B.S0) ≠ 1 := fun h => hx1 (by simpa using congrArg Subtype.val h)
        have hb1 : (⟨B.t, B.t_mem⟩ : ↥B.S0) ≠ 1 :=
          fun h => htne (by simpa using congrArg Subtype.val h)
        exact congrArg Subtype.val (Work.CORE2A.eq_of_sq_eq_one_of_isCyclic ha hb ha1 hb1)
    · rintro (rfl | rfl)
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨htV, B.t_mem⟩
  have hcapcard : ((pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G)).ncard = 2 := by
    rw [show (pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G) = ({1, B.t} : Set G) from by
      ext x; rw [hcap x]; simp]
    exact Set.ncard_pair (fun h => htne h.symm)
  -- an element of `V` outside `S₀`
  have hv1ex : ((pCoreIn 2 B.Hhat : Set G) \ (B.S0 : Set G)).Nonempty := by
    have hsub : ((pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G)) ⊆ (pCoreIn 2 B.Hhat : Set G) :=
      Set.inter_subset_left
    have heq : (pCoreIn 2 B.Hhat : Set G) \ (B.S0 : Set G)
        = (pCoreIn 2 B.Hhat : Set G) \ ((pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G)) := by
      ext x; constructor
      · rintro ⟨hxV, hxS0⟩; exact ⟨hxV, fun h => hxS0 h.2⟩
      · rintro ⟨hxV, h⟩; exact ⟨hxV, fun hxS0 => h ⟨hxV, hxS0⟩⟩
    have hncard : ((pCoreIn 2 B.Hhat : Set G) \ (B.S0 : Set G)).ncard = 2 := by
      rw [heq]
      have h := Set.ncard_sdiff hsub (Set.toFinite _)
      rw [hVncard, hcapcard] at h
      exact h
    rw [← Set.ncard_pos, hncard]
    norm_num
  obtain ⟨v1, hv1V, hv1S0⟩ := hv1ex
  have hv1sq : v1 * v1 = 1 := by simpa [pow_two] using hV4.2 v1 hv1V
  have hv1ne1 : v1 ≠ 1 := fun h => hv1S0 (h ▸ B.S0.one_mem)
  have hv1neT : v1 ≠ B.t := fun h => hv1S0 (h ▸ B.t_mem)
  have hv2V : B.t * v1 ∈ pCoreIn 2 B.Hhat := (pCoreIn 2 B.Hhat).mul_mem htV hv1V
  have hv2ne1 : B.t * v1 ≠ 1 := fun h =>
    hv1neT ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_left hv1sq)).symm
  have hv2neT : B.t * v1 ≠ B.t := fun h => hv1ne1 (by
    have hh : B.t * v1 = B.t * 1 := by rwa [mul_one]
    exact mul_left_cancel hh)
  have hv2neV1 : B.t * v1 ≠ v1 := fun h => htne (by
    have hh : B.t * v1 = 1 * v1 := by rwa [one_mul]
    exact mul_right_cancel hh)
  -- `V = {1, t, v1, t v1}`
  have hVsub : ({1, B.t, v1, B.t * v1} : Set G) ⊆ (pCoreIn 2 B.Hhat : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact htV
    · rw [h]; exact hv1V
    · rw [h]; exact hv2V
  have hfour_card : ({1, B.t, v1, B.t * v1} : Set G).ncard = 4 :=
    ncard_four' 1 B.t v1 (B.t * v1) (fun h => htne h.symm) (fun h => hv1ne1 h.symm)
      (fun h => hv2ne1 h.symm) hv1neT.symm (fun h => hv2neT h.symm) hv2neV1.symm
  have hVset : (pCoreIn 2 B.Hhat : Set G) = ({1, B.t, v1, B.t * v1} : Set G) :=
    (Set.eq_of_subset_of_ncard_le hVsub (by rw [hVncard, hfour_card])).symm
  have hmemV : ∀ w ∈ (pCoreIn 2 B.Hhat : Set G), w ≠ 1 →
      w = B.t ∨ w = v1 ∨ w = B.t * v1 := by
    intro w hw hw1
    have h := hVset ▸ hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    tauto
  have htV' : B.t ∈ ({1, B.t, v1, B.t * v1} : Set G) := by simp
  have hv1V' : v1 ∈ ({1, B.t, v1, B.t * v1} : Set G) := by simp
  have hv2V' : B.t * v1 ∈ ({1, B.t, v1, B.t * v1} : Set G) := by simp

  -- ===== involutions centralizing `V` lie in `V` =====
  have hKinv : ∀ x : G, x ∈ B.Hhat → (∀ y ∈ (pCoreIn 2 B.Hhat : Set G), y * x = x * y) →
      x * x = 1 → x ∈ pCoreIn 2 B.Hhat := by
    intro x hxHhat hxC hx2
    have hxH : x ∈ B.H := by
      rw [Work.CORE2A.bSetup_H_eq B, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxC B.t htV
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    by_cases hxt : x = B.t
    · rw [hxt]; exact htV
    obtain ⟨u, hu, ρ, hρS, hρS0, hxu, _hρu⟩ := H_inv_form I hBc B hxH hx2 hx1 hxt
    have hρC : ∀ y ∈ (pCoreIn 2 B.Hhat : Set G), y * ρ = ρ * y := by
      intro y hy
      have hyu : u * y = y * u := (Subgroup.mem_centralizer_iff.mp (hVCU hy)) u hu
      have hyx : y * x = x * y := hxC y hy
      have h1 : y * (u * ρ) = (u * ρ) * y := by rw [← hxu]; exact hyx
      have h3 : u * (y * ρ) = u * (ρ * y) := by
        calc u * (y * ρ) = u * y * ρ := by group
          _ = y * u * ρ := by rw [hyu]
          _ = y * (u * ρ) := by group
          _ = (u * ρ) * y := h1
          _ = u * (ρ * y) := by group
      exact mul_left_cancel h3
    have hρsq : ρ * ρ = 1 := by
      rw [← pow_two, ← hOutside ρ hρS hρS0]
      exact pow_orderOf_eq_one ρ
    have hρv1C : v1 * ρ = ρ * v1 := hρC v1 hv1V
    have hρv1sq : (ρ * v1) * (ρ * v1) = 1 := by
      calc (ρ * v1) * (ρ * v1) = ρ * (v1 * ρ) * v1 := by group
        _ = ρ * (ρ * v1) * v1 := by rw [hρv1C]
        _ = ρ * ρ * (v1 * v1) := by group
        _ = 1 := by rw [hρsq, hv1sq, mul_one]
    have hρv1S0 : ρ * v1 ∈ B.S0 := by
      have hidx : (B.S0.subgroupOf (B.S : Subgroup G)).index = 2 := B.S0_index
      have hiff := Subgroup.mul_mem_iff_of_index_two
        (H := B.S0.subgroupOf (B.S : Subgroup G)) hidx
        (a := (⟨ρ, hρS⟩ : ↥(B.S : Subgroup G))) (b := (⟨v1, hVS hv1V⟩ : ↥(B.S : Subgroup G)))
      have hmem : (⟨ρ, hρS⟩ * ⟨v1, hVS hv1V⟩ : ↥(B.S : Subgroup G)) ∈
          B.S0.subgroupOf (B.S : Subgroup G) :=
        hiff.mpr ⟨fun ha => absurd (Subgroup.mem_subgroupOf.mp ha) hρS0,
          fun hb => absurd (Subgroup.mem_subgroupOf.mp hb) hv1S0⟩
      simpa [Subgroup.mem_subgroupOf] using hmem
    have hρV : ρ ∈ pCoreIn 2 B.Hhat := by
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      have ha : (⟨ρ * v1, hρv1S0⟩ : ↥B.S0) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [Subgroup.coe_pow, pow_two] using hρv1sq
      have hb : (⟨B.t, B.t_mem⟩ : ↥B.S0) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← B.t_order]
        exact pow_orderOf_eq_one B.t
      rcases eq_or_ne (⟨ρ * v1, hρv1S0⟩ : ↥B.S0) 1 with h0 | h0
      · have h0' : ρ * v1 = 1 := by simpa using congrArg Subtype.val h0
        have hρeq : ρ = v1 := by
          have hh : ρ * v1 * v1 = 1 * v1 := by rw [h0', one_mul]
          simpa [mul_assoc, hv1sq] using hh
        rw [hρeq]; exact hv1V
      · have hb1 : (⟨B.t, B.t_mem⟩ : ↥B.S0) ≠ 1 :=
          fun h => htne (by simpa using congrArg Subtype.val h)
        have h0' : ρ * v1 = B.t :=
          congrArg Subtype.val (Work.CORE2A.eq_of_sq_eq_one_of_isCyclic ha hb h0 hb1)
        have hρeq : ρ = B.t * v1 := by
          have hh : ρ * v1 * v1 = B.t * v1 := by rw [h0']
          simpa [mul_assoc, hv1sq] using hh
        rw [hρeq]; exact hv2V
    have hρuC : u * ρ = ρ * u := (Subgroup.mem_centralizer_iff.mp (hVCU hρV)) u hu
    have huu : u ^ 2 = 1 := by
      rw [pow_two]
      have h1 : u * ρ * (u * ρ) = u * u := by
        rw [show u * ρ * (u * ρ) = u * (ρ * u * ρ⁻¹) * (ρ * ρ) from by group,
          show ρ * u * ρ⁻¹ = u from by rw [← hρuC]; group, hρsq]
        group
      rw [← h1, ← hxu]; exact hx2
    have hu1 : u = 1 := eq_one_of_mem_of_sq_eq_one hUodd hu huu
    rw [show x = ρ from by rw [hxu, hu1, one_mul]]
    exact hρV
  -- ===== the involutions centralizing `V` are exactly `V \ {1}` =====
  have hA0set : involutionSet (B.Hhat ⊓ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Set G)))
      = (pCoreIn 2 B.Hhat : Set G) \ {1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxK, hxo⟩ := hx
      obtain ⟨hxHhat, hxC⟩ := hxK
      have hx2 : x * x = 1 := by rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one x
      have hx1 : x ≠ 1 := by
        intro h; rw [h, orderOf_one] at hxo; exact absurd hxo (by norm_num)
      exact ⟨hKinv x hxHhat (fun y hy => hxC y hy) hx2, hx1⟩
    · rintro ⟨hxV, hx1⟩
      refine ⟨⟨hVleHhat hxV, ?_⟩, ?_⟩
      · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hVcomm x hxV y hy).symm)
      · exact orderOf_eq_prime (by simpa [pow_two] using hV4.2 x hxV) hx1
  have hA0card : (involutionSet (B.Hhat ⊓ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Set G)))).ncard = 3 := by
    rw [hA0set]
    have hsub : ({(1 : G)} : Set G) ⊆ (pCoreIn 2 B.Hhat : Set G) := by
      intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact one_mem _
    have h := Set.ncard_sdiff hsub (Set.toFinite _)
    rw [hVncard, Set.ncard_singleton] at h
    exact h
  -- ===== conjugates of `H` =====
  have hCwcard : ∀ w ∈ (pCoreIn 2 B.Hhat : Set G), w ≠ 1 →
      (involutionSet (B.Hhat ⊓ Subgroup.centralizer ({w} : Set G))).ncard
        = 3 + 2 * Nat.card D.K := by
    intro w hwV hw1
    obtain ⟨n2, hn2', hdih⟩ := SylowDihedral G hBc B
    have hNoIdx := no_normal_index_two hBc.simple (card_G_ne_two B n2 hn2' hdih)
    have hfus := (I.T.fus G B.S n2 hn2' hdih hNoIdx).2
    obtain ⟨g, hgN, hgt⟩ := hfus (pCoreIn 2 B.Hhat) D.four B.t htV w hwV
      (Work.CORE2A.bSetup_t_ne_one B) hw1
    have hgHhat : g ∈ B.Hhat := by
      rw [← Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
      exact hgN
    have hmain : (involutionSet (B.Hhat ⊓ Subgroup.centralizer ({w} : Set G))).ncard
        = (involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G))).ncard := by
      refine Set.ncard_congr (fun x _ => g⁻¹ * x * g) ?_ ?_ ?_
      · rintro x ⟨hxK, hxo⟩
        obtain ⟨hxHhat, hxC⟩ := hxK
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact B.Hhat.mul_mem (B.Hhat.mul_mem (B.Hhat.inv_mem hgHhat) hxHhat) hgHhat
        · refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          have hx' : w * x = x * w :=
            Subgroup.mem_centralizer_iff.mp hxC w (Set.mem_singleton w)
          have hgti : g⁻¹ * w * g = B.t := by rw [← hgt]; group
          calc B.t * (g⁻¹ * x * g) = (g⁻¹ * w * g) * (g⁻¹ * x * g) := by rw [hgti]
            _ = g⁻¹ * (w * x) * g := by group
            _ = g⁻¹ * (x * w) * g := by rw [hx']
            _ = (g⁻¹ * x * g) * (g⁻¹ * w * g) := by group
            _ = (g⁻¹ * x * g) * B.t := by rw [hgti]
        · have h1 : g⁻¹ * x * g = (MulAut.conj g⁻¹) x := by rw [MulAut.conj_apply]; group
          rw [h1, MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x]; exact hxo
      · rintro x y _ _ hxy
        exact mul_left_cancel (mul_right_cancel hxy)
      · rintro y ⟨hyK, hyo⟩
        obtain ⟨hyHhat, hyC⟩ := hyK
        refine ⟨g * y * g⁻¹, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · exact B.Hhat.mul_mem (B.Hhat.mul_mem hgHhat hyHhat) (B.Hhat.inv_mem hgHhat)
        · refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          have hy' : B.t * y = y * B.t :=
            Subgroup.mem_centralizer_iff.mp hyC B.t (Set.mem_singleton B.t)
          calc w * (g * y * g⁻¹) = (g * B.t * g⁻¹) * (g * y * g⁻¹) := by rw [hgt]
            _ = g * (B.t * y) * g⁻¹ := by group
            _ = g * (y * B.t) * g⁻¹ := by rw [hy']
            _ = (g * y * g⁻¹) * (g * B.t * g⁻¹) := by group
            _ = (g * y * g⁻¹) * w := by rw [hgt]
        · have h1 : (MulAut.conj g) y = g * y * g⁻¹ := by rw [MulAut.conj_apply]
          rw [← h1, MulEquiv.orderOf_eq (MulAut.conj g) y]; exact hyo
        · show g⁻¹ * (g * y * g⁻¹) * g = y
          group
    rw [hmain]
    have hHt : B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G) = B.H :=
      inf_eq_right.mpr B.H_le_Hhat
    rw [hHt]; exact hH

  -- ===== the final count =====
  have hCt1 : Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.centralizer ({v1} : Set G)
      ≤ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Set G)) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : B.t * z = z * B.t := Subgroup.mem_centralizer_iff.mp hz1 B.t (Set.mem_singleton B.t)
    have hz2' : v1 * z = z * v1 := Subgroup.mem_centralizer_iff.mp hz2 v1 (Set.mem_singleton v1)
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    rw [hVset] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]; exact hz1'
    · rw [h]; exact hz2'
    · rw [h]
      calc B.t * v1 * z = B.t * (v1 * z) := by group
        _ = B.t * (z * v1) := by rw [hz2']
        _ = (B.t * z) * v1 := by group
        _ = (z * B.t) * v1 := by rw [hz1']
        _ = z * (B.t * v1) := by group
  have hCt2 : Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.centralizer ({B.t * v1} : Set G)
      ≤ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Set G)) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : B.t * z = z * B.t := Subgroup.mem_centralizer_iff.mp hz1 B.t (Set.mem_singleton B.t)
    have hz2' : z * (B.t * v1) = B.t * v1 * z :=
      (Subgroup.mem_centralizer_iff.mp hz2 (B.t * v1) (Set.mem_singleton (B.t * v1))).symm
    have hzv1 : v1 * z = z * v1 := by
      have h2 : B.t * (z * v1) = B.t * (v1 * z) := by
        calc B.t * (z * v1) = (z * B.t) * v1 := by rw [← hz1']; group
          _ = z * (B.t * v1) := by group
          _ = (B.t * v1) * z := hz2'
          _ = B.t * (v1 * z) := by group
      exact (mul_left_cancel h2).symm
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    rw [hVset] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]; exact hz1'
    · rw [h]; exact hzv1
    · rw [h]; exact hz2'.symm
  have hC12 : Subgroup.centralizer ({v1} : Set G) ⊓ Subgroup.centralizer ({B.t * v1} : Set G)
      ≤ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Set G)) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : v1 * z = z * v1 := Subgroup.mem_centralizer_iff.mp hz1 v1 (Set.mem_singleton v1)
    have hz2' : z * (B.t * v1) = B.t * v1 * z :=
      (Subgroup.mem_centralizer_iff.mp hz2 (B.t * v1) (Set.mem_singleton (B.t * v1))).symm
    have hzt : B.t * z = z * B.t := by
      have h2 : z * B.t * v1 = B.t * z * v1 := by
        calc z * B.t * v1 = z * (B.t * v1) := by group
          _ = (B.t * v1) * z := hz2'
          _ = B.t * (v1 * z) := by group
          _ = B.t * (z * v1) := by rw [hz1']
          _ = B.t * z * v1 := by group
      exact (mul_right_cancel h2).symm
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    rw [hVset] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]; exact hzt
    · rw [h]; exact hz1'
    · rw [h]; exact hz2'.symm
  have hcount : (involutionSet B.Hhat).ncard = 3 + 6 * Nat.card D.K := by
    set A0 : Set G := involutionSet (B.Hhat ⊓ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Set G)))
      with hA0def
    set Bt : Set G := involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) \ A0
      with hBtdef
    set B1 : Set G := involutionSet (B.Hhat ⊓ Subgroup.centralizer ({v1} : Set G)) \ A0
      with hB1def
    set B2 : Set G := involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t * v1} : Set G)) \ A0
      with hB2def
    have hA0n : A0.ncard = 3 := by rw [hA0def]; exact hA0card
    have hBt_sub : A0 ⊆ involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) := by
      rw [hA0def]
      refine Work.CORE2A.involutionSet_mono ?_
      refine inf_le_inf_left _ ?_
      exact Subgroup.centralizer_le (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]; exact htV)
    have hB1_sub : A0 ⊆ involutionSet (B.Hhat ⊓ Subgroup.centralizer ({v1} : Set G)) := by
      rw [hA0def]
      refine Work.CORE2A.involutionSet_mono ?_
      refine inf_le_inf_left _ ?_
      exact Subgroup.centralizer_le (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hv1V)
    have hB2_sub : A0 ⊆ involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t * v1} : Set G)) := by
      rw [hA0def]
      refine Work.CORE2A.involutionSet_mono ?_
      refine inf_le_inf_left _ ?_
      exact Subgroup.centralizer_le (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hv2V)
    have hBtn : Bt.ncard = 2 * Nat.card D.K := by
      rw [hBtdef, Set.ncard_sdiff hBt_sub (Set.toFinite _),
        show (involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G))).ncard
            = 3 + 2 * Nat.card D.K from hCwcard B.t htV htne, hA0n]
      omega
    have hB1n : B1.ncard = 2 * Nat.card D.K := by
      rw [hB1def, Set.ncard_sdiff hB1_sub (Set.toFinite _),
        show (involutionSet (B.Hhat ⊓ Subgroup.centralizer ({v1} : Set G))).ncard
            = 3 + 2 * Nat.card D.K from hCwcard v1 hv1V hv1ne1, hA0n]
      omega
    have hB2n : B2.ncard = 2 * Nat.card D.K := by
      rw [hB2def, Set.ncard_sdiff hB2_sub (Set.toFinite _),
        show (involutionSet (B.Hhat ⊓ Subgroup.centralizer ({B.t * v1} : Set G))).ncard
            = 3 + 2 * Nat.card D.K from hCwcard (B.t * v1) hv2V hv2ne1, hA0n]
      omega
    have hUn : involutionSet B.Hhat = A0 ∪ (Bt ∪ (B1 ∪ B2)) := by
      ext x
      constructor
      · intro hx
        by_cases hxA : x ∈ A0
        · exact Or.inl hxA
        · have hxHhat : x ∈ B.Hhat := hx.1
          have hxo : orderOf x = 2 := hx.2
          have hx2 : x * x = 1 := by rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one x
          have hxN : x ∈ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Set G)) := by
            rw [Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]; exact hxHhat
          have hconjV : ∀ y ∈ (pCoreIn 2 B.Hhat : Set G),
              x * y * x⁻¹ ∈ (pCoreIn 2 B.Hhat : Set G) := fun y hy =>
            (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
          have hwV : B.t * (x * B.t * x⁻¹) ∈ (pCoreIn 2 B.Hhat : Set G) :=
            (pCoreIn 2 B.Hhat).mul_mem htV (hconjV B.t htV)
          have hxw : x * (B.t * (x * B.t * x⁻¹)) * x⁻¹ = B.t * (x * B.t * x⁻¹) := by
            have hx2' : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
            calc x * (B.t * (x * B.t * x⁻¹)) * x⁻¹
                = (x * B.t * x⁻¹) * (x * (x * B.t * x⁻¹) * x⁻¹) := by group
              _ = (x * B.t * x⁻¹) * B.t := by
                    rw [show x * (x * B.t * x⁻¹) * x⁻¹ = B.t from by
                      rw [show x * (x * B.t * x⁻¹) * x⁻¹
                          = (x * x) * B.t * (x⁻¹ * x⁻¹) from by group,
                        hx2, hx2', hx2, one_mul, mul_one]]
              _ = B.t * (x * B.t * x⁻¹) := hVcomm (x * B.t * x⁻¹) (hconjV B.t htV) B.t htV
          have hxw' : (B.t * (x * B.t * x⁻¹)) * x = x * (B.t * (x * B.t * x⁻¹)) := by
            have h2 : x * (B.t * (x * B.t * x⁻¹)) = (B.t * (x * B.t * x⁻¹)) * x := by
              simpa [mul_assoc] using congrArg (fun y => y * x) hxw
            exact h2.symm
          have hxCw : ∀ w : G, w = B.t * (x * B.t * x⁻¹) →
              x ∈ Subgroup.centralizer ({w} : Set G) := by
            intro w hw
            refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
            rw [Set.mem_singleton_iff] at hz
            rw [hz, hw]
            exact hxw'
          by_cases hw1 : B.t * (x * B.t * x⁻¹) = 1
          · have h2 : x * B.t * x⁻¹ = B.t := by
              have h3 := congrArg (fun y => B.t⁻¹ * y) hw1
              have ht2 : B.t * B.t = 1 := by
                rw [← pow_two, ← B.t_order]; exact pow_orderOf_eq_one B.t
              have h4 : x * B.t * x⁻¹ = B.t⁻¹ := by simpa [mul_assoc] using h3
              rw [h4, inv_eq_of_mul_eq_one_left ht2]
            have hxtC : x ∈ Subgroup.centralizer ({B.t} : Set G) := by
              refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
              rw [Set.mem_singleton_iff] at hz
              rw [hz]
              have h4 : (x * B.t * x⁻¹) * x = B.t * x := by rw [h2]
              have h6 : x * B.t = B.t * x := by simpa [mul_assoc] using h4
              exact h6.symm
            exact Or.inr (Or.inl (by
              rw [hBtdef]
              exact ⟨⟨⟨hxHhat, hxtC⟩, hxo⟩, hxA⟩))
          · rcases hmemV (B.t * (x * B.t * x⁻¹)) hwV hw1 with h | h | h
            · exact Or.inr (Or.inl (by
                rw [hBtdef]
                exact ⟨⟨⟨hxHhat, hxCw _ h.symm⟩, hxo⟩, hxA⟩))
            · exact Or.inr (Or.inr (Or.inl (by
                rw [hB1def]
                exact ⟨⟨⟨hxHhat, hxCw _ h.symm⟩, hxo⟩, hxA⟩)))
            · exact Or.inr (Or.inr (Or.inr (by
                rw [hB2def]
                exact ⟨⟨⟨hxHhat, hxCw _ h.symm⟩, hxo⟩, hxA⟩)))
      · rintro (hxA | hxt | hx1 | hx2)
        · rw [hA0def] at hxA
          exact ⟨hxA.1.1, hxA.2⟩
        · rw [hBtdef] at hxt
          exact ⟨hxt.1.1.1, hxt.1.2⟩
        · rw [hB1def] at hx1
          exact ⟨hx1.1.1.1, hx1.1.2⟩
        · rw [hB2def] at hx2
          exact ⟨hx2.1.1.1, hx2.1.2⟩
    have hd0 : Disjoint A0 (Bt ∪ (B1 ∪ B2)) := by
      rw [Set.disjoint_left]
      rintro x hxA (h | h | h)
      · rw [hBtdef] at h; exact h.2 hxA
      · rw [hB1def] at h; exact h.2 hxA
      · rw [hB2def] at h; exact h.2 hxA
    have hd1 : Disjoint Bt (B1 ∪ B2) := by
      rw [Set.disjoint_left]
      rintro x hxt (h | h)
      · rw [hBtdef] at hxt; rw [hB1def] at h
        exact hxt.2 (by rw [hA0def]; exact ⟨⟨hxt.1.1.1, hCt1 ⟨hxt.1.1.2, h.1.1.2⟩⟩, hxt.1.2⟩)
      · rw [hBtdef] at hxt; rw [hB2def] at h
        exact hxt.2 (by rw [hA0def]; exact ⟨⟨hxt.1.1.1, hCt2 ⟨hxt.1.1.2, h.1.1.2⟩⟩, hxt.1.2⟩)
    have hd2 : Disjoint B1 B2 := by
      rw [Set.disjoint_left]
      rintro x hx1 hx2
      rw [hB1def] at hx1; rw [hB2def] at hx2
      exact hx1.2 (by rw [hA0def]; exact ⟨⟨hx1.1.1.1, hC12 ⟨hx1.1.1.2, hx2.1.1.2⟩⟩, hx1.1.2⟩)
    rw [hUn, Set.ncard_union_eq hd0 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _), hA0n, hBtn, hB1n, hB2n]
    ring
  rw [hcount]


theorem invCountH_aux {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (hBc : BenderCtx G) (B : BenderSetup G) (_h1 : Case1 B) (D : Case1bData B) :
    (involutionSet B.H).ncard = 3 + 2 * Nat.card D.K := by
  classical
  -- ===== 0.  Theorem 2.6 and elementary structure =====
  obtain ⟨_hOC, hSC, _hdisj⟩ := I.h26 G I.T.ft hBc B
  have hV4 : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  have hVS : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by rw [← hSC]; exact inf_le_left
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← hSC]; exact inf_le_right
  have hUS : B.U ⊓ (B.S : Subgroup G) = ⊥ := Work.CORE2A.inf_U_S_eq_bot B
  have hH : B.U ⊔ (B.S : Subgroup G) = B.H := H_eq_U_sup_S G I.T hBc B
  have hUleH : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have hSleH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hSleHhat : (B.S : Subgroup G) ≤ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B
  have hfitU : Work.GW2.fittingIn B.U ≤ B.U :=
    Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U)
  have htH : B.t ∈ B.H := Work.CORE2A.bSetup_t_mem_H B
  have htS0 : B.t ∈ B.S0 := B.t_mem
  have htS : B.t ∈ (B.S : Subgroup G) := Work.CORE2A.bSetup_t_mem_S B
  have htne : B.t ≠ 1 := Work.CORE2A.bSetup_t_ne_one B
  have hS0leS : B.S0 ≤ (B.S : Subgroup G) := B.S0_le
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hBc B
  have hOutside := OutsideS0OrderTwo G hBc B n hn2 hdih
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [Work.CORE2A.bSetup_U_eq B]
    exact Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H)
  have hSN : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := hSleH.trans hHN
  have hUnorm : ((B.U).subgroupOf B.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have hdec : ∀ x ∈ B.H, ∃ u ∈ B.U, ∃ σ ∈ (B.S : Subgroup G), u * σ = x :=
    Work.CORE2A.exists_mul_of_mem_sup_of_normal hUleH hSleH hUnorm hH
  have huniq : ∀ {u₁ u₂ σ₁ σ₂ : G}, u₁ ∈ B.U → σ₁ ∈ (B.S : Subgroup G) → u₂ ∈ B.U →
      σ₂ ∈ (B.S : Subgroup G) → u₁ * σ₁ = u₂ * σ₂ → u₁ = u₂ ∧ σ₁ = σ₂ := by
    intro u₁ u₂ σ₁ σ₂ hu₁ hσ₁ hu₂ hσ₂ heq
    have h : u₂⁻¹ * u₁ = σ₂ * σ₁⁻¹ := by
      have hh := congrArg (fun z => u₂⁻¹ * z * σ₁⁻¹) heq
      simpa [mul_assoc] using hh
    have hm1 : u₂⁻¹ * u₁ ∈ B.U := B.U.mul_mem (B.U.inv_mem hu₂) hu₁
    have hm2 : σ₂ * σ₁⁻¹ ∈ (B.S : Subgroup G) := (B.S).mul_mem hσ₂ ((B.S).inv_mem hσ₁)
    have hmem : u₂⁻¹ * u₁ ∈ B.U ⊓ (B.S : Subgroup G) := ⟨hm1, h ▸ hm2⟩
    rw [hUS] at hmem
    have h1 : u₂⁻¹ * u₁ = 1 := Subgroup.mem_bot.mp hmem
    have hueq : u₁ = u₂ := by
      have hh := congrArg (fun z => u₂ * z) h1
      simpa [mul_assoc] using hh
    refine ⟨hueq, ?_⟩
    rw [hueq] at heq
    exact mul_left_cancel heq
  have htcent : ∀ u ∈ B.U, B.t * u = u * B.t := fun u hu =>
    Subgroup.mem_centralizer_iff.mp (hUleH hu) B.t (Set.mem_singleton B.t)
  have htV : B.t ∈ pCoreIn 2 B.Hhat := by
    rw [← hSC]
    exact ⟨htS, Subgroup.mem_centralizer_iff.mpr (fun u hu => (htcent u hu).symm)⟩
  have hcap : ∀ x : G, x ∈ (pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G) ↔ x = 1 ∨ x = B.t := by
    intro x
    constructor
    · rintro ⟨hxV, hxS0⟩
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · refine Or.inr ?_
        haveI : IsCyclic ↥B.S0 := B.S0_cyclic
        have ha : (⟨x, hxS0⟩ : ↥B.S0) ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hV4.2 x hxV
        have hb : (⟨B.t, htS0⟩ : ↥B.S0) ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one, ← B.t_order]
          exact pow_orderOf_eq_one B.t
        have ha1 : (⟨x, hxS0⟩ : ↥B.S0) ≠ 1 := fun h => hx1 (by simpa using congrArg Subtype.val h)
        have hb1 : (⟨B.t, htS0⟩ : ↥B.S0) ≠ 1 :=
          fun h => htne (by simpa using congrArg Subtype.val h)
        exact congrArg Subtype.val (Work.CORE2A.eq_of_sq_eq_one_of_isCyclic ha hb ha1 hb1)
    · rintro (rfl | rfl)
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨htV, htS0⟩
  have hVncard : (pCoreIn 2 B.Hhat : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hV4.1
  have hS0ncard : (B.S0 : Set G).ncard = 4 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [inf_eq_left.mpr hS0leS, B.S0_index, D.S8] at h
    have h4 : Nat.card B.S0 = 4 := by omega
    rw [← Nat.card_coe_set_eq]; exact h4
  have hSncard : ((B.S : Subgroup G) : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact D.S8
  -- ===== 1.  the reflections and their two halves =====
  have hRncard : (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)).ncard = 4 := by
    have h := Set.ncard_sdiff (s := (B.S0 : Set G)) (t := ((B.S : Subgroup G) : Set G))
      (fun _ hx => hS0leS hx) (Set.toFinite _)
    rw [hSncard, hS0ncard] at h
    simpa using h
  have hcapcard : ((pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G)).ncard = 2 := by
    rw [show (pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G) = ({1, B.t} : Set G) from by
      ext x; rw [hcap x]; simp]
    exact Set.ncard_pair (fun h => htne h.symm)
  have hR1card : ((((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
      ∩ (pCoreIn 2 B.Hhat : Set G)).ncard = 2 := by
    have heq : (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) ∩ (pCoreIn 2 B.Hhat : Set G)
        = (pCoreIn 2 B.Hhat : Set G) \ (B.S0 : Set G) := by
      ext x
      constructor
      · rintro ⟨⟨-, hxS0⟩, hxV⟩; exact ⟨hxV, hxS0⟩
      · rintro ⟨hxV, hxS0⟩; exact ⟨⟨hVS hxV, hxS0⟩, hxV⟩
    rw [heq]
    have heq2 : (pCoreIn 2 B.Hhat : Set G) \ (B.S0 : Set G)
        = (pCoreIn 2 B.Hhat : Set G) \ ((pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G)) := by
      ext x
      constructor
      · rintro ⟨hxV, hxS0⟩; exact ⟨hxV, fun h => hxS0 h.2⟩
      · rintro ⟨hxV, h⟩; exact ⟨hxV, fun hxS0 => h ⟨hxV, hxS0⟩⟩
    rw [heq2]
    have h := Set.ncard_sdiff
      (s := (pCoreIn 2 B.Hhat : Set G) ∩ (B.S0 : Set G)) (t := (pCoreIn 2 B.Hhat : Set G))
      Set.inter_subset_left (Set.toFinite _)
    rw [hVncard, hcapcard] at h
    simpa using h
  have hR2card : ((((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
      \ (pCoreIn 2 B.Hhat : Set G)).ncard = 2 := by
    have heq2 : (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) \ (pCoreIn 2 B.Hhat : Set G)
        = (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
          \ ((((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) ∩ (pCoreIn 2 B.Hhat : Set G)) := by
      ext x
      constructor
      · rintro ⟨hxR, hxV⟩; exact ⟨hxR, fun h => hxV h.2⟩
      · rintro ⟨hxR, h⟩; exact ⟨hxR, fun hxV => h ⟨hxR, hxV⟩⟩
    rw [heq2]
    have h := Set.ncard_sdiff
      (s := ((((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
        ∩ (pCoreIn 2 B.Hhat : Set G)))
      (t := ((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) Set.inter_subset_left (Set.toFinite _)
    rw [hRncard, hR1card] at h
    simpa using h
  -- ===== 2.  involutions of `H` other than `t` =====
  have hTcount : {x : G | x ∈ involutionSet B.H ∧ x ≠ B.t}.ncard = 2 + 2 * Nat.card D.K := by
    -- the two pieces of the count
    have hT2card : {y : G | ∃ p : G × G,
        p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) \ (pCoreIn 2 B.Hhat : Set G)
        ∧ p.2 ∈ (D.K : Set G) ∧ p.2 * p.1 = y}.ncard = 2 * Nat.card D.K := by
      have hDcard : {p : G × G | p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
          \ (pCoreIn 2 B.Hhat : Set G) ∧ p.2 ∈ (D.K : Set G)}.ncard = 2 * Nat.card D.K := by
        have hDeq : {p : G × G | p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
              \ (pCoreIn 2 B.Hhat : Set G) ∧ p.2 ∈ (D.K : Set G)}
            = ((((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
              \ (pCoreIn 2 B.Hhat : Set G)) ×ˢ (D.K : Set G) := by
          ext p
          exact (Set.mem_prod).symm
        rw [hDeq, Set.ncard_prod, hR2card]
        congr 1
      have hmain : {p : G × G | p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
            \ (pCoreIn 2 B.Hhat : Set G) ∧ p.2 ∈ (D.K : Set G)}.ncard
          = {y : G | ∃ p : G × G,
              p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
                \ (pCoreIn 2 B.Hhat : Set G)
              ∧ p.2 ∈ (D.K : Set G) ∧ p.2 * p.1 = y}.ncard := by
        refine Set.ncard_congr (fun (p : G × G) _ => p.2 * p.1) ?_ ?_ ?_
        · rintro p hp
          refine ⟨p, ?_, ?_, rfl⟩
          · exact hp.1
          · exact hp.2
        · rintro p q hp hq heq
          have hh := huniq (hfitU (D.hall.1 hq.2)) hq.1.1.1
            (hfitU (D.hall.1 hp.2)) hp.1.1.1 heq.symm
          exact Prod.ext hh.2.symm hh.1.symm
        · rintro y ⟨p, hp1, hp2, hy⟩
          exact ⟨p, ⟨hp1, hp2⟩, hy⟩
      rw [← hmain, hDcard]
    have hT1ncard : ((pCoreIn 2 B.Hhat : Set G)
        ∩ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))).ncard = 2 := by
      rw [Set.inter_comm]; exact hR1card
    have hdisj : Disjoint ((pCoreIn 2 B.Hhat : Set G)
        ∩ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)))
        {y : G | ∃ p : G × G,
          p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) \ (pCoreIn 2 B.Hhat : Set G)
          ∧ p.2 ∈ (D.K : Set G) ∧ p.2 * p.1 = y} := by
      rw [Set.disjoint_left]
      rintro y ⟨hyV, _⟩ ⟨p, hp1, hp2, hpy⟩
      obtain ⟨⟨hpS, hpS0⟩, hpV⟩ := hp1
      have hSmem : p.1 ∈ (B.S : Subgroup G) := hpS
      have hUmem : p.2 ∈ B.U := hfitU (D.hall.1 hp2)
      have hxS : p.2 * p.1 ∈ (B.S : Subgroup G) := hVS (hpy ▸ hyV)
      have hh := huniq B.U.one_mem hxS hUmem hSmem (one_mul _)
      have hp1eq : p.1 = y := by rw [← hh.2, hpy]
      exact hpV (hp1eq ▸ hyV)
    have hTeq : {x : G | x ∈ involutionSet B.H ∧ x ≠ B.t}
        = ((pCoreIn 2 B.Hhat : Set G)
            ∩ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)))
          ∪ {y : G | ∃ p : G × G,
              p.1 ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G))
                \ (pCoreIn 2 B.Hhat : Set G)
              ∧ p.2 ∈ (D.K : Set G) ∧ p.2 * p.1 = y} := by
      ext x
      constructor
      · rintro ⟨⟨hxH, hxo⟩, hxt⟩
        have hx2 : x * x = 1 := by
          rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one x
        have hx1 : x ≠ 1 := by
          intro h; rw [h, orderOf_one] at hxo; exact absurd hxo (by norm_num)
        obtain ⟨u, hu, σ, hσ, hux⟩ := hdec x hxH
        have hmul : u * (σ * u * σ⁻¹) * σ ^ 2 = 1 := by
          have hfac : u * σ * (u * σ) = u * (σ * u * σ⁻¹) * σ ^ 2 := by group
          rw [← hfac, hux, hx2]
        have hconjU : σ * u * σ⁻¹ ∈ B.U :=
          (Subgroup.mem_normalizer_iff.mp (hSN hσ) u).mp hu
        have hA : u * (σ * u * σ⁻¹) ∈ B.U := B.U.mul_mem hu hconjU
        have hprod : u * (σ * u * σ⁻¹) = (σ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hmul
        have hmem : u * (σ * u * σ⁻¹) ∈ B.U ⊓ (B.S : Subgroup G) :=
          ⟨hA, by rw [hprod]; exact (B.S).inv_mem ((B.S).pow_mem hσ 2)⟩
        rw [hUS] at hmem
        have h1' : u * (σ * u * σ⁻¹) = 1 := Subgroup.mem_bot.mp hmem
        have hs2 : σ ^ 2 = 1 := by rw [h1', one_mul] at hmul; exact hmul
        have hu_inv : σ * u * σ⁻¹ = u⁻¹ := eq_inv_of_mul_eq_one_right h1'
        by_cases hσS0 : σ ∈ B.S0
        · haveI : IsCyclic ↥B.S0 := B.S0_cyclic
          have ha : (⟨σ, hσS0⟩ : ↥B.S0) ^ 2 = 1 := by
            apply Subtype.ext
            rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hs2
          have hb : (⟨B.t, htS0⟩ : ↥B.S0) ^ 2 = 1 := by
            apply Subtype.ext
            rw [Subgroup.coe_pow, Subgroup.coe_one, ← B.t_order]
            exact pow_orderOf_eq_one B.t
          rcases eq_or_ne (⟨σ, hσS0⟩ : ↥B.S0) 1 with hσ1 | hσ1
          · have hσ1' : σ = 1 := by simpa using congrArg Subtype.val hσ1
            have hxu : x = u := by rw [← hux, hσ1', mul_one]
            have huu : u ^ 2 = 1 := by rw [pow_two, ← hxu, hx2]
            exact absurd (by rw [hxu]; exact eq_one_of_mem_of_sq_eq_one hUodd hu huu) hx1
          · have hb1 : (⟨B.t, htS0⟩ : ↥B.S0) ≠ 1 :=
              fun h => htne (by simpa using congrArg Subtype.val h)
            have hσt : σ = B.t :=
              congrArg Subtype.val (Work.CORE2A.eq_of_sq_eq_one_of_isCyclic ha hb hσ1 hb1)
            have hut : B.t * u * B.t⁻¹ = u := by rw [htcent u hu]; group
            have hu_inv' : u = u⁻¹ := by
              rw [hσt, hut] at hu_inv
              exact hu_inv
            have hu1 : u = 1 := eq_one_of_eq_inv_of_odd hUodd hu hu_inv'
            exact absurd (by rw [← hux, hσt, hu1, one_mul]) hxt
        · have hσn1 : σ ≠ 1 := fun h => hσS0 (h ▸ B.S0.one_mem)
          have hσR : σ ∈ (((B.S : Subgroup G) : Set G) \ (B.S0 : Set G)) := ⟨hσ, hσS0⟩
          by_cases hσV : σ ∈ (pCoreIn 2 B.Hhat : Set G)
          · have hcomm : u * σ = σ * u := Subgroup.mem_centralizer_iff.mp (hVcU hσV) u hu
            have hconjfix : σ * u * σ⁻¹ = u := by rw [← hcomm]; group
            have hu_inv' : u = u⁻¹ := by
              rw [hconjfix] at hu_inv
              exact hu_inv
            have hu1 : u = 1 := eq_one_of_eq_inv_of_odd hUodd hu hu_inv'
            have hxσ : x = σ := by rw [← hux, hu1, one_mul]
            exact Or.inl ⟨hxσ ▸ hσV, hxσ ▸ hσR⟩
          · have hσ2 : orderOf σ = 2 := orderOf_eq_prime hs2 hσn1
            have hK : (D.K : Set G) = invSet B.U σ :=
              D.inv σ (hSleHhat hσ) hσ2 hσV
            have huK : u ∈ (D.K : Set G) := by rw [hK]; exact ⟨hu, hu_inv⟩
            refine Or.inr ⟨(σ, u), ?_, ?_, hux⟩
            · exact ⟨hσR, hσV⟩
            · exact huK
      · rintro (⟨hxV, hxR⟩ | ⟨p, hp1, hp2, hpx⟩)
        · refine ⟨⟨hSleH (hVS hxV), orderOf_eq_prime (hV4.2 x hxV) ?_⟩, ?_⟩
          · intro h; exact hxR.2 (by rw [h]; exact B.S0.one_mem)
          · intro h; exact hxR.2 (by rw [h]; exact htS0)
        · rw [← hpx]
          obtain ⟨⟨hσ, hσS0⟩, hσV⟩ := hp1
          have hu : p.2 ∈ B.U := hfitU (D.hall.1 hp2)
          have hσ2 : orderOf p.1 = 2 := hOutside p.1 hσ hσS0
          have hsq : p.1 * p.1 = 1 := by rw [← pow_two, ← hσ2]; exact pow_orderOf_eq_one p.1
          have hK : (D.K : Set G) = invSet B.U p.1 :=
            D.inv p.1 (hSleHhat hσ) hσ2 hσV
          have huinv : p.1 * p.2 * p.1⁻¹ = p.2⁻¹ := (hK ▸ hp2).2
          have hxsq : (p.2 * p.1) * (p.2 * p.1) = 1 := by
            have hfac : p.2 * p.1 * (p.2 * p.1)
                = p.2 * (p.1 * p.2 * p.1⁻¹) * (p.1 * p.1) := by group
            rw [hfac, huinv, hsq, mul_one, mul_inv_cancel]
          refine ⟨⟨B.H.mul_mem (hUleH hu) (hSleH hσ), orderOf_eq_prime ?_ ?_⟩, ?_⟩
          · simpa [pow_two] using hxsq
          · intro h
            have h2 : p.1 = p.2⁻¹ := by
              have hh := congrArg (fun z => p.2⁻¹ * z) h
              simpa [mul_assoc] using hh
            have hmem : p.1 ∈ B.U ⊓ (B.S : Subgroup G) := ⟨h2 ▸ B.U.inv_mem hu, hσ⟩
            rw [hUS] at hmem
            exact hσS0 (Subgroup.mem_bot.mp hmem ▸ B.S0.one_mem)
          · intro h
            have h2 : p.2 = B.t * p.1⁻¹ := by rw [← h]; group
            have hmem : p.2 ∈ B.U ⊓ (B.S : Subgroup G) :=
              ⟨hu, by rw [h2]; exact (B.S).mul_mem (hS0leS htS0) ((B.S).inv_mem hσ)⟩
            rw [hUS] at hmem
            have hp2' : p.2 = 1 := Subgroup.mem_bot.mp hmem
            have hp1' : p.1 = B.t := by
              calc p.1 = 1 * p.1 := (one_mul _).symm
                _ = p.2 * p.1 := by rw [hp2']
                _ = B.t := h
            exact hσS0 (hp1' ▸ htS0)
    rw [hTeq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hT1ncard, hT2card]
  -- ===== 3.  add back `t` =====
  have htInv : B.t ∈ involutionSet B.H := ⟨htH, B.t_order⟩
  rw [show involutionSet B.H
      = insert B.t {x : G | x ∈ involutionSet B.H ∧ x ≠ B.t} from by
    ext x
    constructor
    · intro hx
      rcases eq_or_ne x B.t with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (rfl | ⟨hx, -⟩)
      · exact htInv
      · exact hx]
  rw [Set.ncard_insert_of_notMem (by simp) (Set.toFinite _), hTcount]
  omega

end MAIN

end Work.CORE3

namespace Work.CORE3

namespace Work.CORE3

/-- Elementary identity behind Bender 1981 §3 (4): `∑ (n − 3) b_n = (∑ n b_n) − 3 (∑ b_n)`,
stated over `ℤ` for a `ℕ`-valued function on a `Finset`. -/
private lemma sum_sub_three (s : Finset ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ s, ((i : ℤ) - 3) * (f i : ℤ))
      = ((∑ i ∈ s, i * f i : ℕ) : ℤ) - 3 * ((∑ i ∈ s, f i : ℕ) : ℤ) := by
  have h1 : (∑ i ∈ s, ((i : ℤ) - 3) * (f i : ℤ))
      = ∑ i ∈ s, ((i : ℤ) * (f i : ℤ) - 3 * (f i : ℤ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, Finset.sum_sub_distrib]
  congr 1
  · rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  · rw [Nat.cast_sum, Finset.mul_sum]

/-- Bender 1981 §3, p. 223, (1)–(4).  Deliverable `Work.GW2.Case1bCountProp`.

With `J` the set of involutions of `G`, `k = |K|` and `b_n` the number of cosets `Ĥg ≠ Ĥ`
containing exactly `n` involutions: `|H ∩ J| = 3 + 2k`, `|Ĥ ∩ J| = 3 + 6k`, `|G:H| = 3|G:Ĥ|`,
`6k + Σ_n (n−3)b_n = 0` and `|G:Ĥ| = 1 + Σ_n b_n`.

The involution counts come from the structure of `H = C_G(t) = S·U` and of `Ĥ` (with `U = O(H)`
inverted by the involutions of `Ĥ − V`); the two sum identities are
`Work.CORE3.BCountSum` and `Work.CORE3.SumMulBCount`, together with `|J| = |J ∩ Ĥ| + Σ n b_n`
and `|J| = |G:H|` from the toolkit's `InvolutionFusionProp` (`I.T.fus`). -/
theorem Case1bCount (I : Case1Inputs) : Case1bCountProp := by
  intro G hG hFin hFT hBc B h1 D
  classical
  -- ## (1) the two involution counts
  have hInvH : (involutionSet B.H).ncard = 3 + 2 * Nat.card D.K := invCountH_aux I hBc B h1 D
  have hInvHhat : (involutionSet B.Hhat).ncard = 3 + 6 * Nat.card D.K :=
    invCountHhat_aux I hBc B h1 D hInvH
  -- ## (2) `|G : H| = 3 |G : Ĥ|`
  have hIdx : B.H.index = 3 * B.Hhat.index := by
    have hRel : B.H.relIndex B.Hhat = 3 := RelIndexHHhat I hBc B h1 D
    have h := Subgroup.relIndex_mul_index (H := B.H) (K := B.Hhat) B.H_le_Hhat
    rw [hRel] at h
    exact h.symm
  -- ## (3) `|G : Ĥ| = 1 + Σ b_n`
  have hv : B.Hhat.index
      = 1 + ∑ m ∈ Finset.range (Nat.card B.Hhat + 1), bCount B.Hhat m := by
    have hBC := BCountSum G B.Hhat
    have hpos : 1 ≤ B.Hhat.index :=
      le_of_lt (Subgroup.one_lt_index_of_ne_top (Work.CORE2A.bSetup_Hhat_ne_top B))
    omega
  -- ## (4) `6k + Σ (n − 3) b_n = 0`
  have hfour : 6 * (Nat.card D.K : ℤ)
      + ∑ m ∈ Finset.range (Nat.card B.Hhat + 1),
          ((m : ℤ) - 3) * (bCount B.Hhat m : ℤ) = 0 := by
    obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hBc B
    have hJ : ({x : G | orderOf x = 2} : Set G).ncard = B.H.index :=
      Work.CORE2A.ncard_involutions_eq_index I.T hBc B n hn2 hdih
    have hSM := SumMulBCount G B.Hhat
    have hset : involutionSet B.Hhat ∪ {x : G | orderOf x = 2 ∧ x ∉ B.Hhat}
        = {x : G | orderOf x = 2} := by
      ext x
      constructor
      · rintro (⟨-, ho⟩ | ⟨ho, -⟩)
        · exact ho
        · exact ho
      · intro ho
        by_cases h : x ∈ B.Hhat
        · exact Or.inl ⟨h, ho⟩
        · exact Or.inr ⟨ho, h⟩
    have hdisj : Disjoint (involutionSet B.Hhat) {x : G | orderOf x = 2 ∧ x ∉ B.Hhat} := by
      rw [Set.disjoint_left]
      rintro x ⟨hx, -⟩ ⟨-, hx'⟩
      exact hx' hx
    have hsplit : ({x : G | orderOf x = 2} : Set G).ncard
        = (involutionSet B.Hhat).ncard
          + ({x : G | orderOf x = 2 ∧ x ∉ B.Hhat} : Set G).ncard := by
      rw [← hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    have hkey : B.H.index
        = (3 + 6 * Nat.card D.K)
          + ∑ m ∈ Finset.range (Nat.card B.Hhat + 1), m * bCount B.Hhat m := by
      rw [← hJ, hsplit, hInvHhat, ← hSM]
    have harith : 3 * (∑ m ∈ Finset.range (Nat.card B.Hhat + 1), bCount B.Hhat m)
        = 6 * Nat.card D.K
          + ∑ m ∈ Finset.range (Nat.card B.Hhat + 1), m * bCount B.Hhat m := by
      omega
    rw [sum_sub_three]
    omega
  exact ⟨hInvH, hInvHhat, hIdx, hfour, hv⟩

end Work.CORE3

/-- The same statement, exposed under the name `Work.CORE3.Case1bCount` requested by the lead
(the module's declaration sits in the doubly nested namespace `Work.CORE3.Work.CORE3`). -/
theorem Case1bCount (I : Case1Inputs) : Work.GW2.Case1bCountProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bCount I

end Work.CORE3
