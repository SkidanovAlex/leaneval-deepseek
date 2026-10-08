import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.fourGroup_centralizer_in_sylow
import Submission.Work.BG.isFourGroup_closure_pair
import Submission.Work.BG.S_le_H
import Submission.Work.BG.nCases
import Submission.Work.GLUE.PiCoreApi

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

namespace Work.BG

open Subgroup

/-!
# Area BG: the `t₂`-relative index `k₂ = |H : C_H(t₂)|`

For the Bender–Glauberman data `D` (`H = C_G(t) = D.H`, `U = O(H) = D.U`,
`S` the dihedral Sylow `2`-subgroup, `S₀ ≤ S` cyclic of index two, `t ∈ S₀` and `t₂ ∈ S ∖ S₀`
involutions), the quantity `k₂ = |H : C_H(t₂)|` of Bender–Glauberman 1981 satisfies

  `k₂ = (|S₀| / 2) · |U : B₂|`,  `B₂ = U ⊓ C_G(t₂)`.

The proof is the `t₂`-analogue of the `t₁` computation.  Its ingredients:

* `S ≤ H = C_G(t)` (`Work.BG.S_le_H`) and `H = U ⊔ S` (the centralizer splitting
  `Work.GW2.CentralizerSplitProp`, proved as `Work.BG.SplitGlue.centralizerSplitProp`);
* `U` is odd and `S` a `2`-group, so `U ⊓ S = ⊥` and (because `U ⊴ H` normalizes `S`)
  `|H| = |U| · |S| = |U| · 2·|S₀|/2`;
* an element of `C_H(t₂)` is `u·s` with `u ∈ U`, `s ∈ S`, and conjugating by `t₂` fixes both
  factors (uniqueness of the decomposition `U·S`), so `C_H(t₂) = B₂ ⊔ C_S(t₂)` with
  `B₂ = U ⊓ C_G(t₂)` and `C_S(t₂) = S ⊓ C_G(t₂)`;
* `C_S(t₂) = ⟨t, t₂⟩` is the Klein four-group of `S`, of order `4`, because four-subgroups of a
  dihedral `2`-subgroup are self-centralizing (`Work.BG.fourGroup_centralizer_in_sylow` applied to
  the four-group `Work.BG.isFourGroup_closure_pair`).
-/

namespace RelIndexCentT2Aux

/-! ## General group-theoretic helpers -/

/-- If `A ⊴ X` (globally) for a finite group `X` and `A ⊔ B = ⊤`, `A ⊓ B = ⊥`, then
`|X| = |A| · |B|`.  (The point is that no coprimality or commutativity is needed, only that the
product `A·B` is a subgroup, which holds because `A` is normal.) -/
theorem card_eq_mul_card_of_sup_eq_top_of_normal {X : Type} [Group X] [Finite X]
    (A B : Subgroup X) [A.Normal] (hsup : A ⊔ B = ⊤) (hdis : A ⊓ B = ⊥) :
    Nat.card X = Nat.card A * Nat.card B := by
  have h1 : A.relIndex (A ⊔ B) * Nat.card ↥(A ⊓ (A ⊔ B)) = Nat.card ↥(A ⊔ B) :=
    Subgroup.relIndex_mul_card A (A ⊔ B)
  rw [Subgroup.relIndex_sup_left B A, inf_eq_left.mpr le_sup_left, hsup] at h1
  have h2 : A.subgroupOf B = ⊥ := by
    rw [eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have : (x : X) ∈ A ⊓ B := ⟨hx, x.2⟩
    rw [hdis] at this
    simpa using this
  have h3 : A.relIndex B = Nat.card B := by
    show (A.subgroupOf B).index = Nat.card B
    rw [h2, Subgroup.index_bot]
  rw [h3] at h1
  have h4 : Nat.card ↥(⊤ : Subgroup X) = Nat.card X :=
    Nat.card_congr (Subgroup.topEquiv (G := X)).toEquiv
  rw [h4] at h1
  rw [mul_comm] at h1
  exact h1.symm

/-- Relative version of `card_eq_mul_card_of_sup_eq_top_of_normal`: for `A, B ≤ X'` with
`A` normalized by `X'`, `A ⊔ B = X'` and `A ⊓ B = ⊥`, one has `|X'| = |A| · |B|`. -/
theorem card_eq_mul_card_of_sup_eq_of_normal {X : Type} [Group X] [Finite X]
    (A B X' : Subgroup X) (hA : A ≤ X') (hB : B ≤ X')
    (hnorm : X' ≤ Subgroup.normalizer (A : Set X))
    (hsup : A ⊔ B = X') (hdis : A ⊓ B = ⊥) :
    Nat.card X' = Nat.card A * Nat.card B := by
  haveI : (A.subgroupOf X').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr hnorm
  have hsup' : A.subgroupOf X' ⊔ B.subgroupOf X' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA hB, hsup, Subgroup.subgroupOf_self]
  have hdis' : A.subgroupOf X' ⊓ B.subgroupOf X' = ⊥ := by
    rw [eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hxbot : (x : X) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
    rw [hdis] at hxbot
    simpa using hxbot
  have h := card_eq_mul_card_of_sup_eq_top_of_normal (A.subgroupOf X') (B.subgroupOf X')
    hsup' hdis'
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv] at h
  exact h

/-- Existence of the decomposition `x = a·b` with `a ∈ A`, `b ∈ B` for `x ∈ X'`, when `A` is
normalized by `X'` and `A ⊔ B = X'`. -/
theorem exists_mul_mem_of_sup_eq_of_normal {X : Type} [Group X] (A B X' : Subgroup X)
    (hA : A ≤ X') (hB : B ≤ X') (hnorm : X' ≤ Subgroup.normalizer (A : Set X))
    (hsup : A ⊔ B = X') {x : X} (hx : x ∈ X') :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  haveI : (A.subgroupOf X').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr hnorm
  have hsup' : A.subgroupOf X' ⊔ B.subgroupOf X' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA hB, hsup, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hx⟩ : ↥X') ∈ A.subgroupOf X' ⊔ B.subgroupOf X' := by rw [hsup']; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left).mp hx'
  refine ⟨(a : X), ?_, (b : X), ?_, ?_⟩
  · rwa [Subgroup.mem_subgroupOf] at ha
  · rwa [Subgroup.mem_subgroupOf] at hb
  · exact congrArg Subtype.val hab

/-- **Uniqueness of the decomposition** along a direct product `A · B` with `A ⊓ B = ⊥`. -/
theorem eq_of_mul_eq_mul_of_inf_eq_bot {X : Type} [Group X] {A B : Subgroup X}
    (hdis : A ⊓ B = ⊥) {a a' : X} (ha : a ∈ A) (ha' : a' ∈ A) {b b' : X}
    (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hkey : a'⁻¹ * a = b' * b⁻¹ := by
    have h1 : a'⁻¹ * (a * b) * b⁻¹ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
    simpa [mul_assoc] using h1
  have hmemA : a'⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha') ha
  have hmemB : a'⁻¹ * a ∈ B := by rw [hkey]; exact B.mul_mem hb' (B.inv_mem hb)
  have hmem : a'⁻¹ * a ∈ A ⊓ B := ⟨hmemA, hmemB⟩
  rw [hdis] at hmem
  have h1 : a'⁻¹ * a = 1 := hmem
  have h2 : b' * b⁻¹ = 1 := by rw [← hkey]; exact h1
  exact ⟨(inv_mul_eq_one.mp h1).symm, (mul_inv_eq_one.mp h2).symm⟩

/-- Arithmetic: if `2·n = 2 ^ k` and `2 ≤ n` (so `n` is a power of two, `≥ 2`), then `n` is even,
i.e. `2 * (n / 2) = n`. -/
theorem two_mul_div_two_eq_of_two_mul_eq_two_pow {n k : ℕ} (hn : 2 ≤ n) (h : 2 * n = 2 ^ k) :
    2 * (n / 2) = n := by
  have hk2 : 2 ≤ k := by
    by_contra hk
    push Not at hk
    interval_cases k <;> simp at h <;> omega
  have hn' : n = 2 ^ (k - 1) := by
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [h2] at h
    exact Nat.mul_left_cancel (by norm_num) h
  have hdvd : 2 ∣ n := by
    rw [hn']
    exact ⟨2 ^ (k - 1 - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
  exact Nat.mul_div_cancel' hdvd

/-! ## Elementary facts about the Bender–Glauberman data -/

/-- `U = O(H)` is a subgroup of `H`. -/
theorem aux_U_le_H {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) : D.U ≤ D.H := by
  have : D.U = (Work.GW2.oddCore ↥D.H).map D.H.subtype := rfl
  rw [this]; exact Subgroup.map_subtype_le _

/-- `U = O(H)` is normalized by `H` (it is normal in `H`). -/
theorem aux_H_le_normalizer_U {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.H ≤ Subgroup.normalizer (D.U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh u hu
  have hUm : D.U = (Work.GW2.oddCore ↥D.H).map D.H.subtype := rfl
  rw [hUm] at hu ⊢
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * a * ⟨h, hh⟩⁻¹,
    (Work.GW2.oddCore_normal ↥D.H).conj_mem a ha ⟨h, hh⟩, by simp⟩

/-- The centralizer splitting `H = U · S` (`Work.GW2.CentralizerSplitProp`). -/
theorem aux_H_eq_U_sup_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.U ⊔ (D.S : Subgroup G) = D.H := by
  have h := Work.BG.SplitGlue.centralizerSplitProp
  exact h G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (Work.BG.S_le_H D hx) D.t (by simp)).symm)

/-- `U ⊓ S = ⊥` (coprime orders: `U` is odd, `S` is a `2`-group). -/
theorem aux_U_inf_S_eq_bot {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.U ⊓ (D.S : Subgroup G) = ⊥ := by
  have hU : Odd (Nat.card D.U) := by
    have h : D.U = (Work.GW2.oddCore ↥D.H).map D.H.subtype := rfl
    rw [h, Subgroup.card_map_of_injective D.H.subtype_injective]
    exact Work.GW2.odd_card_oddCore
  obtain ⟨e⟩ := D.dih
  have hS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp D.S.isPGroup'
  rw [hS] at hj
  have hd : Disjoint D.U (D.S : Subgroup G) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hS, hj]
    exact (Nat.coprime_two_right.mpr hU).pow_right j
  rwa [disjoint_iff] at hd

/-- `|S| = 2 · |S₀|/2 · 2` … concretely `|S| = 2 * D.n`, since `S ≃* DihedralGroup D.n`. -/
theorem aux_card_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
  obtain ⟨e⟩ := D.dih
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- `D.n` is even (it is a power of two `≥ 2`), so `2 * (D.n / 2) = D.n`. -/
theorem aux_two_mul_div_two_eq {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    2 * (D.n / 2) = D.n := by
  obtain ⟨e⟩ := D.dih
  have hS : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp D.S.isPGroup'
  rw [hS] at hk
  exact two_mul_div_two_eq_of_two_mul_eq_two_pow D.two_le hk

/-- `⟨t, t₂⟩ ≤ S`. -/
theorem aux_closure_le_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    Subgroup.closure ({D.t, D.t2} : Set G) ≤ (D.S : Subgroup G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact D.S0_le D.t_mem
  · exact D.t2_mem

/-- `⟨t, t₂⟩` is a Klein four-group (`t` centralizes `t₂`, both are distinct involutions). -/
theorem aux_isFourGroup {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    Work.GW2.IsFourGroup (Subgroup.closure ({D.t, D.t2} : Set G)) := by
  have hSH : (D.S : Subgroup G) ≤ D.H := Work.BG.S_le_H D
  have ht2sq : D.t2 ^ 2 = 1 := by
    have := pow_orderOf_eq_one D.t2; rw [D.t2_order] at this; exact this
  have htsq : D.t ^ 2 = 1 := by
    have := pow_orderOf_eq_one D.t; rw [D.t_order] at this; exact this
  have ht1 : D.t ≠ 1 := by
    intro h; have := D.t_order; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have ht21 : D.t2 ≠ 1 := by
    intro h; have := D.t2_order; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have htne : D.t ≠ D.t2 := by rintro h; exact D.t2_nmem (h ▸ D.t_mem)
  have hcomm : D.t * D.t2 = D.t2 * D.t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hSH D.t2_mem)).symm
  exact Work.BG.isFourGroup_closure_pair htsq ht2sq hcomm ht1 ht21 htne

/-- `C_S(t₂) = ⟨t, t₂⟩`: a four-subgroup of a dihedral Sylow is self-centralizing, and `t` is
central in `S`. -/
theorem aux_centralizer_inf_S_eq_closure {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G)
      = Subgroup.closure ({D.t, D.t2} : Set G) := by
  have hSH : (D.S : Subgroup G) ≤ D.H := Work.BG.S_le_H D
  have ht2W : D.t2 ∈ Subgroup.closure ({D.t, D.t2} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hWS := aux_closure_le_S D
  have hW4 := aux_isFourGroup D
  obtain ⟨e⟩ := D.dih
  have hfour := Work.BG.fourGroup_centralizer_in_sylow D.S e hWS hW4
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [← hfour, Subgroup.mem_inf]
    refine ⟨?_, hx.2⟩
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hSH hx.2)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.1).symm
  · intro x hx
    rw [← hfour] at hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, hx.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx.1) D.t2 ht2W).symm

/-- `|C_S(t₂)| = |⟨t, t₂⟩| = 4`. -/
theorem aux_card_centralizer_inf_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    Nat.card ↥(Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G)) = 4 := by
  rw [aux_centralizer_inf_S_eq_closure D]
  exact (aux_isFourGroup D).1

/-- `C_H(t₂) = B₂ ⊔ C_S(t₂)`: an element `x = u·s ∈ C_H(t₂)` (`u ∈ U`, `s ∈ S`) has the
conjugate decomposition `(t₂ u t₂)·(t₂ s t₂) = x`, and uniqueness forces `t₂ u t₂ = u`,
`t₂ s t₂ = s`; so `u ∈ B₂ = U ⊓ C_G(t₂)` and `s ∈ C_S(t₂)`. -/
theorem aux_B2_sup_eq {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.B2 ⊔ (Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G))
      = Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H := by
  have hUH := aux_U_le_H D
  have hSH : (D.S : Subgroup G) ≤ D.H := Work.BG.S_le_H D
  have hnorm := aux_H_le_normalizer_U D
  have hsup := aux_H_eq_U_sup_S D
  have hdis := aux_U_inf_S_eq_bot D
  have ht2sq : D.t2 * D.t2 = 1 := by
    have := pow_orderOf_eq_one D.t2
    rw [D.t2_order] at this
    simpa [pow_two] using this
  have ht2H : D.t2 ∈ D.H := hSH D.t2_mem
  apply le_antisymm
  · apply sup_le
    · intro x hx; rw [Subgroup.mem_inf] at hx ⊢; exact ⟨hx.2, hUH hx.1⟩
    · intro x hx; rw [Subgroup.mem_inf] at hx ⊢; exact ⟨hx.1, hSH hx.2⟩
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxC, hxH⟩ := hx
    obtain ⟨a, haU, b, hbS, hab⟩ :=
      exists_mul_mem_of_sup_eq_of_normal D.U (D.S : Subgroup G) D.H hUH hSH hnorm hsup hxH
    have hxt : x * D.t2 = D.t2 * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hconj : (D.t2 * a * D.t2) * (D.t2 * b * D.t2) = x := by
      have h1 : (D.t2 * a * D.t2) * (D.t2 * b * D.t2) = D.t2 * (a * b) * D.t2 := by
        rw [show (D.t2 * a * D.t2) * (D.t2 * b * D.t2)
            = D.t2 * a * (D.t2 * D.t2) * b * D.t2 by group, ht2sq, mul_one]
        group
      rw [h1, hab]
      have hfinal : D.t2 * x * D.t2 = x := by
        rw [mul_assoc, hxt, ← mul_assoc, ht2sq, one_mul]
      exact hfinal
    have haU' : D.t2 * a * D.t2 ∈ D.U := by
      have h := (Subgroup.le_normalizer_iff.mp hnorm) D.t2 ht2H a haU
      rwa [inv_eq_of_mul_eq_one_right ht2sq] at h
    have hbS' : D.t2 * b * D.t2 ∈ D.S :=
      (D.S).mul_mem ((D.S).mul_mem D.t2_mem hbS) D.t2_mem
    obtain ⟨haeq, hbeq⟩ :=
      eq_of_mul_eq_mul_of_inf_eq_bot hdis haU haU' hbS hbS' (hab.trans hconj.symm)
    have haC : a ∈ Subgroup.centralizer ({D.t2} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : D.t2 * a = a * D.t2 := by
        have e1 : D.t2 * a = D.t2 * (D.t2 * a * D.t2) := congrArg (fun z => D.t2 * z) haeq
        have e2 : D.t2 * (D.t2 * a * D.t2) = a * D.t2 := by
          rw [show D.t2 * (D.t2 * a * D.t2) = (D.t2 * D.t2) * (a * D.t2) by group,
            ht2sq, one_mul]
        exact e1.trans e2
      exact h2.symm
    have hbC : b ∈ Subgroup.centralizer ({D.t2} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : D.t2 * b = b * D.t2 := by
        have e1 : D.t2 * b = D.t2 * (D.t2 * b * D.t2) := congrArg (fun z => D.t2 * z) hbeq
        have e2 : D.t2 * (D.t2 * b * D.t2) = b * D.t2 := by
          rw [show D.t2 * (D.t2 * b * D.t2) = (D.t2 * D.t2) * (b * D.t2) by group,
            ht2sq, one_mul]
        exact e1.trans e2
      exact h2.symm
    rw [← hab]
    exact Subgroup.mul_mem_sup ⟨haU, haC⟩ ⟨hbC, hbS⟩

end RelIndexCentT2Aux

open RelIndexCentT2Aux

/-- **Bender–Glauberman 1981 notation**: `k₂ = |H : C_H(t₂)| = (1/2)|S₀|·|U : B₂|`, i.e.
`(C_G(t₂)).relIndex H = (D.n / 2) * D.B2.relIndex D.U` for the Bender–Glauberman data `D`
(`H = C_G(t)`, `U = O(H)`, `B₂ = U ⊓ C_G(t₂)`, `|S₀| = D.n`).  This is the `t₂`-analogue of
`Work.BG.relIndexCentT1`; the same route applies verbatim with `t₂` in place of `t₁` (`S_le_H` gives
`S ≤ H`, `centralizerSplitProp` gives `H = U ⊔ S`, and `C_S(t₂) = ⟨t, t₂⟩` is the self-centralizing
Klein four-group of the dihedral Sylow `S`). -/
theorem relIndexCentT2 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H
      = (D.n / 2) * D.B2.relIndex D.U := by
  have hUH := aux_U_le_H D
  have hSH : (D.S : Subgroup G) ≤ D.H := Work.BG.S_le_H D
  have hnorm := aux_H_le_normalizer_U D
  have hsup := aux_H_eq_U_sup_S D
  have hdis := aux_U_inf_S_eq_bot D
  -- `|H| = |U| · |S|`
  have hcardH : Nat.card ↥D.H = Nat.card D.U * Nat.card ↥(D.S : Subgroup G) :=
    card_eq_mul_card_of_sup_eq_of_normal D.U (D.S : Subgroup G) D.H hUH hSH hnorm hsup hdis
  have hcardS := aux_card_S D
  have hcardV := aux_card_centralizer_inf_S D
  have hdecomp := aux_B2_sup_eq D
  -- `B₂` is normalized by `C_G(t₂) ⊓ H`
  have hnormB2 : (Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H) ≤
      Subgroup.normalizer (D.B2 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx b hb
    rw [Subgroup.mem_inf] at hx hb
    have hmemU : x * b * x⁻¹ ∈ D.U :=
      (Subgroup.le_normalizer_iff.mp hnorm) x hx.2 b hb.1
    have hmemC : x * b * x⁻¹ ∈ Subgroup.centralizer ({D.t2} : Set G) :=
      (Subgroup.centralizer ({D.t2} : Set G)).mul_mem
        ((Subgroup.centralizer ({D.t2} : Set G)).mul_mem hx.1 hb.2)
        ((Subgroup.centralizer ({D.t2} : Set G)).inv_mem hx.1)
    exact ⟨hmemU, hmemC⟩
  have hsubB2 : D.B2 ≤ Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H :=
    le_inf inf_le_right (inf_le_left.trans hUH)
  have hsubV : Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G) ≤
      Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H :=
    le_inf inf_le_left (inf_le_right.trans hSH)
  have hdisB2V : D.B2 ⊓ (Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G)) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxU : x ∈ D.U := (Subgroup.mem_inf.mp hx.1).1
    have hxS : x ∈ (D.S : Subgroup G) := (Subgroup.mem_inf.mp hx.2).2
    have : x ∈ D.U ⊓ (D.S : Subgroup G) := ⟨hxU, hxS⟩
    rw [hdis] at this
    simpa using this
  -- `|C_H(t₂)| = |B₂| · |C_S(t₂)| = |B₂| · 4`
  have hcardCH : Nat.card ↥(Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H)
      = Nat.card ↥D.B2 * Nat.card ↥(Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G)) :=
    card_eq_mul_card_of_sup_eq_of_normal D.B2
      (Subgroup.centralizer ({D.t2} : Set G) ⊓ (D.S : Subgroup G))
      (Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H) hsubB2 hsubV hnormB2 hdecomp hdisB2V
  -- index arithmetic
  have E1 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({D.t2} : Set G)) D.H
  have hB2U : D.B2 ≤ D.U := inf_le_left
  have E4 : D.B2.relIndex D.U * Nat.card ↥D.B2 = Nat.card ↥D.U := by
    have h := Subgroup.relIndex_mul_card D.B2 D.U
    rwa [inf_eq_left.mpr hB2U] at h
  have E4' : Nat.card ↥D.U = Nat.card ↥D.B2 * D.B2.relIndex D.U := by
    rw [← E4]; exact mul_comm _ _
  have hn2 := aux_two_mul_div_two_eq D
  have h2n : 2 * D.n = 4 * (D.n / 2) := by
    calc 2 * D.n = 2 * (2 * (D.n / 2)) := by rw [hn2]
      _ = 4 * (D.n / 2) := by ring
  have main : (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H * (Nat.card ↥D.B2 * 4)
      = (Nat.card ↥D.B2 * D.B2.relIndex D.U) * (2 * D.n) := by
    rw [← hcardV, ← hcardCH, E1, hcardH, hcardS, E4']
  have hu : 0 < Nat.card ↥D.B2 :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, Subgroup.one_mem D.B2⟩⟩, inferInstance⟩
  have key : ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H * 4) * Nat.card ↥D.B2
      = (((D.n / 2) * D.B2.relIndex D.U) * 4) * Nat.card ↥D.B2 := by
    calc ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H * 4) * Nat.card ↥D.B2
        = (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H * (Nat.card ↥D.B2 * 4) := by ring
      _ = (Nat.card ↥D.B2 * D.B2.relIndex D.U) * (2 * D.n) := main
      _ = (((D.n / 2) * D.B2.relIndex D.U) * 4) * Nat.card ↥D.B2 := by rw [h2n]; ring
  exact Nat.mul_right_cancel (by norm_num : (0:ℕ) < 4) (Nat.mul_right_cancel hu key)

end Work.BG
