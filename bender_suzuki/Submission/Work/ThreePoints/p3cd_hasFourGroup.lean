import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.P3NeBot.p3_appI_one
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.F1EqF.prop2c_of_even
import Submission.Work.ThreePoints.exists_involution_normalizer_of_brsz
import Submission.Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {X : Subgroup G}

/-! ## Elementary facts about `F = O^{2'}(C_G(X))` -/

/-- An involution of `C_G(X)` lies in `F = O^{2'}(C_G(X))`: the quotient of `C_G(X)` by `O^{2'}`
has odd order and an involution generates a `2`-subgroup. -/
theorem involution_mem_p3F {X : Subgroup G} {u : G}
    (hu : u ∈ involutions (Subgroup.centralizer (X : Set G) : Set G)) : u ∈ p3F X := by
  obtain ⟨huC, hu2⟩ := hu
  change u ∈ p3F X
  rw [mem_p3F]
  refine ⟨⟨u, huC⟩, ?_, rfl⟩
  exact involution_mem_oddResidual
    (x := (⟨u, huC⟩ : ↥(Subgroup.centralizer (X : Set G))))
    (Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2))

/-- `p3F X ≤ N_G(X)`. -/
theorem p3F_le_normalizer (X : Subgroup G) :
    p3F X ≤ Subgroup.normalizer (X : Set G) :=
  (p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G))

/-- `X ≤ H` for `X ≤ centD H t`. -/
theorem le_H_of_le_centD {H : Subgroup G} {t : G} {X : Subgroup G}
    (hX : X ≤ centD H t) : X ≤ H :=
  hX.trans (le_trans inf_le_left inf_le_left)

/-- **Peterfalvi I Ch. II §4 Prop. 1 (b)** at the fixed point `H` of `X`: for `X ≤ V = C_D(t)`,
the subgroup `F ⊓ H` of `F = O^{2'}(C_G(X))` is strongly embedded in `F` (`t ∈ F ∖ H` makes it
proper, and Ch. II §4 Prop. 1 (a) makes it even). -/
theorem strongEmbedded_p3F_inf_H (hFT : FeitThompsonProp) (hC : ThmCProp) (hA : ThmAProp)
    (hBrSz : BrauerSuzukiProp) (hS : Situation G) (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ centD H t) :
    IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X)) := by
  have hX3 : 3 ≤ (fixedPts H X).ncard := P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  have hevH : Even (Nat.card (H ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
    P3NeBot.p3_even_card_centralizer hFT hC hBrSz hS hH hX3
      ⟨1, (DoubleTransitivity.conj_one H).symm⟩ (le_H_of_le_centD hX)
  have hev : Even (Nat.card (p3F X ⊓ H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer hevH (fun u hu => involution_mem_p3F hu)
  refine IsStronglyEmbedded.subgroupOf_inf hH ?_ hev
  intro htop
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (mem_centD.mp (hX hx)).2.2
  have htF : t ∈ p3F X := involution_mem_p3F ⟨htC, ht⟩
  have hmem : (⟨t, htF⟩ : ↥(p3F X)) ∈ (p3F X ⊓ H).subgroupOf (p3F X) := by
    rw [htop]; trivial
  exact htH (Subgroup.mem_subgroupOf.mp hmem).2

/-! ## Maximality of a point stabiliser in a `2`-transitive action -/

/-- In a `2`-transitive action of `F` on a set `S`, the stabiliser of a point `a ∈ S` is maximal
among the subgroups `M ≤ F` containing it: if `M` fixes `a` then `M` is contained in that
stabiliser, and otherwise `M` is transitive on `S`, hence equal to `F`. -/
theorem stabilizer_maximal_of_twoTransitive {Y : Type} [Group Y] {E : Type} [MulAction Y E]
    {F : Subgroup Y} {S : Set E} (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub F S)
    (hS : ∀ y ∈ F, ∀ c ∈ S, y • c ∈ S) {a : E} (ha : a ∈ S)
    {M : Subgroup Y} (hMF : M ≤ F) (hKM : ∀ y ∈ F, y • a = a → y ∈ M) :
    M = F ∨ ∀ m ∈ M, m • a = a := by
  by_cases hfix : ∀ m ∈ M, m • a = a
  · exact Or.inr hfix
  · refine Or.inl (le_antisymm hMF ?_)
    push_neg at hfix
    obtain ⟨m, hmM, hma⟩ := hfix
    -- `M` is transitive on `S`
    have htr : ∀ c ∈ S, ∃ m' ∈ M, m' • a = c := by
      intro c hc
      by_cases hca : c = a
      · exact ⟨1, M.one_mem, by rw [one_smul, hca]⟩
      · obtain ⟨f, hfF, hf1, hf2⟩ :=
          h2t a ha (m • a) (hS m (hMF hmM) a ha) (fun h => hma h.symm) a ha c hc (fun h => hca h.symm)
        exact ⟨f * m, M.mul_mem (hKM f hfF hf1) hmM, by rw [mul_smul, hf2]⟩
    intro f hfF
    obtain ⟨m', hm'M, hm'a⟩ := htr (f • a) (hS f hfF a ha)
    have h1 : (m'⁻¹ * f) • a = a := by rw [mul_smul, ← hm'a, inv_smul_smul]
    have h2 : m'⁻¹ * f ∈ M :=
      hKM (m'⁻¹ * f) (F.mul_mem (F.inv_mem (hMF hm'M)) hfF) h1
    have h3 : f = m' * (m'⁻¹ * f) := by group
    rw [h3]
    exact M.mul_mem hm'M h2

/-! ## The target -/

theorem p3cd_hasFourGroup {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Submission.Blueprint.HasFourGroup ↥(Work.ThreePoints.p3F X) := by
  classical
  by_contra hno4
  -- ### Ch. II §4 Prop. 1 (a) with the inputs available in the workspace
  have hEven : ∀ (X' M : Subgroup G), (∃ g : G, M = conj g H) → X' ≤ M →
      3 ≤ (fixedPts H X').ncard →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X' : Set G) : Subgroup G)) :=
    fun X' M hM hXM hX'3 => P3NeBot.p3_even_card_centralizer hFT hC hBrSz hS hH hX'3 hM hXM
  -- ### Ch. II §4 Prop. 2 (c): every non-trivial element of `K = J(D,t)` fixes exactly two points
  have hProp2c : ∀ x ∈ invertedBy (twoPoint H t) t, x ≠ 1 →
      (fixedPts H (Subgroup.zpowers x)).ncard = 2 :=
    fun x hx hx1 => F1EqF.prop2c_of_even hC hBrSz hS hH ht htH hEven hx hx1
  -- ### `F₁ = ⟨Inv C_G(X)⟩` is `2`-transitive on `Ω_X`, hence so is `F = p3F X`
  have h2t1 : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F1 X) (fixedPts H X) :=
    P3NeBot.p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F X) (fixedPts H X) :=
    fun c hc d hd hcd c' hc' d' hd' hcd' =>
      let ⟨y, hy, h1, h2⟩ := h2t1 c hc d hd hcd c' hc' d' hd' hcd'
      ⟨y, p3F1_le_p3F X hy, h1, h2⟩
  -- ### `F ⊓ H` is strongly embedded in `F`
  have hSE : IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X)) :=
    strongEmbedded_p3F_inf_H hFT hC hA hBrSz hS hH ht htH hX
  -- ### the point `a = 1·H` of `Ω = G ⧸ H` and its stabiliser
  set a : G ⧸ H := ((1 : G) : G ⧸ H) with ha
  have hstab_a : MulAction.stabilizer G a = H := by
    rw [ha, Work.ThreePoints.stabilizer_mk, DoubleTransitivity.conj_one]
  have haS : a ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, hstab_a]
    exact le_H_of_le_centD hX
  have hSinv : ∀ y ∈ p3F X, ∀ c ∈ fixedPts H X, y • c ∈ fixedPts H X :=
    fun y hy c hc => P3NeBot.normalizer_preserves_fixedPts (p3F_le_normalizer X hy) hc
  -- ### `F ⊓ H` is maximal in `F` (a point stabiliser of a `2`-transitive action)
  have hmax : ∀ M : Subgroup G, p3F X ⊓ H ≤ M → M ≤ p3F X →
      M = p3F X ⊓ H ∨ M = p3F X := by
    intro M hKM hMF
    have hKM' : ∀ y ∈ p3F X, y • a = a → y ∈ M := by
      intro y hyF hya
      have h1 : y ∈ MulAction.stabilizer G a := MulAction.mem_stabilizer_iff.mpr hya
      have h2 : y ∈ H := by rw [hstab_a] at h1; exact h1
      exact hKM ⟨hyF, h2⟩
    rcases stabilizer_maximal_of_twoTransitive (F := p3F X) (S := fixedPts H X) h2t hSinv haS
        hMF hKM' with hcase | hcase
    · exact Or.inr hcase
    · refine Or.inl (le_antisymm ?_ hKM)
      intro m hm
      have h1 : m ∈ MulAction.stabilizer G a := MulAction.mem_stabilizer_iff.mpr (hcase m hm)
      have h2 : m ∈ H := by rw [hstab_a] at h1; exact h1
      exact ⟨hMF hm, h2⟩
  -- ### the fixed point `ω` of `t` in `Ω`
  obtain ⟨ω, hωset⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hH ht)
  have hω : t • ω = ω := by
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hωset]; exact rfl
    exact mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
  have htF : t ∈ p3F X := by
    have htC : t ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (mem_centD.mp (hX hx)).2.2
    exact involution_mem_p3F ⟨htC, ht⟩
  -- ### Appendix III (1): the two-point stabiliser `F ⊓ D` fixes `ω`
  have hstab : p3F X ⊓ twoPoint H t ≤ MulAction.stabilizer G ω :=
    P3NeBot.app3_1 (H := H) (X := X) (F := p3F X) (t := t) (ω := ω)
      hFT hBrSz hH (p3F_le_normalizer X) h2t hSE hmax hno4 ht htF htH hω
  -- ### the witness `k ∈ K#` normalising `X`
  obtain ⟨k, hk, hk1, hkN⟩ := hNX
  have hkF1 : k ∈ p3F1 X := P3NeBot.p3_lemma1 hFT hC hA hBrSz hS hH ht htH hX hk hkN
  have hkF : k ∈ p3F X := p3F1_le_p3F X hkF1
  have hkD : k ∈ twoPoint H t := hk.1
  have hkstab : k ∈ MulAction.stabilizer G ω := hstab ⟨hkF, hkD⟩
  have hkH : k ∈ H := (Work.ThreePoints.mem_twoPoint.mp hkD).1
  have hktH : k ∈ conj t H := Work.ThreePoints.mem_conj_iff.mpr (Work.ThreePoints.mem_twoPoint.mp hkD).2
  -- ### `k` fixes three distinct points of `Ω`
  have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) := by
    rw [mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
      DoubleTransitivity.conj_one]
    exact Subgroup.zpowers_le.mpr hkH
  have hmemt : ((t : G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) := by
    rw [mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk]
    exact Subgroup.zpowers_le.mpr hktH
  have hmemω : ω ∈ fixedPts H (Subgroup.zpowers k) := by
    rw [mem_fixedPts_iff_le_stabilizer]
    exact Subgroup.zpowers_le.mpr hkstab
  have h1t : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have h1ω : ((1 : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : t • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by rw [hcon]; exact hω
    rw [DoubleTransitivity.smul_mk_eq_mk_iff, DoubleTransitivity.mem_conj] at hmem
    exact htH (by simpa using hmem)
  have htω : ((t : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : t • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by rw [hcon]; exact hω
    rw [DoubleTransitivity.smul_mk_eq_mk_iff, DoubleTransitivity.mem_conj] at hmem
    rw [inv_mul_cancel, one_mul] at hmem
    exact htH hmem
  set b : G ⧸ H := ((t : G) : G ⧸ H) with hb
  have hsub : ({a, b, ω} : Set (G ⧸ H)) ⊆ fixedPts H (Subgroup.zpowers k) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h, ha]; exact hmem1
    · rw [h, hb]; exact hmemt
    · rw [h]; exact hmemω
  have hcard : ({a, b, ω} : Set (G ⧸ H)).ncard = 3 := by
    have h1 : a ∉ ({b, ω} : Set (G ⧸ H)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by rw [ha, hb]; exact h1t, by rw [ha]; exact h1ω⟩
    have h2 : b ∉ ({ω} : Set (G ⧸ H)) := by
      simp only [Set.mem_singleton_iff]
      rw [hb]; exact htω
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
  have h3 : 3 ≤ (fixedPts H (Subgroup.zpowers k)).ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard hsub
  -- ### contradiction with Prop. 2 (c)
  have h2 := hProp2c k hk hk1
  omega

end Work.ThreePoints
