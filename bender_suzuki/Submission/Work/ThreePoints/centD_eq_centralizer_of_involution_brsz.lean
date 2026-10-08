import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThreePoints.centD_eq_centralizer_of_involution
import Submission.Work.ThreePoints.S4Prop2.even_card_normalizer_of_maximal_p_subgroup_gen
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz

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

/-- Peterfalvi I Ch. II §4 Prop. 2 (a) and (c), with the Brauer–Suzuki black box as an
hypothesis (the `2`-rank-`1` case of Ch. I §4 Prop. 2, consumed by the source's proof of
Prop. 1 (a), is exactly `BrauerSuzukiProp`).  Under (B0)–(B2), for an involution `t ∉ H`:
`V = C_D(t)` is the centraliser in `D` of some involution of `H`, and every non-trivial element of
`K = J(D,t)` fixes exactly two points of `Ω = G ⧸ H`. -/
theorem centD_eq_centralizer_of_involution_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (∃ u ∈ Submission.Blueprint.involutions (H : Set G),
        Submission.Blueprint.centD H t =
          Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)) ∧
    (∀ x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, x ≠ 1 →
        (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard = 2) := by
  classical
  -- Ch. I §4 Prop. 2 in the form with the Brauer–Suzuki black box: for a strongly
  -- embedded `K ≤ F` and a maximal `p`-subgroup `Q ≤ K` fixing `≥ 3` points, `|N_K(Q)|` is even.
  have hS4 : ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) :=
    fun F _ _ {K} hK p hp hp2 Q hQK hQp hQ3 hQmax =>
      S4Prop2.even_card_normalizer_of_maximal_p_subgroup_gen hBrSz hK hp hp2 hQK hQp hQ3 hQmax
  -- Ch. II §4 Prop. 1 (a) with the Brauer–Suzuki black box.
  have hProp1a : ∀ {X M : Subgroup G},
      3 ≤ (Submission.Blueprint.fixedPts H X).ncard →
      (∃ g : G, M = Submission.Blueprint.conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
    fun {X M} hX3 hM hXM =>
      Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC hS4 hS hH hX3 hM hXM
  constructor
  · -- ## Prop. 2 (a)
    -- `V = C_D(t)` fixes the three points `H`, `H^t`, `H(t)`, so `|C_H(V)|` is even.
    have hV3 : 3 ≤ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard :=
      three_le_ncard_fixedPts_centD hH ht htH
    have hVH : (Submission.Blueprint.centD H t : Subgroup G) ≤ H := by
      rw [centD_eq, twoPoint_eq]
      exact le_trans inf_le_left inf_le_left
    have hev : Even (Nat.card
        (H ⊓ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) : Subgroup G)) :=
      hProp1a hV3 ⟨1, (conj_one H).symm⟩ hVH
    obtain ⟨u, hu_mem, hu2⟩ := exists_orderOf_two_of_even_card hev
    have huH : u ∈ H := (Subgroup.mem_inf.mp hu_mem).1
    have huC : u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) :=
      (Subgroup.mem_inf.mp hu_mem).2
    refine ⟨u, ⟨huH, hu2⟩, ?_⟩
    -- `V ≤ C_D(u)`, and `|C_D(u)| ≤ |V|` by the counting of Ch. I §2.
    have hVle : (Submission.Blueprint.centD H t : Subgroup G) ≤
        Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) := by
      refine le_inf inf_le_left ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp huC x hx
    have hcard_le : Nat.card (Submission.Blueprint.twoPoint H t ⊓
          Subgroup.centralizer ({u} : Set G) : Subgroup G)
        ≤ Nat.card (Submission.Blueprint.centD H t : Subgroup G) := by
      have hindex := ncard_invertedBy_le_index hH ht htH huH hu2
      have hCeq : Nat.card ((Submission.Blueprint.twoPoint H t ⊓
            Subgroup.centralizer ({u} : Set G)).subgroupOf
            (Submission.Blueprint.twoPoint H t))
          = Nat.card (Submission.Blueprint.twoPoint H t ⊓
            Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (inf_le_left : _ ≤ Submission.Blueprint.twoPoint H t)).toEquiv
      have hDcard' : Nat.card (Submission.Blueprint.twoPoint H t : Subgroup G)
          = ((Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
                (Submission.Blueprint.twoPoint H t)).index
            * Nat.card (Submission.Blueprint.twoPoint H t ⊓
                Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
        have h := Subgroup.card_mul_index
          ((Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
            (Submission.Blueprint.twoPoint H t))
        rw [hCeq] at h
        exact h.symm.trans (Nat.mul_comm _ _)
      have hKpos : 0 < (Submission.Blueprint.invertedBy
          (Submission.Blueprint.twoPoint H t) t).ncard := by
        haveI : Fintype G := Fintype.ofFinite G
        exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, one_mem_invertedBy _ _⟩
      have hDcard : Nat.card (Submission.Blueprint.twoPoint H t : Subgroup G)
          = Nat.card (Submission.Blueprint.centD H t : Subgroup G) *
              (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard :=
        card_twoPoint_eq_card_centD_mul_ncard_invertedBy hH ht htH
      refine Nat.le_of_mul_le_mul_left ?_ hKpos
      calc (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard
              * Nat.card (Submission.Blueprint.twoPoint H t ⊓
                  Subgroup.centralizer ({u} : Set G) : Subgroup G)
          ≤ ((Submission.Blueprint.twoPoint H t ⊓
                Subgroup.centralizer ({u} : Set G)).subgroupOf
                (Submission.Blueprint.twoPoint H t)).index
              * Nat.card (Submission.Blueprint.twoPoint H t ⊓
                  Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
            Nat.mul_le_mul_right _ hindex
        _ = Nat.card (Submission.Blueprint.twoPoint H t : Subgroup G) := hDcard'.symm
        _ = Nat.card (Submission.Blueprint.centD H t : Subgroup G) *
              (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard :=
            hDcard
        _ = (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard
              * Nat.card (Submission.Blueprint.centD H t : Subgroup G) := Nat.mul_comm _ _
    exact Subgroup.eq_of_le_of_card_ge hVle hcard_le
  · -- ## Prop. 2 (c)
    intro x hx hx1
    have hxD : x ∈ Submission.Blueprint.twoPoint H t := hx.1
    have hxH : x ∈ H := (mem_twoPoint.mp hxD).1
    have hxt : x ∈ conj t H := mem_conj_iff.mpr (mem_twoPoint.mp hxD).2
    have hmem1 : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
      exact Subgroup.zpowers_le.mpr hxH
    have hmemt : (t : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
      exact Subgroup.zpowers_le.mpr hxt
    have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact htH (by simpa using hcon)
    refine le_antisymm ?_ ?_
    · -- `≤ 2`: otherwise Prop. 1(a) gives an involution of `H` centralising `⟨x⟩`
      by_contra hle
      have hge3 : 3 ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard := by omega
      have hEven : Even (Nat.card
          (H ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) : Subgroup G)) :=
        hProp1a hge3 ⟨1, (conj_one H).symm⟩ (Subgroup.zpowers_le.mpr hxH)
      obtain ⟨v, hv_mem, hv2⟩ := exists_orderOf_two_of_even_card hEven
      have hvH : v ∈ H := (Subgroup.mem_inf.mp hv_mem).1
      have hvC : v ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp hv_mem).2
      have hvx : x * v = v * x :=
        Subgroup.mem_centralizer_iff.mp hvC x (Subgroup.mem_zpowers x)
      have heq : x⁻¹ * v * x = (1 : G)⁻¹ * v * 1 := by
        rw [inv_one, one_mul, mul_one, mul_assoc, ← hvx, ← mul_assoc,
          inv_mul_cancel, one_mul]
      have hx1' : x = 1 :=
        inv_conj_injective_on_invertedBy hH ht htH hvH hv2 x hx 1 (one_mem_invertedBy _ _) heq
      exact hx1 hx1'
    · -- `≥ 2`: `H` and `H^t` are fixed by `x`
      have h2 : ({((1 : G) : G ⧸ H), (t : G ⧸ H)} : Set (G ⧸ H)).ncard = 2 :=
        Set.ncard_pair h1t
      calc 2 = _ := h2.symm
        _ ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard :=
            Set.ncard_le_ncard (by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl
              · exact hmem1
              · exact hmemt)

end Work.ThreePoints
