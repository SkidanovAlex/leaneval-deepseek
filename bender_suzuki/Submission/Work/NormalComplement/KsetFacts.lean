import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.BenderPrelimAux
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Facts about `D = H ⊓ H^t`, `t`, and `K = J(D,t) = invertedBy D t`

Elementary consequences of strong embeddedness: `|D|` is odd, `t` normalises `D`, `|K| = |Inv H|`
(Ch. I §2 Prop. 2(b)), `H` has at least two involutions in situation (B0)–(B2), conjugation
preserves the number of involutions, and the centraliser of an involution is contained in the
conjugate of `H` containing it (Ch. I §1 (2)).

Extracted from `case3_isCyclic.lean` so that consumers that only need these facts do not have to
depend on `fpf_invertedBy_isCyclic` (App. I (5)(c) in the `U ≤ D` form).
-/

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type} [Group G] [Finite G]


/-! ## Elementary facts about `D = H ⊓ H^t` -/

/-- `D = H ⊓ H^t` has odd order when `t ∉ H` and `H` is strongly embedded. -/
theorem odd_card_twoPoint {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (htH : t ∉ H) :
    Odd (Nat.card ↥(twoPoint H t)) :=
  hH.2.2 t htH

/-- `t` normalises `D = H ⊓ H^t`. -/
theorem normalize_twoPoint {H : Subgroup G} {t : G} (ht : orderOf t = 2) {x : G}
    (hx : x ∈ twoPoint H t) : t * x * t⁻¹ ∈ twoPoint H t := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hxH : x ∈ H := hx.1
  obtain ⟨y, hy, hxy⟩ := Work.ThreePoints.mem_conj_iff'.mp hx.2
  have hxt : t⁻¹ * x * t = y := by
    rw [hxy, mul_assoc t y t⁻¹, inv_mul_cancel_left, inv_mul_cancel_right]
  refine ⟨?_, ?_⟩
  · have h : t * x * t⁻¹ = t⁻¹ * x * t := by rw [htinv]
    rw [h, hxt]; exact hy
  · exact Subgroup.mem_map.mpr ⟨x, hxH,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

/-- The centraliser of an involution lying in a conjugate of `H` is contained in that conjugate
(Ch. I §1 (2)). -/
theorem centralizer_le_conj_of_involution {H : Subgroup G} (hH : IsStronglyEmbedded H) {g u : G}
    (hu : orderOf u = 2) (huH : u ∈ conj g H) :
    Subgroup.centralizer ({u} : Set G) ≤ conj g H := by
  intro c hc
  have hcu : c * u * c⁻¹ = u := by
    have h : u * c = c * u := (Subgroup.mem_centralizer_iff.mp hc) u (Set.mem_singleton u)
    rw [← h]
    exact mul_inv_cancel_right u c
  have hu' : u ∈ conj (c * g) H := by
    have heq : conj (c * g) H = conj c (conj g H) := Work.ThreePoints.conj_mul c g H
    rw [heq]
    show u ∈ (conj g H).map (MulAut.conj c).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨u, huH,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcu]⟩
  by_cases hEq : conj (c * g) H = conj g H
  · have heq : conj c (conj g H) = conj g H := by
      rw [← Work.ThreePoints.conj_mul c g H, hEq]
    have hmem : c ∈ Subgroup.normalizer ((conj g H : Subgroup G) : Set G) :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer c (conj g H)).mp heq
    rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq
      (Work.ThreePoints.conj_stronglyEmbedded hH g)] at hmem
    exact hmem
  · have hdvd : 2 ∣ Nat.card ↥((conj (c * g) H) ⊓ conj g H : Subgroup G) := by
      rw [← hu]
      exact Subgroup.orderOf_dvd_natCard _ ⟨hu', huH⟩
    exact absurd (even_iff_two_dvd.mpr hdvd)
      (Nat.not_even_iff_odd.mpr (Work.ThreePoints.card_inf_conj_odd hH hEq))

/-- Conjugation by `g` preserves the number of involutions. -/
theorem ncard_involutions_conj (g : G) (H : Subgroup G) :
    (involutions (conj g H : Set G)).ncard = (involutions (H : Set G)).ncard := by
  have h : (MulAut.conj g) '' (involutions (H : Set G)) = involutions (conj g H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyH, hy2⟩ := Work.ThreePoints.mem_involutions.mp hy
      exact Work.ThreePoints.mem_involutions.mpr
        ⟨Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hyH,
          by rw [MulEquiv.orderOf_eq, hy2]⟩
    · intro hx
      obtain ⟨hxH, hx2⟩ := Work.ThreePoints.mem_involutions.mp hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxH
      refine ⟨y, Work.ThreePoints.mem_involutions.mpr ⟨hy, ?_⟩, ?_⟩
      · rw [← (MulEquiv.orderOf_eq (MulAut.conj g) y), show (MulAut.conj g) y = x from hyx]
        exact hx2
      · rw [← hyx]; simp
  rw [← h]
  exact Set.ncard_image_of_injective _ (MulAut.conj g).injective

/-- `H` contains at least two involutions when `G` has 2-rank at least two (Ch. I §1 (2)). -/
theorem two_le_ncard_involutions (hS : Situation G) {H : Subgroup G} (hH : IsStronglyEmbedded H) :
    2 ≤ (involutions (H : Set G)).ncard := by
  obtain ⟨a, b, ha2, hb2, hne, hcomm⟩ := hS.1.1
  obtain ⟨g, hg⟩ := Work.ThreePoints.exists_conj_mem hH ha2
  have hb : b ∈ conj g H := by
    refine centralizer_le_conj_of_involution hH ha2 hg ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  have hsub : ({a, b} : Set G) ⊆ involutions (conj g H : Set G) := by
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain rfl | rfl := hx
    · exact Work.ThreePoints.mem_involutions.mpr ⟨hg, ha2⟩
    · exact Work.ThreePoints.mem_involutions.mpr ⟨hb, hb2⟩
  have h2 : 2 ≤ (involutions (conj g H : Set G)).ncard := by
    have hle := Set.ncard_le_ncard hsub
    rwa [Set.ncard_pair hne] at hle
  rwa [ncard_involutions_conj g H] at h2

/-- **Peterfalvi I Ch. I §2 Prop. 2(b)**, the count: `|K| = |Inv H|`. -/
theorem ncard_Kset_eq_involutions {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (Kset (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
  (kapp_ncard_eq_invOfConj_ncard hH ht htH).trans
    (invOfConj_ncard_eq_involutions_ncard hH ht htH)

end Work.NormalComplement
