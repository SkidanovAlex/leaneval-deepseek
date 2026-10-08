/-
# `Work.NormalComplement.Sec5Fix.P2a.Basic`

First consequences for the group `𝒩 ⧸ KK` acting on `Ω_V`: the kernel `KK` has odd order, the
action is transitive (from the sharp transitivity of `S` and the involution `t`), and the point
stabiliser is strongly embedded (from Ch. II §4 Prop. 1 (b) at `X = V`, `F = N_G(V)`, transported
along `𝒩 ↠ 𝒩 ⧸ KK`).
-/
import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.P2a.Nq
import Submission.Work.NormalComplement.sec5_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix
namespace P2a

variable {G : Type} [Group G] [Finite G]

/-- A nontrivial subgroup has at least two elements. -/
theorem two_le_ncard_of_ne_bot {S : Subgroup G} (h : S ≠ ⊥) : 2 ≤ (S : Set G).ncard := by
  have hx : ∃ x ∈ S, x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact h (le_antisymm (fun y hy => by simpa using hcon y hy) bot_le)
  obtain ⟨x, hxS, hx1⟩ := hx
  have hsub : ({1, x} : Set G) ⊆ (S : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact S.one_mem
    · exact hxS
  have h2 : ({1, x} : Set G).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem (by rintro rfl; exact hx1 rfl), Set.ncard_singleton]
  calc 2 = ({1, x} : Set G).ncard := h2.symm
    _ ≤ (S : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- The kernel of the action of `𝒩 = N_G(V)` on `Ω_V` has odd order: it lies in
`𝒩 ⊓ H ≤ D = H ⊓ H^t`, which has odd order. -/
theorem odd_card_KK {H : Subgroup G} {t : G} (hse : IsStronglyEmbedded H) (ht : t ∉ H) :
    Odd (Nat.card ↥(KK H t)) := by
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := hse.2.2 t ht
  have h1 : Nat.card ↥(KKg H t) = Nat.card ↥(KK H t) := by
    rw [KKg]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [← h1]
  exact Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le (KKg_le_twoPoint H t))

/-- `t ∈ 𝒩 = N_G(V)` (because `V ≤ C_G(t)`). -/
theorem mem_NNg_t (H : Subgroup G) (t : G) : t ∈ NNg H t := by
  have hV : centD H t ≤ Subgroup.centralizer ({t} : Set G) := inf_le_right
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hcomm : t * v = v * t := Subgroup.mem_centralizer_iff.mp (hV hv) t (by simp)
    have h : t * v * t⁻¹ = v := by rw [hcomm]; group
    rw [h]; exact hv
  · intro hv
    have hcw : t * v * t⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := hV hv
    have hcomm : t * (t * v * t⁻¹) = (t * v * t⁻¹) * t :=
      Subgroup.mem_centralizer_iff.mp hcw t (by simp)
    have h2 : v = t⁻¹ * (t * v * t⁻¹) * t := by group
    have h3 : t⁻¹ * (t * v * t⁻¹) * t = t * v * t⁻¹ := by
      rw [mul_assoc, ← hcomm]; group
    rw [h2, h3]; exact hv

/-- The orbit of the point `H^t` under `𝒩 ⧸ KK` is all of `Ω_V`. -/
theorem orbit_pttV_eq_univ {H : Subgroup G} {t : G} {S : Subgroup G} (hS : P2aSdata H t S) :
    ∀ ω : ↥(Om H t), ∃ g : Nq H t, g • (Sec5f.pttV H t : ↥(Om H t)) = ω := by
  intro ω
  by_cases hω : (ω : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H)
  · refine ⟨(QuotientGroup.mk' (KK H t) ⟨t, mem_NNg_t H t⟩)⁻¹, ?_⟩
    apply Subtype.ext
    show (t : G)⁻¹ • (QuotientGroup.mk t : G ⧸ H) = (ω : G ⧸ H)
    rw [Work.DoubleTransitivity.smul_mk, inv_mul_cancel, hω]
  · obtain ⟨q, hq, -⟩ := hS.sharp (ω : G ⧸ H) ω.2 hω
    refine ⟨QuotientGroup.mk' (KK H t) ⟨(q : G), hS.le_NN q.2⟩, ?_⟩
    apply Subtype.ext
    show (q : G) • (QuotientGroup.mk t : G ⧸ H) = (ω : G ⧸ H)
    exact hq

/-- `𝒩 ⧸ KK` acts transitively on `Ω_V`. -/
theorem pretransitive_Nq {H : Subgroup G} {t : G} {S : Subgroup G} (hS : P2aSdata H t S) :
    MulAction.IsPretransitive (Nq H t) ↥(Om H t) := by
  refine ⟨fun ω₁ ω₂ => ?_⟩
  obtain ⟨g₁, hg₁⟩ := orbit_pttV_eq_univ hS ω₁
  obtain ⟨g₂, hg₂⟩ := orbit_pttV_eq_univ hS ω₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [mul_smul, ← hg₁, inv_smul_smul, hg₂]

/-- The point stabiliser in `𝒩 ⧸ KK` is strongly embedded: `𝒩 ⊓ H` is strongly embedded in `𝒩`
(Ch. II §4 Prop. 1 (b) at `X = V`), and strong embeddedness is transported along the quotient
`𝒩 ↠ 𝒩 ⧸ KK` (whose kernel has odd order). -/
theorem isStronglyEmbedded_stab (hC4 : Submission.Blueprint.ChIIFourProp) {H : Subgroup G}
    {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) {S : Subgroup G}
    (hS : P2aSdata H t S) :
    IsStronglyEmbedded (MulAction.stabilizer (Nq H t) (Sec5f.ptV H t)) := by
  have h3 : 3 ≤ (Om H t).ncard := by
    rw [hS.card]
    have := two_le_ncard_of_ne_bot hS.ne_bot
    omega
  have hseL : IsStronglyEmbedded ((NNg H t ⊓ H).subgroupOf (NNg H t)) := by
    have h1 := (hC4 G h.sit H h.se t h.invol h.notMem).1 (centD H t) (NNg H t) h3 ?_ le_rfl 1 ?_
    · simpa [Work.ThreePoints.conj_one] using h1
    · intro x hx
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq] at hx
      exact Subgroup.centralizer_le_normalizer _ hx.1
    · rw [Work.ThreePoints.conj_one]
      exact (Work.ThreePoints.le_of_le_centD (le_refl (centD H t))).1
  have hres := Work.NormalComplement.isStronglyEmbedded_map_of_surjective
    (QuotientGroup.mk' (KK H t)) (QuotientGroup.mk'_surjective (KK H t))
    (QuotientGroup.ker_mk' (KK H t)) (odd_card_KK h.se h.notMem)
    (Sec5f.KK_le_subgroupOf (H := H) (t := t)) hseL
  rw [stabilizer_ptV_Nq H t]
  exact hres

end P2a
end Work.NormalComplement.Sec5Fix
