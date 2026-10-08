import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2K1_ne_bot

namespace Work.CORE4.FpropsAux

/-- In a cyclic group `B`, every subgroup `X ≤ B` is characteristic in `B`; in particular,
every element of `G` normalizing `B` also normalizes `X`. -/
theorem normalizer_le_normalizer_of_isCyclic {G : Type} [Group G] [Finite G]
    {B X : Subgroup G} (hcyc : IsCyclic ↥B) (hX : X ≤ B) :
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  set φ : MulAut G := MulAut.conj g with hφ
  have hXB : Subgroup.map (φ : G →* G) X ≤ B := by
    rw [← hg]
    exact Subgroup.map_mono hX
  haveI : IsCyclic ↥B := hcyc
  have hc1 : Nat.card ↥(X.subgroupOf B) = Nat.card ↥X := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective B) (K := X.subgroupOf B),
        Subgroup.map_subgroupOf_eq_of_le hX]
  have hc2 : Nat.card ↥((Subgroup.map (φ : G →* G) X).subgroupOf B) =
      Nat.card ↥(Subgroup.map (φ : G →* G) X) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective B)
          (K := (Subgroup.map (φ : G →* G) X).subgroupOf B),
        Subgroup.map_subgroupOf_eq_of_le hXB]
  have hc3 : Nat.card ↥(Subgroup.map (φ : G →* G) X) = Nat.card ↥X :=
    Subgroup.card_map_of_injective (MulEquiv.injective φ)
  have hY : X.subgroupOf B = (Subgroup.map (φ : G →* G) X).subgroupOf B :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (hc1.trans (hc3.symm.trans hc2.symm))
  have hfin : Subgroup.map (φ : G →* G) X = X := by
    have hcong := congr_arg (Subgroup.map (B.subtype)) hY
    simp only [Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hXB] at hcong
    exact hcong.symm
  exact hfin

/-- If `A` is nilpotent, `A ⊓ M` is cyclic, `X ≤ A ⊓ M` and the normalizer in `G` of `X` lies
in `M`, then `A ≤ M`. -/
theorem le_of_isCyclic_inf_of_normalizer_le {G : Type} [Group G] [Finite G]
    {A M X : Subgroup G} (hnil : Group.IsNilpotent ↥A) (hcyc : IsCyclic ↥(A ⊓ M))
    (hX : X ≤ A ⊓ M) (hXne : X ≠ ⊥) (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    A ≤ M := by
  let B : Subgroup G := A ⊓ M
  have hBA : B ≤ A := inf_le_left
  have hX' : X ≤ B := hX
  have hcyc' : IsCyclic ↥B := hcyc
  -- `A ⊓ M` is cyclic, hence abelian, so it normalizes `X`.
  have hBnormX : B ≤ Subgroup.normalizer (X : Set G) := by
    letI : CommGroup ↥B := IsCyclic.commGroup
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    have hxB : x ∈ B := hX' hx
    have hcomm : b * x = x * b := by
      have h2 := mul_comm (⟨b, hb⟩ : ↥B) (⟨x, hxB⟩ : ↥B)
      exact congr_arg Subtype.val h2
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  -- The normalizer of `X` inside `A` is exactly `B`.
  have hNAX : A ⊓ Subgroup.normalizer (X : Set G) = B := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans hNX)
    · exact le_inf inf_le_left hBnormX
  -- Every element of `A` normalizing `B` normalizes `X` (subgroups of a cyclic group are
  -- characteristic), so the normalizer of `B` inside `A` is again exactly `B`.
  have hNAB : A ⊓ Subgroup.normalizer (B : Set G) = B := by
    apply le_antisymm
    · calc A ⊓ Subgroup.normalizer (B : Set G)
          ≤ A ⊓ Subgroup.normalizer (X : Set G) :=
              le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_of_isCyclic hcyc' hX'))
        _ = B := hNAX
    · exact le_inf hBA Subgroup.le_normalizer
  -- Since `A` is nilpotent, only `A` itself is self-normalizing, so `B = A`.
  haveI : Group.IsNilpotent ↥A := hnil
  have hnc : NormalizerCondition ↥A := Group.normalizerCondition_of_isNilpotent
  have hnormeq : Subgroup.normalizer ↑(B.subgroupOf A) = B.subgroupOf A := by
    rw [← Subgroup.subgroupOf_normalizer_eq hBA]
    rw [Subgroup.subgroupOf_inj]
    rw [inf_comm (Subgroup.normalizer (B : Set G)) A, hNAB, inf_eq_left.mpr hBA]
  have htop : B.subgroupOf A = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing (G := ↥A)).mp hnc
      (B.subgroupOf A) hnormeq
  have hAB : A ≤ B := by
    intro a ha
    have hmem : (⟨a, ha⟩ : ↥A) ∈ B.subgroupOf A := by
      rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  intro a ha
  have hmem : a ∈ A ⊓ M := hAB ha
  exact (Subgroup.mem_inf.mp hmem).2

end Work.CORE4.FpropsAux
