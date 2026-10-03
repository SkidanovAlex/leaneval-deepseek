import Mathlib
import Submission.Work.ORBassSerre.Interface

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Work.ORLocInd.CohenLyndon

open HNNExtension

/-! # The normal closure of `of r` inside an HNN extension meets the base in the right place

Let `K` be a group, `A B ≤ K`, `φ : A ≃* B` and `r ∈ K` with `⟪r⟫ ∩ A = ⟂` and `⟪r⟫ ∩ B = ⟂`.
Writing `G = HNNExtension K A B φ`, we show

`⟪of r⟫_G ⊓ of(K) = of(⟪r⟫_K)`.

The proof is a quotient argument: since `N := ⟪r⟫_K` meets `A` and `B` trivially, the subgroups
`A` and `B` embed in `K ⧸ N`, so `φ` descends to an isomorphism `φ̄` between their images; there is
therefore a canonical homomorphism `ψ` from `G` to the HNN extension of the quotient `K ⧸ N`.  It
vanishes on `of r`, and on the base group it has kernel exactly `N`. -/

/-- The canonical map sending a subgroup to its image under a quotient map. -/
private noncomputable def qSubgroupHom {K : Type u} [Group K] (N A : Subgroup K) [N.Normal] :
    A →* A.map (QuotientGroup.mk' N) where
  toFun a := ⟨QuotientGroup.mk' N (a : K), Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- A subgroup meeting the kernel of a quotient map trivially is isomorphic to its image. -/
private noncomputable def qSubgroupEquiv {K : Type u} [Group K] (N A : Subgroup K) [N.Normal]
    (h : N ⊓ A = ⊥) : A ≃* A.map (QuotientGroup.mk' N) :=
  MulEquiv.ofBijective (qSubgroupHom N A) ⟨fun a b hab => by
    have h1 : QuotientGroup.mk' N (a : K) = QuotientGroup.mk' N (b : K) :=
      congrArg Subtype.val hab
    have h2 : (a : K) / (b : K) ∈ N := by
      rw [← QuotientGroup.eq_iff_div_mem]; exact h1
    have h3 : (a : K) / (b : K) ∈ A ⊓ N :=
      Subgroup.mem_inf.mpr ⟨Subgroup.div_mem (H := A) a.2 b.2, h2⟩
    have h4 : (a : K) / (b : K) = 1 := by
      have := h3
      rw [inf_comm, h] at this
      simpa using this
    exact Subtype.ext (div_eq_one.mp h4),
   fun b => by
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp b.2
    exact ⟨⟨a, ha⟩, Subtype.ext haeq⟩⟩

private lemma qSubgroupEquiv_coe {K : Type u} [Group K] (N A : Subgroup K) [N.Normal]
    (h : N ⊓ A = ⊥) (a : A) :
    ((qSubgroupEquiv N A h a : A.map (QuotientGroup.mk' N)) : K ⧸ N) = QuotientGroup.mk' N (a : K) :=
  rfl

/-- The isomorphism induced by `φ` between the images of `A` and `B` in `K ⧸ N`. -/
private noncomputable def phiBar {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B)
    (N : Subgroup K) [N.Normal] (hA : N ⊓ A = ⊥) (hB : N ⊓ B = ⊥) :
    A.map (QuotientGroup.mk' N) ≃* B.map (QuotientGroup.mk' N) :=
  (qSubgroupEquiv N A hA).symm.trans (φ.trans (qSubgroupEquiv N B hB))

private lemma phiBar_apply {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B)
    (N : Subgroup K) [N.Normal] (hA : N ⊓ A = ⊥) (hB : N ⊓ B = ⊥) (a : A) :
    phiBar A B φ N hA hB (qSubgroupEquiv N A hA a) = qSubgroupEquiv N B hB (φ a) := by
  simp only [phiBar, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- The canonical homomorphism from `HNNExtension K A B φ` to the HNN extension of `K ⧸ N`. -/
private noncomputable def hnnQuotientHom {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B)
    (N : Subgroup K) [N.Normal] (hA : N ⊓ A = ⊥) (hB : N ⊓ B = ⊥) :
    HNNExtension K A B φ →*
      HNNExtension (K ⧸ N) (A.map (QuotientGroup.mk' N)) (B.map (QuotientGroup.mk' N))
        (phiBar A B φ N hA hB) :=
  HNNExtension.lift
    ((HNNExtension.of (A := A.map (QuotientGroup.mk' N))
        (B := B.map (QuotientGroup.mk' N))
        (φ := phiBar A B φ N hA hB)).comp (QuotientGroup.mk' N))
    (HNNExtension.t (A := A.map (QuotientGroup.mk' N))
      (B := B.map (QuotientGroup.mk' N)) (φ := phiBar A B φ N hA hB))
    (by
      intro a
      have h := HNNExtension.t_mul_of
        (A := A.map (QuotientGroup.mk' N)) (B := B.map (QuotientGroup.mk' N))
        (φ := phiBar A B φ N hA hB) (qSubgroupEquiv N A hA a)
      simp only [qSubgroupEquiv_coe, phiBar_apply] at h
      exact h)

private lemma hnnQuotientHom_of {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B)
    (N : Subgroup K) [N.Normal] (hA : N ⊓ A = ⊥) (hB : N ⊓ B = ⊥) (k : K) :
    hnnQuotientHom A B φ N hA hB (HNNExtension.of k) =
      HNNExtension.of (QuotientGroup.mk' N k) := by
  simp only [hnnQuotientHom, HNNExtension.lift_of, MonoidHom.comp_apply]

theorem hnn_inf_range_eq {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B) {r : K}
    (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥) :
    Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ)) ⊓
        (HNNExtension.of (A := A) (B := B) (φ := φ)).range =
      (Subgroup.normalClosure ({r} : Set K)).map
        (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
  classical
  let N : Subgroup K := Subgroup.normalClosure ({r} : Set K)
  haveI hNn : N.Normal := Subgroup.normalClosure_normal
  change Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ)) ⊓
      (HNNExtension.of (A := A) (B := B) (φ := φ)).range =
    N.map (HNNExtension.of (A := A) (B := B) (φ := φ))
  have hqr : QuotientGroup.mk' N r = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure (Set.mem_singleton r)
  let ψ := hnnQuotientHom A B φ N hA hB
  have hψdef : ψ = hnnQuotientHom A B φ N hA hB := rfl
  refine le_antisymm ?_ ?_
  · -- `⟪of r⟫ ⊓ of(K) ≤ of(N)`: the base element lies in `ker ψ`.
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxL, hxr⟩ := hx
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hxr
    have hLK : Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ))
        ≤ MonoidHom.ker ψ := by
      apply Subgroup.normalClosure_le_normal
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      show ψ (HNNExtension.of r) = 1
      rw [hψdef, hnnQuotientHom_of A B φ N hA hB r, hqr]
      exact map_one _
    have hmem : ψ (HNNExtension.of k) = 1 := MonoidHom.mem_ker.mp (hLK hxL)
    have h2 : HNNExtension.of (A := A.map (QuotientGroup.mk' N))
        (B := B.map (QuotientGroup.mk' N)) (φ := phiBar A B φ N hA hB)
        (QuotientGroup.mk' N k) = 1 := by
      rw [hψdef, hnnQuotientHom_of A B φ N hA hB k] at hmem
      exact hmem
    have hqk : QuotientGroup.mk' N k = 1 :=
      HNNExtension.of_injective (A := A.map (QuotientGroup.mk' N))
        (B := B.map (QuotientGroup.mk' N)) (phiBar A B φ N hA hB) (by simpa using h2)
    have hkq : (k : K ⧸ N) = 1 := by simpa using hqk
    have hkN : k ∈ N := (QuotientGroup.eq_one_iff k).mp hkq
    exact Subgroup.mem_map.mpr ⟨k, hkN, rfl⟩
  · -- `of(N) ≤ ⟪of r⟫ ⊓ of(K)`.
    rw [Subgroup.map_le_iff_le_comap]
    intro k hk
    rw [Subgroup.mem_comap, Subgroup.mem_inf]
    refine ⟨?_, MonoidHom.mem_range.mpr ⟨k, rfl⟩⟩
    have h : Subgroup.normalClosure ({r} : Set K) ≤
        (Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ))).comap
          (HNNExtension.of (A := A) (B := B) (φ := φ)) :=
      Subgroup.normalClosure_le_normal (by
        rintro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_comap.mpr (Subgroup.subset_normalClosure (Set.mem_singleton _)))
    exact h hk

end Work.ORLocInd.CohenLyndon
