import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.CosetInvCountLeSix

/-!
# Bender 1981 §3 (5) ⟹ `n ≠ 5`

Given Bender's (5), the inverted set `I_Ĥ(y) = invSetIn Ĥ y` of an involution `y ∉ Ĥ` injects
into `H = Ĥ/VU ≅ S₃` (a nonabelian group of order `6`).  Its image `Q` therefore satisfies
`|Q| = |I_Ĥ(y)|`, `1 ∈ Q`, `Q⁻¹ = Q`, and: conjugation by an element of `Q` of order `2`
preserves `Q` (because such an element is the image of an *involution* of `I_Ĥ(y)`, and
conjugation by an involution of `I_Ĥ(y)` preserves `I_Ĥ(y)`).

Hence `|I_Ĥ(y)| = 5` is impossible — the combinatorial fact `OrderSixNoFiveSubset`.  This file
proves the reduction, taking that combinatorial input as an explicit hypothesis
(`cosetInvCount_ne_five_of`).
-/

namespace Work.CORE3

open Work.GW2
open Subgroup

/-- Conjugation by an involution `x` inverted by the involution `y` preserves the inverted set:
if `y x y = x⁻¹`, `y w y = w⁻¹` and `x * x = 1` then `y (x w x⁻¹) y = (x w x⁻¹)⁻¹`. -/
theorem conj_mem_invSet_of_sq_eq_one {G : Type} [Group G] {y x w : G} (hy : y * y = 1)
    (hx : y * x * y = x⁻¹) (hw : y * w * y = w⁻¹) (hx2 : x * x = 1) :
    y * (x * w * x⁻¹) * y = (x * w * x⁻¹)⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyx : y * x * y = x := by rw [hx, hxinv]
  have hyxi : y * x⁻¹ * y = x := by rw [hxinv, hyx]
  have hkey : x * w⁻¹ * x = (x * w * x⁻¹)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hxinv]
    group
  calc y * (x * w * x⁻¹) * y
      = (y * x * y) * (y * w * y) * (y * x⁻¹ * y) := by
        rw [show x * w * x⁻¹ = (x * w) * x⁻¹ from by group,
          ← mul_conj_mul hy (x * w) x⁻¹, ← mul_conj_mul hy x w]
    _ = x * w⁻¹ * x := by rw [hyx, hw, hyxi]
    _ = (x * w * x⁻¹)⁻¹ := hkey

/-- **Reduction of `n ≠ 5` to a finite combinatorial fact.**  Assuming the combinatorial lemma
`hcomb` about nonabelian groups of order `6`, Bender's (5) implies that no coset of `Ĥ`
containing an involution `y ∉ Ĥ` contains exactly five involutions. -/
theorem cosetInvCount_ne_five_of (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1})
    (hcomb : ∀ (K : Type) [Group K] [Finite K], Nat.card K = 6 → ¬ IsMulCommutative K →
      ∀ Q : Set K, Q.ncard = 5 → (1 : K) ∈ Q → (∀ q ∈ Q, q⁻¹ ∈ Q) →
      (∀ q ∈ Q, q * q = 1 → ∀ r ∈ Q, q * r * q⁻¹ ∈ Q) → False) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y ≠ 5 := by
  intro y hy2 hyH hcnt5
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hy : y * y = 1 := (orderOf_eq_two_iff_mul_self y).mp hy2 |>.1
  have h5' : ∀ z : G, z * z = 1 → z ∉ B.Hhat → invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} := by
    intro z hz hzH
    have hz1 : z ≠ 1 := by rintro rfl; exact hzH B.Hhat.one_mem
    exact h5 z ((orderOf_eq_two_iff_mul_self z).mpr ⟨hz, hz1⟩) hzH
  have hWle : pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat :=
    sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have hWn : ((pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat).Normal :=
    normal_VU_subgroupOf G I h B h1 D
  have hrel : (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := relIndex_VU_Hhat G I h B h1 D
  let N : Subgroup ↥B.Hhat := (pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat
  haveI : N.Normal := hWn
  -- the lift `S'` of `invSetIn Ĥ y` to `↥Ĥ`
  let S' : Set ↥B.Hhat := {x : ↥B.Hhat | (x : G) ∈ invSetIn B.Hhat y}
  have hcong : S'.ncard = (invSetIn B.Hhat y).ncard := by
    refine Set.ncard_congr (fun x _ => (x : G)) ?_ ?_ ?_
    · intro x hx; exact hx
    · intro a b _ _ hab; exact Subtype.ext hab
    · intro b hb; exact ⟨⟨b, hb.1⟩, hb, rfl⟩
  have hS'card : S'.ncard = 5 := by
    rw [hcong, ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]; exact hcnt5
  -- injectivity of `↥Ĥ → Ĥ/VU` on `S'`
  have hφinj : Set.InjOn (⇑(QuotientGroup.mk' N)) S' := by
    intro x hx x' hx' heq
    have heq' : (QuotientGroup.mk x : ↥B.Hhat ⧸ N) = QuotientGroup.mk x' := by
      simpa only [QuotientGroup.mk'_apply] using heq
    rw [QuotientGroup.eq] at heq'
    have hmem : ((x⁻¹ * x' : ↥B.Hhat) : G) ∈ (pCoreIn 2 B.Hhat ⊔ B.U) :=
      Subgroup.mem_subgroupOf.mp heq'
    have hmem' : (x : G)⁻¹ * (x' : G) ∈ (pCoreIn 2 B.Hhat ⊔ B.U) := by simpa using hmem
    have hconj : (x' : G) * (x : G)⁻¹ ∈ (pCoreIn 2 B.Hhat ⊔ B.U) := by
      have hnorm := (Subgroup.normal_subgroupOf_iff hWle).mp hWn
      have hh := hnorm ((x : G)⁻¹ * (x' : G)) (x : G) hmem' x.2
      simpa [mul_assoc] using hh
    exact Subtype.ext (invSetIn_eq_of_mul_inv_mem hWle h5' hy hyH hx' hx hconj).symm
  -- the image `Q` in `H = Ĥ/VU`
  have hQcard : ((⇑(QuotientGroup.mk' N)) '' S').ncard = 5 := by
    have himg : ((⇑(QuotientGroup.mk' N)) '' S').ncard = S'.ncard :=
      (Set.ncard_congr (s := S') (t := (⇑(QuotientGroup.mk' N)) '' S')
        (f := fun x (_ : x ∈ S') => QuotientGroup.mk' N x)
        (fun x hx => Set.mem_image_of_mem (⇑(QuotientGroup.mk' N)) hx)
        (fun a b ha hb hab => hφinj ha hb hab)
        (fun z hz => by
          obtain ⟨x, hx, hfl⟩ := (Set.mem_image (⇑(QuotientGroup.mk' N)) S' z).mp hz
          exact ⟨x, hx, hfl⟩)).symm
    rw [himg, hS'card]
  have hQ1 : (1 : ↥B.Hhat ⧸ N) ∈ (⇑(QuotientGroup.mk' N)) '' S' := by
    have h1mem : (1 : ↥B.Hhat) ∈ S' := by
      show ((1 : ↥B.Hhat) : G) ∈ invSetIn B.Hhat y
      simpa using one_mem_invSetIn (Hh := B.Hhat) (y := y) hy
    exact (Set.mem_image (⇑(QuotientGroup.mk' N)) S' (1 : ↥B.Hhat ⧸ N)).mpr
      ⟨1, h1mem, by simp⟩
  have hQinv : ∀ q ∈ (⇑(QuotientGroup.mk' N)) '' S', q⁻¹ ∈ (⇑(QuotientGroup.mk' N)) '' S' := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := (Set.mem_image (⇑(QuotientGroup.mk' N)) S' q).mp hq
    exact (Set.mem_image (⇑(QuotientGroup.mk' N)) S' ((QuotientGroup.mk' N x))⁻¹).mpr
      ⟨x⁻¹, inv_mem_invSetIn (Hh := B.Hhat) (y := y) hy hx, by simp only [map_inv]⟩
  have hQconj : ∀ q ∈ (⇑(QuotientGroup.mk' N)) '' S', q * q = 1 →
      ∀ r ∈ (⇑(QuotientGroup.mk' N)) '' S',
        q * r * q⁻¹ ∈ (⇑(QuotientGroup.mk' N)) '' S' := by
    intro q hq hq2 r hr
    obtain ⟨x, hx, rfl⟩ := (Set.mem_image (⇑(QuotientGroup.mk' N)) S' q).mp hq
    obtain ⟨z, hz, rfl⟩ := (Set.mem_image (⇑(QuotientGroup.mk' N)) S' r).mp hr
    -- `x` is an involution of `G`
    have hq2' : QuotientGroup.mk' N (x * x) = 1 := by rw [map_mul, hq2]
    have hmemN : (x * x : ↥B.Hhat) ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N)]
      exact MonoidHom.mem_ker.mpr hq2'
    have hx2W : (x : G) * (x : G) ∈ (pCoreIn 2 B.Hhat ⊔ B.U) := by
      have hh := Subgroup.mem_subgroupOf.mp hmemN
      simpa [N] using hh
    have hsq : y * ((x : G) * (x : G)) * y⁻¹ = ((x : G) * (x : G))⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hy]
      rw [← mul_conj_mul hy (x : G) (x : G), hx.2, mul_inv_rev]
    have hmem1 : (x : G) * (x : G) ∈ invSet (pCoreIn 2 B.Hhat ⊔ B.U) y := ⟨hx2W, hsq⟩
    rw [h5 y hy2 hyH] at hmem1
    have hx2G : (x : G) * (x : G) = 1 := Set.mem_singleton_iff.mp hmem1
    have hxz : x * z * x⁻¹ ∈ S' := by
      show ((x * z * x⁻¹ : ↥B.Hhat) : G) ∈ invSetIn B.Hhat y
      have hmem' := conj_mem_invSet_of_sq_eq_one hy hx.2 hz.2 hx2G
      exact ⟨B.Hhat.mul_mem (B.Hhat.mul_mem x.2 z.2) (B.Hhat.inv_mem x.2), hmem'⟩
    exact (Set.mem_image (⇑(QuotientGroup.mk' N)) S'
      (QuotientGroup.mk' N x * QuotientGroup.mk' N z * (QuotientGroup.mk' N x)⁻¹)).mpr
      ⟨x * z * x⁻¹, hxz, by simp only [map_mul, map_inv]⟩
  -- the commutator witness makes `H` nonabelian
  have hnab0 : ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat,
      a * b * a⁻¹ * b⁻¹ ∉ (pCoreIn 2 B.Hhat ⊔ B.U) := by
    rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, -, hnab⟩
    · exact absurd (isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
        (not_isCyclic_of_isFourGroup' D.four)
    · exact hnab
  have hQnab : ¬ IsMulCommutative (↥B.Hhat ⧸ N) := by
    intro hc
    obtain ⟨a, ha, b, hb, hcomm⟩ := hnab0
    apply hcomm
    have hcy := (isMulCommutative_iff.mp hc)
      (QuotientGroup.mk' N (⟨a, ha⟩ : ↥B.Hhat)) (QuotientGroup.mk' N (⟨b, hb⟩ : ↥B.Hhat))
    have h1 : QuotientGroup.mk' N
        ((⟨a, ha⟩ : ↥B.Hhat) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcy]
      group
    have hN : ((⟨a, ha⟩ : ↥B.Hhat) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N)]
      exact MonoidHom.mem_ker.mpr h1
    have hmem := Subgroup.mem_subgroupOf.mp hN
    simpa [N] using hmem
  have hcard6 : Nat.card (↥B.Hhat ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]
    exact hrel
  exact hcomb _ hcard6 hQnab ((⇑(QuotientGroup.mk' N)) '' S') hQcard hQ1 hQinv hQconj

end Work.CORE3
