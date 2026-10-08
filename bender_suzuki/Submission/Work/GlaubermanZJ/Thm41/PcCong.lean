import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.Symmetry
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.Structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The congruence `[y,c,b] ≡ [y,b,c]` modulo `[B,B]`

This file proves the congruence used in the last step of Glauberman's proof of Theorem 4.1: if
`A, B ≤ H`, `H ≤ N(B)`, `A` is abelian and `y ∈ B`, `b, c ∈ A`, then
`[y,c,b] · [y,b,c]⁻¹ ∈ [B,B]` (Glauberman's commutator `[u,v] = u⁻¹v⁻¹uv`).

The proof passes to the quotient `H/[B,B]`, where the image of `B` is an abelian normal subgroup
and the image of `A` is abelian, and applies the symmetry lemma `pcomm_pcomm_comm`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- A monoid homomorphism commutes with `pcomm`. -/
theorem map_pcomm {H : Type*} [Group H] (f : G →* H) (u v : G) :
    f (pcomm u v) = pcomm (f u) (f v) := by
  simp only [pcomm, map_mul, map_inv]

/-- `[u⁻¹,v⁻¹] = (v·u)·[u,v]·(v·u)⁻¹`. -/
theorem pcomm_inv_inv (u v : G) : pcomm u⁻¹ v⁻¹ = (v * u) * pcomm u v * (v * u)⁻¹ := by
  simp only [pcomm]
  group

/-- `[u,v] ∈ B` when `u ∈ B` and `v` normalizes `B`. -/
theorem pcomm_mem_of_mem {H A B : Subgroup G} (hBH : B ≤ H) (hAH : A ≤ H)
    (hHn : H ≤ Subgroup.normalizer (B : Set G)) {u v : G} (hu : u ∈ B) (hv : v ∈ A) :
    pcomm u v ∈ B := by
  have hvB : v⁻¹ * u * v ∈ B := by
    have := (Subgroup.mem_normalizer_iff.mp (hHn (H.inv_mem (hAH hv))) u).mp hu
    simpa using this
  rw [show pcomm u v = u⁻¹ * (v⁻¹ * u * v) from by simp only [pcomm]; group]
  exact B.mul_mem (B.inv_mem hu) hvB

/-- **The symmetry of the iterated commutator modulo `[B,B]`.**  If `A, B ≤ H`, `H ≤ N(B)` and
`A` is abelian, then for `y ∈ B`, `b, c ∈ A` the elements `[[y,c],b]` and `[[y,b],c]` agree
modulo `[B,B]`. -/
theorem pcomm_pcomm_sub_mem {H A B : Subgroup G} (hBH : B ≤ H) (hAH : A ≤ H)
    (hHn : H ≤ Subgroup.normalizer (B : Set G)) (hAab : IsMulCommutative A)
    {y b c : G} (hy : y ∈ B) (hb : b ∈ A) (hc : c ∈ A) :
    pcomm (pcomm y c) b * (pcomm (pcomm y b) c)⁻¹ ∈ ⁅B, B⁆ := by
  have hV : pcomm y c ∈ B := pcomm_mem_of_mem hBH hAH hHn hy hc
  have hU : pcomm y b ∈ B := pcomm_mem_of_mem hBH hAH hHn hy hb
  have hP : pcomm (pcomm y c) b ∈ B := pcomm_mem_of_mem hBH hAH hHn hV hb
  have hQ : pcomm (pcomm y b) c ∈ B := pcomm_mem_of_mem hBH hAH hHn hU hc
  have hBBleB : (⁅B, B⁆ : Subgroup G) ≤ B := Subgroup.commutator_le_self B
  have hNle : (⁅B, B⁆ : Subgroup G) ≤ H := hBBleB.trans hBH
  have hHnBB : H ≤ Subgroup.normalizer (⁅B, B⁆ : Subgroup G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (⁅B, B⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅B, B⁆
    have hBmap : B.map (MulAut.conj h).toMonoidHom = B := by
      have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHn hh)
      change B.map (MulAut.conj h).toMonoidHom = B at this
      exact this
    rw [Subgroup.map_commutator B B (MulAut.conj h).toMonoidHom, hBmap]
  let N : Subgroup ↥H := (⁅B, B⁆ : Subgroup G).subgroupOf H
  haveI hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hHnBB
  let CB : Subgroup (↥H ⧸ N) := (B.subgroupOf H).map (QuotientGroup.mk' N)
  let CA : Subgroup (↥H ⧸ N) := (A.subgroupOf H).map (QuotientGroup.mk' N)
  have hCBnormal : CB.Normal :=
    Subgroup.Normal.map
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hBH).mpr hHn) _
      (QuotientGroup.mk'_surjective N)
  have hCBab : IsMulCommutative ↥CB := by
    rw [← Subgroup.commutator_self_eq_bot_iff, eq_bot_iff, Subgroup.commutator_le]
    rintro u ⟨b₁, hb₁, rfl⟩ v ⟨b₂, hb₂, rfl⟩
    have hmem : ⁅b₁, b₂⁆ ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      show ⁅(b₁ : G), (b₂ : G)⁆ ∈ ⁅B, B⁆
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hb₁)
        (Subgroup.mem_subgroupOf.mp hb₂)
    show ⁅(QuotientGroup.mk' N) b₁, (QuotientGroup.mk' N) b₂⁆ = 1
    rw [← map_commutatorElement (QuotientGroup.mk' N) b₁ b₂]
    exact (QuotientGroup.eq_one_iff ⁅b₁, b₂⁆).mpr hmem
  have hCAab : IsMulCommutative ↥CA := Subgroup.map_isMulCommutative (A.subgroupOf H) _
  have hkey : (QuotientGroup.mk' N) (⟨pcomm (pcomm y c) b, hBH hP⟩ : ↥H) =
      (QuotientGroup.mk' N) (⟨pcomm (pcomm y b) c, hBH hQ⟩ : ↥H) := by
    have hsymm := pcomm_pcomm_comm (C := CB) (A := CA) hCBnormal hCBab hCAab
      (x := (QuotientGroup.mk' N) ⟨y, hBH hy⟩)
      (b := (QuotientGroup.mk' N) ⟨b, hAH hb⟩)
      (c := (QuotientGroup.mk' N) ⟨c, hAH hc⟩)
      (Subgroup.mem_map.mpr ⟨⟨y, hBH hy⟩, hy, rfl⟩)
      (Subgroup.mem_map.mpr ⟨⟨b, hAH hb⟩, hb, rfl⟩)
      (Subgroup.mem_map.mpr ⟨⟨c, hAH hc⟩, hc, rfl⟩)
    rw [show (⟨pcomm (pcomm y c) b, hBH hP⟩ : ↥H) =
          pcomm ⟨pcomm y c, hBH hV⟩ ⟨b, hAH hb⟩ from Subtype.ext rfl,
        show (⟨pcomm (pcomm y b) c, hBH hQ⟩ : ↥H) =
          pcomm ⟨pcomm y b, hBH hU⟩ ⟨c, hAH hc⟩ from Subtype.ext rfl,
        show (⟨pcomm y c, hBH hV⟩ : ↥H) = pcomm ⟨y, hBH hy⟩ ⟨c, hAH hc⟩ from Subtype.ext rfl,
        show (⟨pcomm y b, hBH hU⟩ : ↥H) = pcomm ⟨y, hBH hy⟩ ⟨b, hAH hb⟩ from Subtype.ext rfl]
    simp only [map_pcomm]
    exact hsymm
  have h1 : (⟨pcomm (pcomm y c) b, hBH hP⟩ : ↥H)⁻¹ * ⟨pcomm (pcomm y b) c, hBH hQ⟩ ∈ N :=
    QuotientGroup.eq.mp hkey
  have h2 : (pcomm (pcomm y c) b)⁻¹ * (pcomm (pcomm y b) c) ∈ ⁅B, B⁆ :=
    Subgroup.mem_subgroupOf.mp h1
  have h3 : (pcomm (pcomm y b) c)⁻¹ * pcomm (pcomm y c) b ∈ ⁅B, B⁆ := by
    have := (⁅B, B⁆ : Subgroup G).inv_mem h2
    simpa using this
  have hQN : pcomm (pcomm y b) c ∈ Subgroup.normalizer (⁅B, B⁆ : Subgroup G) := hHnBB (hBH hQ)
  have h4 : pcomm (pcomm y b) c *
      ((pcomm (pcomm y b) c)⁻¹ * pcomm (pcomm y c) b) * (pcomm (pcomm y b) c)⁻¹ ∈ ⁅B, B⁆ :=
    ((Subgroup.mem_normalizer_iff.mp hQN)
      ((pcomm (pcomm y b) c)⁻¹ * pcomm (pcomm y c) b)).mp h3
  have h5 : pcomm (pcomm y b) c *
      ((pcomm (pcomm y b) c)⁻¹ * pcomm (pcomm y c) b) * (pcomm (pcomm y b) c)⁻¹ =
      pcomm (pcomm y c) b * (pcomm (pcomm y b) c)⁻¹ := by group
  rwa [h5] at h4

end Work.GlaubermanZJ
