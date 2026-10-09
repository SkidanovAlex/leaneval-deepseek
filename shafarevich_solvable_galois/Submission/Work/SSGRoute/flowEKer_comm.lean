/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The kernel copy `E p G m i j` of a graded piece is abelian

In Schmidt–Wingberg's Step 3 of Theorem 15 the level projection

`flowGroupProj p G m i j : F(m)/F(m)^{(τ+1)} ⋊ G →* F(m)/F(m)^{(τ)} ⋊ G`

has as its kernel `flowEKer p G m i j` the copy of the graded piece `E p G m i j` inside the
level-`τ+1` group.  The graded pieces of the refined `p`-central filtration are elementary
abelian `p`-groups (`Work.CohomologicalShrinking.commutator_refinedTerm_le`, Lemma 4 of the
paper), so this kernel is commutative; here we prove that fact, which is what makes
`flowEKer` an `𝔽_p[G]`-module and what the Scholz-property arguments use.

The proof is a three-step reduction:

* the kernel of a semidirect-product map with the identity on the right factor is (the image
  under `inl` of) the kernel of the map on the left factor (`flowEKer_eq_map_ker`);
* `flowQuotientProj` is `QuotientGroup.map` of the inclusion
  `F(m)^{(τ+1)}/… → F(m)^{(τ)}/…`, whose kernel is the image of
  `F(m)^{(τ)}` inside `F(m)/F(m)^{(τ+1)}` (`flowQuotientProj_ker_eq`);
* such a subgroup image is commutative as soon as `⁅M, M⁆ ≤ S`, which is exactly Lemma 4
  (`commutator_refinedTerm_le`).
-/

import Mathlib
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

open scoped commutatorElement

set_option maxHeartbeats 800000

/-! ## General group theory -/

/-- If `⁅M, M⁆ ≤ S` then the image of the subgroup `M` in `G ⧸ S` is commutative.

This is the statement "`H/(H ∩ S)` is abelian when `S` contains `⁅H, H⁆`", written for the
image `M.map (QuotientGroup.mk' S)` of `M` in the quotient, which avoids any hypothesis
`S ≤ M`. -/
theorem isMulCommutative_map_mk'_of_commutator_le {G : Type*} [Group G] {S M : Subgroup G}
    [S.Normal] (h : ⁅M, M⁆ ≤ S) : IsMulCommutative (M.map (QuotientGroup.mk' S)) := by
  rw [← Subgroup.commutator_self_eq_bot_iff]
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  show ⁅(QuotientGroup.mk' S) x, (QuotientGroup.mk' S) y⁆ ∈ (⊥ : Subgroup _)
  rw [Subgroup.mem_bot, ← map_commutatorElement (f := QuotientGroup.mk' S),
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.commutator_le.mp h x hx y hy

/-- A homomorphic image of a commutative subgroup is commutative. -/
theorem isMulCommutative_map_of {G N : Type*} [Group G] [Group N] (f : G →* N)
    {H : Subgroup G} (h : IsMulCommutative H) : IsMulCommutative (H.map f) := by
  rw [← Subgroup.commutator_self_eq_bot_iff] at h ⊢
  rw [← Subgroup.map_commutator, h, Subgroup.map_bot]

/-- The commutator of the subgroups `T.subgroupOf ⊤` of `⊤ ≤ F` is the commutator of `T`
inside the ambient group, intersected with `⊤`. -/
theorem commutator_subgroupOf_top_le {F : Type*} [Group F] {S T : Subgroup F}
    (h : ⁅T, T⁆ ≤ S) : ⁅T.subgroupOf ⊤, T.subgroupOf ⊤⁆ ≤ S.subgroupOf ⊤ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  have ha' : (a : F) ∈ T := Subgroup.mem_subgroupOf.mp ha
  have hb' : (b : F) ∈ T := Subgroup.mem_subgroupOf.mp hb
  have hc := Subgroup.commutator_le.mp h (a : F) ha' (b : F) hb'
  rw [show ((⁅a, b⁆ : ↥(⊤ : Subgroup F)) : F) = ⁅(a : F), (b : F)⁆ from by
    simp [commutatorElement_def]]
  exact hc

/-! ## The kernel of the level projection of the free factor -/

/-- The kernel of `flowQuotientProj p G m i j : F(m)/F(m)^{(τ+1)} →* F(m)/F(m)^{(τ)}` is the
image of the subgroup `F(m)^{(τ)}` in `F(m)/F(m)^{(τ+1)}`, i.e. the graded piece
`E p G m i j`. -/
theorem flowQuotientProj_ker_eq (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    (flowQuotientProj p G m i j).ker =
      Subgroup.map
        (QuotientGroup.mk' ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
        ((flowTerm p G m i j).subgroupOf ⊤) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ :=
      QuotientGroup.mk'_surjective ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤) x
    rw [Subgroup.mem_map]
    have hx' : flowQuotientProj p G m i j (QuotientGroup.mk' _ y) = 1 := hx
    rw [show flowQuotientProj p G m i j (QuotientGroup.mk' _ y)
        = QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf ⊤) y from rfl] at hx'
    exact ⟨y, (QuotientGroup.eq_one_iff y).mp hx', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [MonoidHom.mem_ker]
    rw [show flowQuotientProj p G m i j (QuotientGroup.mk' _ y)
        = QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf ⊤) y from rfl]
    exact (QuotientGroup.eq_one_iff y).mpr hy

/-- **The graded piece `E p G m i j` is abelian**: the kernel of the level projection of the
free factor is commutative, by Lemma 4 of Schmidt–Wingberg
(`commutator_refinedTerm_le`). -/
theorem isMulCommutative_flowQuotientProj_ker (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    IsMulCommutative (flowQuotientProj p G m i j).ker := by
  rw [flowQuotientProj_ker_eq]
  refine isMulCommutative_map_mk'_of_commutator_le
    (S := (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤) ?_
  exact commutator_subgroupOf_top_le
    (commutator_refinedTerm_le (P := Work.Shrinking.freeOperatorGroup G m) p i j)

/-! ## The kernel of the level projection of the semidirect product -/

/-- The kernel of the level projection `flowGroupProj` is the image, under the inclusion of the
free factor, of the kernel of `flowQuotientProj`: since the projection is the identity on `G`,
an element `inl a * inr g` of the level-`τ+1` group is killed precisely when `g = 1` and
`a ∈ ker flowQuotientProj`. -/
theorem flowEKer_eq_map_ker (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowEKer p G m i j =
      (flowQuotientProj p G m i j).ker.map (flowInl p G m (tauSucc i j).1 (tauSucc i j).2) := by
  ext x
  constructor
  · intro hx
    have hx1 : flowGroupProj p G m i j x = 1 := hx
    have hleft : flowQuotientProj p G m i j x.left = 1 := by
      have h := congrArg SemidirectProduct.left hx1
      simpa [flowGroupProj] using h
    have hright : x.right = 1 := by
      have h := congrArg SemidirectProduct.right hx1
      simpa [flowGroupProj, SemidirectProduct.rightHom_comp_map, MonoidHom.comp_apply] using h
    rw [Subgroup.mem_map]
    refine ⟨x.left, hleft, ?_⟩
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [hright, map_one, mul_one]
    rfl
  · rintro ⟨a, ha, rfl⟩
    show (flowInl p G m (tauSucc i j).1 (tauSucc i j).2) a ∈ (flowGroupProj p G m i j).ker
    rw [MonoidHom.mem_ker, flowGroupProj, flowInl, SemidirectProduct.map_inl]
    have ha' : flowQuotientProj p G m i j a = 1 := ha
    rw [ha', map_one]

/-! ## The requested statement -/

/-- The copy `flowEKer p G m i j` of the graded piece `E p G m i j` inside the level-`τ+1`
group is commutative. -/
theorem flowEKer_comm (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ∀ a b : Work.SSGRoute.flowEKer p G m i j, a * b = b * a := by
  have hcomm : IsMulCommutative (flowEKer p G m i j) := by
    rw [flowEKer_eq_map_ker]
    exact isMulCommutative_map_of _ (isMulCommutative_flowQuotientProj_ker p G m i j)
  intro a b
  exact hcomm.is_comm.comm a b

end Work.SSGRoute
