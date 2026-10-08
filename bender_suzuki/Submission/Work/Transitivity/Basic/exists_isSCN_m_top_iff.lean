import Mathlib
import Submission.Work.LocalPrelim.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SCN_m` subgroups of a subgroup versus of the ambient group

For a subgroup `X` of a finite group `G`, the subgroups of `X` correspond bijectively (via
`Subgroup.map X.subtype` / `Subgroup.subgroupOf X`) to the subgroups of `G` contained in `X`.
This file shows that the property `IsSCN_m m` is transported by this correspondence, and draws
the consequence that the two existential statements

* `∃ A : Subgroup ↥X, IsSCN_m m ⊤ A`  (an `SCN_m`-subgroup of `X`, viewed as a group), and
* `∃ A : Subgroup G, IsSCN_m m X A`  (an `SCN_m`-subgroup of the subgroup `X` of `G`)

are equivalent.

The proof unpacks `IsSCN` into its four defining conditions and checks each of them under the
correspondence: containment, normality, commutativity and self-centralization (the last one is
the only one that needs an argument, namely that centralizing `B ≤ ↥X` inside `X` is the same as
centralizing its image in `G` and lying in `X`).
-/

open scoped Classical Pointwise

namespace Work.Transitivity.Basic

variable {G : Type*} [Group G]

/-- Commutativity transfers across a multiplicative equivalence. -/
theorem isMulCommutative_congr_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    IsMulCommutative H ↔ IsMulCommutative K := by
  constructor
  · intro h
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 := h.is_comm.comm (e.symm a) (e.symm b)
    simpa using congrArg e h1
  · intro h
    refine ⟨⟨fun a b => ?_⟩⟩
    refine e.injective ?_
    rw [map_mul, map_mul]
    exact h.is_comm.comm (e a) (e b)

/-- Mapping `B ≤ ↥X` to the ambient group and pulling back along `X.subtype` is the identity. -/
theorem comap_subtype_map_subtype_eq (X : Subgroup G) (B : Subgroup ↥X) :
    Subgroup.comap X.subtype (Subgroup.map X.subtype B) = B := by
  rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]

/-- `W ≤ X` is contained in the image of `B ≤ ↥X` under `X.subtype` exactly when its pullback
along `X.subtype` is contained in `B`. -/
theorem comap_le_iff_le_map_subtype (X : Subgroup G) (B : Subgroup ↥X) {W : Subgroup G}
    (hW : W ≤ X) :
    Subgroup.comap X.subtype W ≤ B ↔ W ≤ B.map X.subtype := by
  constructor
  · intro h x hx
    have hxX : x ∈ X := hW hx
    have hy : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.comap X.subtype W := hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, h hy, rfl⟩
  · intro h y hy
    have h' : X.subtype y ∈ B.map X.subtype := h hy
    rw [Subgroup.mem_map] at h'
    obtain ⟨b, hb, hbeq⟩ := h'
    have hby : b = y := X.subtype_injective hbeq
    rwa [hby] at hb

/-- The centralizer of the image of `B ≤ ↥X` in `G`, intersected with `X`, is the image of the
centralizer of `B` in `X`. -/
theorem comap_centralizer_map_subtype (X : Subgroup G) (B : Subgroup ↥X) :
    Subgroup.comap X.subtype
        (Subgroup.centralizer ((B.map X.subtype : Subgroup G) : Set G) ⊓ X)
      = Subgroup.centralizer (B : Set ↥X) := by
  ext y
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hcent, -⟩ b hb
    have h := hcent (X.subtype b) (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
    exact X.subtype_injective (by simpa [map_mul] using h)
  · intro hcent
    refine ⟨?_, y.property⟩
    rintro a ⟨b, hb, rfl⟩
    have h := hcent b hb
    simpa [map_mul] using congrArg X.subtype h

/-- `IsSCN` transfers from `⊤ ≤ ↥X` to the corresponding subgroup of `G` contained in `X`. -/
theorem isSCN_top_iff_map_subtype (X : Subgroup G) (B : Subgroup ↥X) :
    Work.LocalPrelim.IsSCN (⊤ : Subgroup ↥X) B ↔
      Work.LocalPrelim.IsSCN X (B.map X.subtype) := by
  have hnorm1 : (B.subgroupOf (⊤ : Subgroup ↥X)).Normal ↔ B.Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_top]
    constructor
    · intro h; exact ⟨fun n hn g => h n g hn trivial⟩
    · intro h n k hn _; exact h.conj_mem n hn k
  have hnorm2 : ((B.map X.subtype).subgroupOf X).Normal ↔ B.Normal := by
    have hEq : (B.map X.subtype).subgroupOf X = B := by
      show Subgroup.comap X.subtype (Subgroup.map X.subtype B) = B
      exact comap_subtype_map_subtype_eq X B
    rw [hEq]
  have hnorm : (B.subgroupOf (⊤ : Subgroup ↥X)).Normal ↔
      ((B.map X.subtype).subgroupOf X).Normal := hnorm1.trans hnorm2.symm
  have hcomm : IsMulCommutative B ↔ IsMulCommutative (B.map X.subtype) :=
    isMulCommutative_congr_mulEquiv
      (Subgroup.equivMapOfInjective B X.subtype X.subtype_injective)
  have hcent : (Subgroup.centralizer (B : Set ↥X) ⊓ ⊤ ≤ B) ↔
      (Subgroup.centralizer ((B.map X.subtype : Subgroup G) : Set G) ⊓ X ≤
        B.map X.subtype) := by
    have hZ : Subgroup.comap X.subtype
        (Subgroup.centralizer ((B.map X.subtype : Subgroup G) : Set G) ⊓ X)
        = Subgroup.centralizer (B : Set ↥X) := comap_centralizer_map_subtype X B
    rw [inf_top_eq]
    constructor
    · intro h
      have h' : Subgroup.comap X.subtype
          (Subgroup.centralizer ((B.map X.subtype : Subgroup G) : Set G) ⊓ X) ≤ B := by
        rw [hZ]; exact h
      exact (comap_le_iff_le_map_subtype X B inf_le_right).mp h'
    · intro h
      have h' : Subgroup.comap X.subtype
          (Subgroup.centralizer ((B.map X.subtype : Subgroup G) : Set G) ⊓ X) ≤ B :=
        (comap_le_iff_le_map_subtype X B inf_le_right).mpr h
      rwa [hZ] at h'
  rw [Work.LocalPrelim.IsSCN, Work.LocalPrelim.IsSCN]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨Subgroup.map_subtype_le B, hnorm.mp h1, hcomm.mp h2, hcent.mp h3⟩
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨le_top, hnorm.mpr h1, hcomm.mpr h2, hcent.mpr h3⟩

/-- `IsSCN_m` transfers from `⊤ ≤ ↥X` to the corresponding subgroup of `G` contained in `X`.
The rank is unaffected because `Subgroup.equivMapOfInjective` is an isomorphism onto the image. -/
theorem isSCN_m_top_iff_map_subtype [Finite G] (m : ℕ) (X : Subgroup G) (B : Subgroup ↥X) :
    Work.LocalPrelim.IsSCN_m m (⊤ : Subgroup ↥X) B ↔
      Work.LocalPrelim.IsSCN_m m X (B.map X.subtype) := by
  have hrank : Group.rank ↥B = Group.rank ↥(B.map X.subtype) :=
    Group.rank_congr (Subgroup.equivMapOfInjective B X.subtype X.subtype_injective)
  rw [Work.LocalPrelim.IsSCN_m, Work.LocalPrelim.IsSCN_m]
  exact and_congr (isSCN_top_iff_map_subtype X B) (by rw [hrank])

theorem exists_isSCN_m_top_iff {G : Type*} [Group G] [Finite G] (m : ℕ) (X : Subgroup G) :
    (∃ A : Subgroup ↥X, Work.LocalPrelim.IsSCN_m m (⊤ : Subgroup ↥X) A) ↔
      (∃ A : Subgroup G, Work.LocalPrelim.IsSCN_m m X A) := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B.map X.subtype, (isSCN_m_top_iff_map_subtype m X B).mp hB⟩
  · rintro ⟨A, hA⟩
    refine ⟨A.subgroupOf X, (isSCN_m_top_iff_map_subtype m X (A.subgroupOf X)).mpr ?_⟩
    rw [Subgroup.map_subgroupOf_eq_of_le hA.1.1]
    exact hA

end Work.Transitivity.Basic
