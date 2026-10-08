import Mathlib
import Submission.Work.LocalPrelim.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Transitivity.Basic

/-!
# `SCN_m(⊤)` is an isomorphism invariant

For a group `G` the predicate `IsSCN_m m ⊤ A` only depends on the isomorphism class of `G`:
if `e : X ≃* Y` is a group isomorphism, the existence of `A ≤ X` with `A ∈ SCN_m(⊤)`
is equivalent to the existence of such a subgroup in `Y`.

The proof transports `A` along `e` (`Subgroup.map`), showing first that, for the top subgroup,
`IsSCN ⊤ A` is exactly "`A` is normal and self-centralizing"
(`IsSCN_top_iff`), and that each of these clauses is preserved/reflected by an isomorphism.
-/

variable {X Y : Type*} [Group X] [Group Y]

/-- The centralizer of a subgroup is transported by a group isomorphism. -/
theorem centralizer_map_eq (e : X ≃* Y) (A : Subgroup X) :
    Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup Y) : Set Y)
      = (Subgroup.centralizer (A : Set X)).map e.toMonoidHom := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro a ha
    have h : e a * e x = e x * e a := hy (e a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [← map_mul, ← map_mul] at h
    exact e.injective h
  · simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (A : Set X) e.toMonoidHom

/-- For the ambient group itself (`P = ⊤`), `IsSCN ⊤ A` says that `A` is normal and
self-centralizing (equivalently `A` is normal and `C_G(A) = A`). -/
theorem IsSCN_top_iff (A : Subgroup X) :
    Work.LocalPrelim.IsSCN (⊤ : Subgroup X) A ↔
      A.Normal ∧ Subgroup.centralizer (A : Set X) = A := by
  constructor
  · intro h
    obtain ⟨-, hnormal, hcomm, hcent⟩ := h
    have hAN : A.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hnormal)
    have hle_cent : A ≤ Subgroup.centralizer (A : Set X) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
    have hcent' : Subgroup.centralizer (A : Set X) ≤ A := by simpa using hcent
    exact ⟨hAN, le_antisymm hcent' hle_cent⟩
  · rintro ⟨hAN, hcent⟩
    refine ⟨le_top, ?_, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
      exact top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hAN)
    · rw [← Subgroup.le_centralizer_iff_isMulCommutative]
      exact le_of_eq hcent.symm
    · rw [inf_top_eq]
      exact hcent.le

/-- `IsSCN ⊤` is preserved and reflected by a group isomorphism (via `Subgroup.map`). -/
theorem IsSCN_top_map_iff (e : X ≃* Y) (A : Subgroup X) :
    Work.LocalPrelim.IsSCN (⊤ : Subgroup Y) (A.map e.toMonoidHom) ↔
      Work.LocalPrelim.IsSCN (⊤ : Subgroup X) A := by
  rw [IsSCN_top_iff, IsSCN_top_iff]
  have hcent : Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup Y) : Set Y)
      = (Subgroup.centralizer (A : Set X)).map e.toMonoidHom := centralizer_map_eq e A
  constructor
  · rintro ⟨hnorm, hc⟩
    refine ⟨?_, ?_⟩
    · have h2 : ((A.map e.toMonoidHom).comap e.toMonoidHom).Normal :=
        hnorm.comap e.toMonoidHom
      rwa [Subgroup.comap_map_eq_self_of_injective e.injective A] at h2
    · have h2 : (Subgroup.centralizer (A : Set X)).map e.toMonoidHom = A.map e.toMonoidHom := by
        rw [← hcent, hc]
      exact Subgroup.map_injective e.injective h2
  · rintro ⟨hnorm, hc⟩
    refine ⟨?_, ?_⟩
    · exact hnorm.map e.toMonoidHom e.surjective
    · rw [hcent, hc]

/-- `IsSCN_m m ⊤` is preserved and reflected by a group isomorphism (via `Subgroup.map`). -/
theorem isSCN_m_top_map_iff [Finite X] [Finite Y] (e : X ≃* Y) (A : Subgroup X) {m : ℕ} :
    Work.LocalPrelim.IsSCN_m m (⊤ : Subgroup Y) (A.map e.toMonoidHom) ↔
      Work.LocalPrelim.IsSCN_m m (⊤ : Subgroup X) A := by
  unfold Work.LocalPrelim.IsSCN_m
  rw [IsSCN_top_map_iff e A]
  have hrank : Group.rank (A.map e.toMonoidHom) = Group.rank A :=
    Group.rank_congr (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).symm
  rw [hrank]

theorem exists_isSCN_m_top_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {m : ℕ} (e : X ≃* Y) :
    (∃ A : Subgroup X, Work.LocalPrelim.IsSCN_m m (⊤ : Subgroup X) A) ↔
      (∃ A : Subgroup Y, Work.LocalPrelim.IsSCN_m m (⊤ : Subgroup Y) A) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.map e.toMonoidHom, (isSCN_m_top_map_iff e A).mpr hA⟩
  · rintro ⟨B, hB⟩
    refine ⟨B.comap e.toMonoidHom, (isSCN_m_top_map_iff e (B.comap e.toMonoidHom)).mp ?_⟩
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective B]
    exact hB

end Work.Transitivity.Basic
