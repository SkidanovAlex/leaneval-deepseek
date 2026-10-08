import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.GL32

/-- Conjugation by `b` maps `zpowers a` onto `zpowers (b * a * b⁻¹)`. -/
private lemma map_conj_zpowers {G : Type*} [Group G] (a b : G) :
    Subgroup.map (MulAut.conj b : G →* G) (Subgroup.zpowers a) =
      Subgroup.zpowers (b * a * b⁻¹) := by
  rw [MonoidHom.map_zpowers]
  show Subgroup.zpowers ((MulAut.conj b : MulAut G) a) = Subgroup.zpowers (b * a * b⁻¹)
  rw [MulAut.conj_apply]

theorem mem_normalizer_zpowers_of_zpowers_conj {G : Type*} [Group G] (a b : G)
    (h : Subgroup.zpowers (b * a * b⁻¹) = Subgroup.zpowers a) :
    b ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  have key : Subgroup.map (MulAut.conj b : G →* G) (Subgroup.zpowers a) = Subgroup.zpowers a := by
    rw [map_conj_zpowers, h]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  show x ∈ Subgroup.zpowers a ↔ (MulAut.conj b : G →* G) x ∈ Subgroup.zpowers a
  have hiff : x ∈ Subgroup.zpowers a ↔
      (MulAut.conj b : G →* G) x ∈
        Subgroup.map (MulAut.conj b : G →* G) (Subgroup.zpowers a) :=
    (Subgroup.mem_map_iff_mem (MulAut.conj b).injective).symm
  rwa [key] at hiff

end Work.Hering.GL32
