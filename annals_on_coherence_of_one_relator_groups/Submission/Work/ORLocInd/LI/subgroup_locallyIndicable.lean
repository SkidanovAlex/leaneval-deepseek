import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.LI

/-- The image of a finitely generated subgroup under a group homomorphism is finitely generated. -/
theorem subgroup_fg_map {G N : Type*} [Group G] [Group N] (f : G →* N) {K : Subgroup G}
    (hK : K.FG) : (K.map f).FG := by
  classical
  obtain ⟨S, hS⟩ := Subgroup.isMulFG_iff.mp hK
  exact Subgroup.isMulFG_iff.mpr ⟨S.image f, by rw [← hS, MonoidHom.map_closure, Finset.coe_image]⟩

theorem subgroup_locallyIndicable {G : Type*} [Group G] (h : Group.LocallyIndicable G)
    (H : Subgroup G) : Group.LocallyIndicable H := by
  intro K hK hKbot
  have hmap : (K.map H.subtype).FG := subgroup_fg_map H.subtype hK
  have hne : K.map H.subtype ≠ ⊥ := by
    intro hzero
    apply hKbot
    rw [eq_bot_iff]
    intro x hx
    have hx' : H.subtype x ∈ K.map H.subtype := ⟨x, hx, rfl⟩
    rw [hzero, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  obtain ⟨f, hf⟩ := h (K.map H.subtype) hmap hne
  refine ⟨f.comp (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := hf y
  refine ⟨(K.equivMapOfInjective H.subtype H.subtype_injective).symm z, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulEquiv.apply_symm_apply, hz]

end Work.ORLocInd.LI
