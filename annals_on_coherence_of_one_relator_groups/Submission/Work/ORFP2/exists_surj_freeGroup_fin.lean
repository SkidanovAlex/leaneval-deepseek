import Mathlib

namespace Work.ORFP2

theorem exists_surj_freeGroup_fin {G : Type*} [Group G] (h : Group.FG G) :
    ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G), Function.Surjective φ := by
  obtain ⟨α, _hα, φ, hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp h
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  refine ⟨n, φ.comp (FreeGroup.freeGroupCongr e).symm, ?_⟩
  exact hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective

end Work.ORFP2
