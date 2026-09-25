import Mathlib
import Submission.Work.Tower.Defs

namespace Work.Tower.Shafarevich.Rank

/-- If `G` is a quotient of the free group on `m` generators and `m ≤ d`, then `G` is also a
quotient of the free group on `d` generators (the extra generators are sent to `1`). -/
theorem exists_surj_freeGroup_of_le {G : Type} [Group G] {m d : ℕ} (hmd : m ≤ d)
    {ψ : FreeGroup (Fin m) →* G} (hψ : Function.Surjective ψ) :
    ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ := by
  classical
  let f : Fin m → G := ⇑ψ ∘ FreeGroup.of
  have hfl : FreeGroup.lift f = ψ := FreeGroup.lift.apply_symm_apply ψ
  let g : Fin d → G := fun j => if h : j.val < m then f ⟨j.val, h⟩ else 1
  have hrange : Set.range f ⊆ Set.range g := by
    rintro _ ⟨a, rfl⟩
    exact ⟨Fin.castLE hmd a, dite_eq_left a.isLt⟩
  have hclf : Subgroup.closure (Set.range f) = ⊤ := by
    rw [← FreeGroup.range_lift_eq_closure, hfl, MonoidHom.range_eq_top]
    exact hψ
  have hclg : Subgroup.closure (Set.range g) = ⊤ :=
    top_unique (hclf ▸ Subgroup.closure_mono hrange)
  exact ⟨FreeGroup.lift g, FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hclg⟩

theorem generatorRank_le_iff {G : Type} [Group G] [Finite G] (d : ℕ) :
    Work.Tower.generatorRank G ≤ d ↔
      ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ := by
  classical
  unfold Work.Tower.generatorRank
  constructor
  · intro hd
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
    have hne : Set.Nonempty {m : ℕ | ∃ φ : FreeGroup (Fin m) →* G, Function.Surjective φ} :=
      ⟨n, FreeGroup.lift ⇑e.symm, FreeGroup.lift_surjective_of_surjective e.symm.surjective⟩
    obtain ⟨ψ, hψ⟩ := Nat.sInf_mem hne
    exact exists_surj_freeGroup_of_le hd hψ
  · rintro ⟨φ, hφ⟩
    exact Nat.sInf_le ⟨φ, hφ⟩

end Work.Tower.Shafarevich.Rank
