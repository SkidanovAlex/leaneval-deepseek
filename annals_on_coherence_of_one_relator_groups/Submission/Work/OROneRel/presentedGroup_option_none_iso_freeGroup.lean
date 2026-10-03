import Mathlib

namespace Work.OROneRel

universe u

/-- **The one-relator group `⟨Option γ | of none⟩` is free on `γ`.**

The relation `of none = 1` determines the generator `none` and imposes nothing on the others, so
`⟨Option γ | of none⟩ ≃* FreeGroup γ`. -/
theorem presentedGroup_option_none_iso_freeGroup {γ : Type u} :
    Nonempty (PresentedGroup ({FreeGroup.of (none : Option γ)} : Set (FreeGroup (Option γ)))
      ≃* FreeGroup γ) := by
  classical
  -- The map on generators killing `none` and fixing the `some` generators.
  let f : Option γ → FreeGroup γ := fun a => match a with | none => 1 | some b => FreeGroup.of b
  -- The single relator `of none` is killed by the induced lift.
  have hf : ∀ r ∈ ({FreeGroup.of (none : Option γ)} : Set (FreeGroup (Option γ))),
      FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [FreeGroup.lift_apply_of]
  -- `τ : ⟨Option γ | of none⟩ →* F(γ)`.
  let τ : PresentedGroup ({FreeGroup.of (none : Option γ)} : Set (FreeGroup (Option γ))) →*
      FreeGroup γ := PresentedGroup.toGroup (f := f) hf
  -- `σ : F(γ) →* ⟨Option γ | of none⟩` sending `b ↦ of (some b)`.
  let σ : FreeGroup γ →*
      PresentedGroup ({FreeGroup.of (none : Option γ)} : Set (FreeGroup (Option γ))) :=
    FreeGroup.lift fun b => PresentedGroup.of (some b)
  have h1 : τ.comp σ = MonoidHom.id (FreeGroup γ) := by
    refine FreeGroup.ext_hom _ _ fun b => ?_
    show τ (σ (FreeGroup.of b)) = FreeGroup.of b
    rw [show σ (FreeGroup.of b) = PresentedGroup.of (some b) from FreeGroup.lift_apply_of,
      PresentedGroup.toGroup.of hf]
  have h2 : σ.comp τ = MonoidHom.id _ := by
    refine PresentedGroup.ext fun a => ?_
    show σ (τ (PresentedGroup.of a)) = PresentedGroup.of a
    rcases a with _ | b
    · -- the generator `none` is trivial in the presented group
      rw [show τ (PresentedGroup.of none) = f none from PresentedGroup.toGroup.of hf]
      show σ (f none) = _
      rw [show f none = 1 from rfl, map_one]
      exact (PresentedGroup.one_of_mem (Set.mem_singleton _)).symm
    · rw [show τ (PresentedGroup.of (some b)) = f (some b) from PresentedGroup.toGroup.of hf,
        show f (some b) = FreeGroup.of b from rfl,
        show σ (FreeGroup.of b) = PresentedGroup.of (some b) from FreeGroup.lift_apply_of]
  exact ⟨MonoidHom.toMulEquiv τ σ h2 h1⟩

end Work.OROneRel
