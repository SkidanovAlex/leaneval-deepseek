import Mathlib
import Submission.Work.OROneRel.wordOfDefs

universe u

namespace Work.OROneRel

noncomputable def killsProj {E : Type u} (T : Set E) : FreeGroup E →* FreeGroup ↥(Tᶜ) := by
  classical
  exact FreeGroup.lift fun e => if h : e ∈ T then 1 else FreeGroup.of ⟨e, h⟩

/-- **`π₁` of a graph-with-one-`2`-cell after deleting a spanning tree.**  Let `E` be the edge set
of a graph, `T ⊆ E` a set of "tree" edges (declared by fiat: the statement is the pure algebra of
killing the generators in `T`), and `w : FreeGroup E` the boundary word of the single `2`-cell.
Then the presentation with generators `E` and relators `{of e : e ∈ T} ∪ {w}` is the one-relator
presentation on the *remaining* edges `Tᶜ` with relator the projection of `w` under the map killing
`T`.  This is the identification `π₁(D) ≅ ⟨β | v ^ l⟩` used to identify the vertex group of the
`Z`-domain splitting with the coedge presentation of its walk. -/
theorem presentedGroup_treeDelete_iso {E : Type u} (T : Set E) (w : FreeGroup E) :
    Nonempty (PresentedGroup ({x : FreeGroup E |
        (∃ t : ↥T, x = FreeGroup.of (t : E)) ∨ x = w} : Set (FreeGroup E)) ≃*
      PresentedGroup ({killsProj T w} : Set (FreeGroup ↥(Tᶜ)))) := by
  classical
  -- The set of relators of the "big" presentation: the generators in `T`, together with `w`.
  let R : Set (FreeGroup E) := {x : FreeGroup E | (∃ t : ↥T, x = FreeGroup.of (t : E)) ∨ x = w}
  change Nonempty (PresentedGroup R ≃* PresentedGroup ({killsProj T w} : Set (FreeGroup ↥(Tᶜ))))
  -- The two maps on generators: `f₁` is the identity on the surviving generators (after killing
  -- `T`), `f₂` sends a surviving generator of the small presentation to the corresponding generator
  -- of the big one.
  let f₁ : E → PresentedGroup ({killsProj T w} : Set (FreeGroup ↥(Tᶜ))) :=
    fun e => if h : e ∈ T then 1 else PresentedGroup.of (⟨e, h⟩ : ↥(Tᶜ))
  let f₂ : ↥(Tᶜ) → PresentedGroup R := fun s => PresentedGroup.of (s.1 : E)
  have hR_of : ∀ t : ↥T, FreeGroup.of (t : E) ∈ R := fun t => Or.inl ⟨t, rfl⟩
  have hR_w : w ∈ R := Or.inr rfl
  have hkill : ∀ e : E, killsProj T (FreeGroup.of e) =
      (if h : e ∈ T then 1 else FreeGroup.of (⟨e, h⟩ : ↥(Tᶜ))) := by
    intro e
    simp [killsProj, FreeGroup.lift_apply_of]
  -- `FreeGroup.lift f₁` is `mk ∘ killsProj`.
  have hLift₁ : FreeGroup.lift f₁ =
      (PresentedGroup.mk ({killsProj T w} : Set (FreeGroup ↥(Tᶜ)))).comp (killsProj T) := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, hkill e]
    by_cases h : e ∈ T
    · simp only [f₁, map_one, dif_pos h]
    · simp only [f₁, dif_neg h]
      rfl
  have hker₁ : FreeGroup.lift f₁ w = 1 := by
    rw [hLift₁, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (Set.mem_singleton _)
  -- The map killing the `T`-generators, on the level of presented groups.
  let ρ : PresentedGroup R →* PresentedGroup ({killsProj T w} : Set (FreeGroup ↥(Tᶜ))) :=
    PresentedGroup.toGroup (f := f₁) (by
      intro x hx
      rcases hx with ⟨t, rfl⟩ | rfl
      · rw [FreeGroup.lift_apply_of]
        show f₁ (t : E) = 1
        simp only [f₁]
        rw [dif_pos t.2]
      · exact hker₁)
  have hρ_of : ∀ a : E, ρ (PresentedGroup.of a) = f₁ a := fun a => PresentedGroup.toGroup.of _
  -- `FreeGroup.lift f₂ ∘ killsProj` is the canonical map of the big presentation.
  have hLift₂ : (FreeGroup.lift f₂).comp (killsProj T) = PresentedGroup.mk R := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, hkill e]
    by_cases h : e ∈ T
    · rw [dif_pos h, map_one]
      exact (PresentedGroup.one_of_mem (hR_of ⟨e, h⟩)).symm
    · rw [dif_neg h, FreeGroup.lift_apply_of]
      rfl
  have hker₂ : FreeGroup.lift f₂ (killsProj T w) = 1 := by
    rw [← MonoidHom.comp_apply, hLift₂]
    exact PresentedGroup.one_of_mem hR_w
  -- The inverse map, sending a surviving generator to itself.
  let φ : PresentedGroup ({killsProj T w} : Set (FreeGroup ↥(Tᶜ))) →* PresentedGroup R :=
    PresentedGroup.toGroup (f := f₂) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hker₂)
  have hφ_of : ∀ s : ↥(Tᶜ), φ (PresentedGroup.of s) = f₂ s := fun s => PresentedGroup.toGroup.of _
  have hρφ : ρ.comp φ = MonoidHom.id _ := by
    refine PresentedGroup.ext fun s => ?_
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hφ_of, hρ_of]
    show f₁ (s.1 : E) = PresentedGroup.of s
    rw [show f₁ (s.1 : E) = PresentedGroup.of (⟨s.1, s.2⟩ : ↥(Tᶜ)) from dif_neg s.2]
  have hφρ : φ.comp ρ = MonoidHom.id _ := by
    refine PresentedGroup.ext fun e => ?_
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hρ_of]
    show φ (f₁ e) = PresentedGroup.of e
    simp only [f₁]
    by_cases h : e ∈ T
    · rw [dif_pos h]
      show φ 1 = PresentedGroup.of e
      rw [map_one]
      exact (PresentedGroup.one_of_mem (hR_of ⟨e, h⟩)).symm
    · rw [dif_neg h, hφ_of]
  exact ⟨MonoidHom.toMulEquiv ρ φ hφρ hρφ⟩

end Work.OROneRel
