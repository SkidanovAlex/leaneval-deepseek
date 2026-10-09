import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `f : Y → X` admits a section landing in the free generators, i.e. there is
`g : X → FreeGroup Y` with `g (f y) = FreeGroup.of y` for all `y`, then the induced
homomorphism `FreeGroup.map f : FreeGroup Y →* FreeGroup X` is a split monomorphism:
there is a retraction `ρ : FreeGroup X →* FreeGroup Y` with `ρ.comp (FreeGroup.map f) = id`.

Concretely `ρ = FreeGroup.lift g` and on generators
`ρ (FreeGroup.map f (FreeGroup.of y)) = g (f y) = FreeGroup.of y`,
so `ρ.comp (FreeGroup.map f)` agrees with the identity on generators, hence everywhere
by the universal property of the free group. -/
theorem exists_freeGroup_lift_retraction {X Y : Type*} (f : Y → X) (g : X → FreeGroup Y)
    (hg : ∀ y, g (f y) = FreeGroup.of y) :
    ∃ ρ : FreeGroup X →* FreeGroup Y, ρ.comp (FreeGroup.map f) = MonoidHom.id (FreeGroup Y) := by
  refine ⟨FreeGroup.lift g, ?_⟩
  rw [← FreeGroup.lift_of_eq_id Y]
  exact MonoidHom.ext fun x =>
    FreeGroup.lift_unique (f := FreeGroup.of) ((FreeGroup.lift g).comp (FreeGroup.map f))
      (fun y => by simp [hg]) (x := x)

end Work.SSGRoute
