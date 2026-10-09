import Mathlib
import Submission.Work.SSGRoute.H1Dual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H1Dual

open CategoryTheory

/-- The concrete coinduced representation `coindRep k G V` is isomorphic to Mathlib's
coinduction from the trivial subgroup. -/
theorem coindRepIsoCoind (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module k V] :
    Nonempty (Work.SSGRoute.coindRep k G V ≅
      Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k ↥(⊥ : Subgroup G) V)) := by
  -- The coinduced module along the trivial subgroup is the whole function space `G → V`,
  -- and the two actions agree: both send `f` to `x ↦ f (x * g)`.
  let e : (G → V) ≃ₗ[k]
      ↥(Representation.coindV (⊥ : Subgroup G).subtype
        (Rep.trivial k ↥(⊥ : Subgroup G) V).ρ) :=
  { toFun := fun f => ⟨f, by
      intro g h
      simp only [Subgroup.coe_subtype]
      rw [Subgroup.mem_bot.1 g.2, one_mul]
      exact (Representation.trivial_apply (k := k) (G := ↥(⊥ : Subgroup G)) (V := V) g (f h)).symm⟩
    invFun := fun f => f.1
    left_inv := fun f => rfl
    right_inv := fun f => rfl
    map_add' := fun f g => Subtype.ext rfl
    map_smul' := fun c f => Subtype.ext rfl }
  refine ⟨Rep.mkIso (Representation.Equiv.mk e ?_)⟩
  intro g
  ext f h
  simp only [LinearMap.coe_comp, Function.comp_apply]
  dsimp only [e]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Representation.coind_apply]
  rw [Work.SSGRoute.coindRepRep_apply]
  show f (h * g) = (LinearMap.funLeft k V (fun x => x * g)) f h
  rw [LinearMap.funLeft_apply]

end Work.SSGRoute.H1Dual
