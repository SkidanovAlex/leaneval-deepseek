import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H1Dual

/-- If `f.range = g.ker` and `f` is injective, then `A` is linearly isomorphic to `g.ker`. -/
theorem kerExtract {k : Type*} [Ring k] {A B C : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : f.range = g.ker) (hinj : f.ker = ⊥) :
    Nonempty (A ≃ₗ[k] g.ker) := by
  have h : Function.Injective f := LinearMap.ker_eq_bot.mp hinj
  exact ⟨(LinearEquiv.ofInjective f h).trans (LinearEquiv.ofEq _ _ hf)⟩

end Work.SSGRoute.H1Dual
