import Mathlib.LinearAlgebra.Isomorphisms
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H1Dual

/-- If `f.range = g.ker` and `g` is surjective, then `C` is linearly isomorphic to the cokernel
`B ⧸ f.range`. -/
theorem cokerExtract {k : Type*} [Ring k] {A B C : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : f.range = g.ker) (hsurj : g.range = ⊤) :
    Nonempty (C ≃ₗ[k] (B ⧸ f.range)) :=
  ⟨(Submodule.topEquiv (R := k) (M := C)).symm.trans
    (((LinearEquiv.ofEq (R := k) g.range ⊤ hsurj).symm).trans
      (((LinearMap.quotKerEquivRange g).symm).trans
        ((Submodule.quotEquivOfEq (R := k) f.range g.ker hf).symm)))⟩

end Work.SSGRoute.H1Dual
