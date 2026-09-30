import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMM2

/-- **Injectivity of `f ⊗ 1` for a short exact sequence with flat cokernel.**  If
`0 → A --f--> B --g--> C → 0` is exact with `C` flat (and `A`, `B` flat), then `f ⊗ 1_N` is
injective for every `N`.  This specialises the Mathlib lemma
`LinearMap.lTensor_injective_of_exact_of_flat` through the identification of the left and right
tensor products (`LinearMap.lTensor_inj_iff_rTensor_inj`). -/
theorem rTensorSubtypeInjective {A B C N : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B]
    [Module ℤ B] [AddCommGroup C] [Module ℤ C] [AddCommGroup N] [Module ℤ N]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) (hf : Function.Injective f) (hex : Function.Exact f g)
    (hg : Function.Surjective g)
    (hA : Module.Flat ℤ A) (hB : Module.Flat ℤ B) (hC : Module.Flat ℤ C) :
    Function.Injective (f.rTensor N) := by
  haveI : Module.Flat ℤ A := hA
  haveI : Module.Flat ℤ B := hB
  haveI : Module.Flat ℤ C := hC
  exact (LinearMap.lTensor_inj_iff_rTensor_inj N f).mp
    (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hex N)

end Work.Pi6.EMM2
