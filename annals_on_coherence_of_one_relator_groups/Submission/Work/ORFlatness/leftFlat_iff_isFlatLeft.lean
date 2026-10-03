import Mathlib
import Submission.Work.ORHomAlg.Flat
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

/-- The two balanced relations coincide as `ℤ`-submodules of `X ⊗[ℤ] N`: the `ℤ`-span of the
set of balancing relations written with `Set.range` (this area) is the `ℤ`-span of the same set
written with an existential (`Work.ORHomAlg`). -/
theorem balRel_eq_balancedRel (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (N : Type u) [AddCommGroup N] [Module R N] :
    balRel R X N = Work.ORHomAlg.balancedRel R X N := by
  rw [balRel, Work.ORHomAlg.balancedRel]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨x, n, r⟩, h⟩
    exact ⟨x, r, n, h.symm⟩
  · rintro ⟨x, r, n, h⟩
    exact ⟨(x, n, r), h.symm⟩

/-- The balanced tensor products of the two areas are linearly isomorphic. -/
noncomputable def baltensorEquiv (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (N : Type u) [AddCommGroup N] [Module R N] :
    BalTensor R X N ≃ₗ[ℤ] Work.ORHomAlg.BalancedTensor R X N :=
  Submodule.quotEquivOfEq (balRel R X N) (Work.ORHomAlg.balancedRel R X N)
    (balRel_eq_balancedRel R X N)

/-- The isomorphism is the identity on the classes of the pure tensors. -/
theorem baltensorEquiv_mk (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (N : Type u) [AddCommGroup N] [Module R N] (x : X) (n : N) :
    baltensorEquiv R X N (BalTensor.mk R x n) = Work.ORHomAlg.BalancedTensor.tmul R x n := by
  show Submodule.quotEquivOfEq (balRel R X N) (Work.ORHomAlg.balancedRel R X N)
      (balRel_eq_balancedRel R X N)
      (Submodule.Quotient.mk (p := balRel R X N) (x ⊗ₜ[ℤ] n)) =
    Submodule.Quotient.mk (p := Work.ORHomAlg.balancedRel R X N) (x ⊗ₜ[ℤ] n)
  rw [Submodule.quotEquivOfEq_mk]

/-- The isomorphism is natural in the first variable. -/
theorem baltensorEquiv_map (R : Type u) [Ring R] {X X' : Type u} [AddCommGroup X]
    [Module Rᵐᵒᵖ X] [AddCommGroup X'] [Module Rᵐᵒᵖ X'] (N : Type u) [AddCommGroup N]
    [Module R N] (f : X →ₗ[Rᵐᵒᵖ] X') (z : BalTensor R X N) :
    baltensorEquiv R X' N (BalTensor.map R f (LinearMap.id : N →ₗ[R] N) z) =
      Work.ORHomAlg.BalancedTensor.map f (LinearMap.id : N →ₗ[R] N)
        (baltensorEquiv R X N z) := by
  let u : BalTensor R X N →+ Work.ORHomAlg.BalancedTensor R X' N :=
    (baltensorEquiv R X' N).toLinearMap.toAddMonoidHom.comp
      (BalTensor.map R f (LinearMap.id : N →ₗ[R] N))
  let v : BalTensor R X N →+ Work.ORHomAlg.BalancedTensor R X' N :=
    (Work.ORHomAlg.BalancedTensor.map f (LinearMap.id : N →ₗ[R] N)).comp
      ((baltensorEquiv R X N).toLinearMap.toAddMonoidHom)
  have huv : u = v := by
    apply BalTensor.ext R
    intro x n
    show baltensorEquiv R X' N
        (BalTensor.map R f (LinearMap.id : N →ₗ[R] N) (BalTensor.mk R x n)) =
      Work.ORHomAlg.BalancedTensor.map f (LinearMap.id : N →ₗ[R] N)
        (baltensorEquiv R X N (BalTensor.mk R x n))
    rw [BalTensor.map_mk, baltensorEquiv_mk, baltensorEquiv_mk,
      Work.ORHomAlg.BalancedTensor.map_tmul]
  exact congrFun (congrArg DFunLike.coe huv) z

/-- Injectivity of two maps related by a commutative square with equivalences on the sides. -/
private theorem injective_iff_of_bijective {A A' B B' : Type*}
    {e : A → A'} {e' : B → B'} (he : Function.Bijective e) (he' : Function.Bijective e')
    {u : A → B} {v : A' → B'} (h : ∀ a, e' (u a) = v (e a)) :
    Function.Injective u ↔ Function.Injective v := by
  constructor
  · intro hu a' b' hab
    obtain ⟨a, rfl⟩ := he.2 a'
    obtain ⟨b, rfl⟩ := he.2 b'
    have h1 : a = b := hu (he'.1 (by
      show e' (u a) = e' (u b)
      rw [h a, h b]
      exact hab))
    rw [h1]
  · intro hv a b hab
    have h2 : v (e a) = v (e b) := by
      rw [← h a, ← h b, hab]
    exact he.1 (hv h2)

/-- The balanced tensor product `Work.ORFlatness.BalTensor R X N` of this area and the balanced tensor product `Work.ORHomAlg.BalancedTensor R X N` (`Submission/Work/ORHomAlg/Basic.lean`, notation `X ⊠[R] N`) are the same construction: both are `(X ⊗[ℤ] N)` modulo the ℤ-span of the elements `(op r • x) ⊗ n - x ⊗ (r • n)`. Indeed `Work.ORFlatness.balRel R X N = Work.ORHomAlg.balancedRel R X N` (the two spanning sets are the same set, written with `Set.range` and with an existential), and the two quotients are both taken by `Submodule.toAddSubgroup`. Consequently the flatness notions agree:

`Work.ORFlatness.LeftFlat R M ↔ Work.ORHomAlg.IsFlatLeft R M`

for a left `R`-module `M`. This lets the results of this area be stated in the vocabulary of N1 (`Work.ORHomAlg`).

Suggested route: prove `balRel R X N = Work.ORHomAlg.balancedRel R X N` by `le_antisymm`/`Submodule.span_le` in both directions (or `ext`), so that `BalTensor R X N` and `X ⊠[R] N` are equal types; then check that the induced maps agree on generators: both `Work.ORFlatness.BalTensor.map R g (LinearMap.id : M →ₗ[R] M)` and `Work.ORHomAlg.BalancedTensor.rTensor (N := M) g` send the class of `x ⊗[ℤ] m` to the class of `g x ⊗[ℤ] m` (each area has its own `lift`/universal property and its own `map_tmul`/`tmul` lemmas for this; `Work.ORFlatness.BalTensor.map_mk` and `Work.ORHomAlg.BalancedTensor.tmul`/`rTensor` are the relevant ones). -/
theorem leftFlat_iff_isFlatLeft (R : Type u) [Ring R] {M : Type u} [AddCommGroup M]
    [Module R M] :
    Work.ORFlatness.LeftFlat R M ↔ Work.ORHomAlg.IsFlatLeft R M := by
  constructor
  · intro h X Y iX mX iY mY f hf
    show Function.Injective (Work.ORHomAlg.BalancedTensor.map f (LinearMap.id : M →ₗ[R] M))
    exact (injective_iff_of_bijective (baltensorEquiv R X M).bijective
      (baltensorEquiv R Y M).bijective
      (fun z => baltensorEquiv_map R M f z)).mp (h f hf)
  · intro h X Y iX mX iY mY f hf
    show Function.Injective (BalTensor.map R f (LinearMap.id : M →ₗ[R] M))
    exact (injective_iff_of_bijective (baltensorEquiv R X M).bijective
      (baltensorEquiv R Y M).bijective
      (fun z => baltensorEquiv_map R M f z)).mpr (h f hf)

end Work.ORFlatness
