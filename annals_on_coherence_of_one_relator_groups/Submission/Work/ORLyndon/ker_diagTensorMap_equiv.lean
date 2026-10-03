import Mathlib
import Submission.Work.ORLyndon.DiagTensor

namespace Work.ORLyndon

universe u v

open scoped TensorProduct

/-- Tensoring an exact sequence `0 → ker f → N → N'` with the flat module `M` on the right
keeps it exact at the middle term: the kernel of `f ⊗ 1` is the image of `(ker f) ⊗ 1`.
This is `- ⊗ M` preserving the kernel of `f`, using flatness of `M`. -/
private theorem ker_rTensor_eq_range {K : Type*} [Field K] {N : Type*} {N' : Type*} {M : Type*}
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup M]
    [Module K N] [Module K N'] [Module K M] [Module.Flat K M] (g : N →ₗ[K] N') :
    LinearMap.ker (LinearMap.rTensor M g) =
      LinearMap.range (LinearMap.rTensor M (LinearMap.ker g).subtype) :=
  LinearMap.exact_iff.mp
    (Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g))

theorem ker_diagTensorMap_equiv {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)} [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] {N : Type (max u v)} [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N] [IsScalarTower K (MonoidAlgebra K G) N] {N' : Type (max u v)} [AddCommGroup N'] [Module K N'] [Module (MonoidAlgebra K G) N'] [IsScalarTower K (MonoidAlgebra K G) N'] (f : N →ₗ[MonoidAlgebra K G] N') : Nonempty (LinearMap.ker (Work.ORLyndon.diagTensorMap (M := M) f) ≃ₗ[MonoidAlgebra K G] (TensorProduct K (LinearMap.ker f) M)) := by
  -- `K` is a field, so every `K`-module is flat.
  haveI : Module.Flat K M := inferInstance
  -- The canonical `K[G]`-linear map `ker f ⊗[K] M → N ⊗[K] M`, `x ⊗ m ↦ x ⊗ m`.
  -- Its underlying `K`-linear map is `rTensor M ((ker f).subtype.restrictScalars K)`
  -- and it agrees with `diagTensorMap (ker f).subtype`.
  let ψ : (LinearMap.ker f) ⊗[K] M →ₗ[MonoidAlgebra K G] N ⊗[K] M :=
    diagTensorMap (M := M) (LinearMap.ker f).subtype
  -- `ψ` is injective, since `(ker f).subtype` is injective and `M` is flat over the field `K`.
  have hψinj : Function.Injective ψ := by
    have hinj : Function.Injective
        (LinearMap.rTensor M ((LinearMap.ker f).subtype.restrictScalars K)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
    intro x y hxy
    exact hinj hxy
  -- Exactness of `0 → ker f → N → N'` after tensoring with `M` over `K`: the kernel of
  -- `f ⊗ 1` is the image of `(ker f) ⊗ 1`.  Both maps are the `K`-linear maps underlying the
  -- `K[G]`-linear maps in play, so the same holds for `range ψ` and `ker (diagTensorMap f)`.
  have hA : LinearMap.ker (LinearMap.rTensor M (kLinear f)) =
      LinearMap.range (LinearMap.rTensor M (LinearMap.ker (kLinear f)).subtype) :=
    ker_rTensor_eq_range (kLinear f)
  have hset_eq : (LinearMap.range ψ : Set (N ⊗[K] M)) =
      (LinearMap.ker (diagTensorMap (M := M) f) : Set (N ⊗[K] M)) := by
    have h1 : (LinearMap.range ψ : Set (N ⊗[K] M)) =
        (LinearMap.range (LinearMap.rTensor M (LinearMap.ker (kLinear f)).subtype) :
          Set (N ⊗[K] M)) := rfl
    rw [h1]
    have h2 : (LinearMap.range (LinearMap.rTensor M (LinearMap.ker (kLinear f)).subtype) :
          Set (N ⊗[K] M)) =
        (LinearMap.ker (LinearMap.rTensor M (kLinear f)) : Set (N ⊗[K] M)) := by
      rw [← hA]
    rw [h2]
    rfl
  -- The canonical map `ker f ⊗[K] M → ker (diagTensorMap f)`, `x ⊗ m ↦ x ⊗ m`.
  let φ : (LinearMap.ker f) ⊗[K] M →ₗ[MonoidAlgebra K G] LinearMap.ker (diagTensorMap (M := M) f) :=
    LinearMap.codRestrict _ ψ (fun x => by
      rw [LinearMap.mem_ker]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add p q hp hq => simp [map_add, hp, hq]
      | tmul a m =>
          have hfa : f (↑a : N) = 0 := a.2
          rw [show ψ (a ⊗ₜ[K] m) = (↑a : N) ⊗ₜ[K] m from diagTensorMap_tmul _ a m,
            diagTensorMap_tmul, hfa]
          simp)
  -- `φ` is bijective: injective because `ψ` is, surjective because its range is all of
  -- `ker (diagTensorMap f)`.
  refine ⟨(LinearEquiv.ofBijective φ ?_).symm⟩
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hψinj
    exact congrArg Subtype.val hxy
  · intro y
    have hy : (y : N ⊗[K] M) ∈ (LinearMap.range ψ : Set (N ⊗[K] M)) := by
      rw [hset_eq]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

end Work.ORLyndon
