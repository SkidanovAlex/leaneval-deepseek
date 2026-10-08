import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

open scoped TensorProduct

/-- The trace of the endomorphism `X ↦ A ∘ X ∘ B` of `End(V)` is the product of the traces
of `A` and `B`.

The proof identifies `End(V)` with the tensor product `V* ⊗ V` through the contraction
isomorphism `dualTensorHomEquiv`.  Under this identification the operator
`mulLeft A ∘ mulRight B` corresponds to `TensorProduct.map (Dual.transpose B) A`, whose
trace is `trace (Dual.transpose B) * trace A = trace B * trace A`. -/
theorem trace_mulLeft_comp_mulRight {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (A B : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (V →ₗ[ℂ] V) (LinearMap.mulLeft ℂ A ∘ₗ LinearMap.mulRight ℂ B)
      = LinearMap.trace ℂ V A * LinearMap.trace ℂ V B := by
  classical
  set e := dualTensorHomEquiv ℂ V V with he
  set f := TensorProduct.map (Module.Dual.transpose B) A with hf
  -- The operator `X ↦ A ∘ X ∘ B` is the conjugate of `map (transpose B) A` under `e`.
  have key : ∀ y : Module.Dual ℂ V ⊗[ℂ] V,
      e (f y) = (LinearMap.mulLeft ℂ A ∘ₗ LinearMap.mulRight ℂ B) (e y) := by
    intro y
    refine TensorProduct.inductionOn y ?_ ?_
    · intro φ v
      rw [hf, he]
      simp only [TensorProduct.map_tmul]
      ext x
      simp [LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Module.Dual.transpose_apply, LinearMap.comp_apply]
    · intro x y hx hy
      simp [map_add, hx, hy]
  have hconj : e.conj f = LinearMap.mulLeft ℂ A ∘ₗ LinearMap.mulRight ℂ B := by
    apply LinearMap.ext
    intro X
    obtain ⟨y, rfl⟩ := e.surjective X
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact key y
  calc LinearMap.trace ℂ (V →ₗ[ℂ] V) (LinearMap.mulLeft ℂ A ∘ₗ LinearMap.mulRight ℂ B)
      = LinearMap.trace ℂ (V →ₗ[ℂ] V) (e.conj f) := by rw [hconj]
    _ = LinearMap.trace ℂ (Module.Dual ℂ V ⊗[ℂ] V) f := LinearMap.trace_conj' f e
    _ = LinearMap.trace ℂ (Module.Dual ℂ V ⊗[ℂ] V)
          (TensorProduct.map (Module.Dual.transpose B) A) := by rw [hf]
    _ = LinearMap.trace ℂ (Module.Dual ℂ V) (Module.Dual.transpose B) * LinearMap.trace ℂ V A :=
          LinearMap.trace_tensorProduct' (Module.Dual.transpose B) A
    _ = LinearMap.trace ℂ V B * LinearMap.trace ℂ V A := by rw [LinearMap.trace_transpose']
    _ = LinearMap.trace ℂ V A * LinearMap.trace ℂ V B := by ring

end Work.Clifford
