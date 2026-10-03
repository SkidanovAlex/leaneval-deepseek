import Submission.Work.ORCoherence.Defs

set_option autoImplicit false

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

variable {R S : Type*}

section Map

variable [Ring R] [Ring S] (f : R →+* S)
variable {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

theorem balancedMapAux_smul (g : M →ₗ[R] M') (t : S) (x : S ⊗[ℤ] M) :
    TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ) (t • x) =
      t • TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul, TensorProduct.map_tmul,
        LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', smul_eq_mul]
      rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Auxiliary construction for functoriality of the balanced tensor product. -/
noncomputable def balancedMapAux (g : M →ₗ[R] M') : (S ⊗[ℤ] M) →ₗ[S] S ⊗[ℤ] M' where
  toFun := TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ)
  map_add' := fun x y => map_add _ x y
  map_smul' := balancedMapAux_smul g

/-- Functoriality of the balanced tensor product in the second variable. -/
noncomputable def Balanced.map (g : M →ₗ[R] M') : Balanced f M →ₗ[S] Balanced f M' :=
  Submodule.mapQ (balancedRel f M) (balancedRel f M')
    (balancedMapAux g : (S ⊗[ℤ] M) →ₗ[S] S ⊗[ℤ] M')
    (by
      rw [balancedRel, balancedRel]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨r, s, m, rfl⟩
      have h1 : balancedMapAux (S := S) g ((s * f r) ⊗ₜ[ℤ] m) = (s * f r) ⊗ₜ[ℤ] g m := by
        change (TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ))
          ((s * f r) ⊗ₜ[ℤ] m) = _
        rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.coe_restrictScalars]
      have h2 : balancedMapAux (S := S) g (s ⊗ₜ[ℤ] (r • m)) = s ⊗ₜ[ℤ] (r • g m) := by
        change (TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ))
          (s ⊗ₜ[ℤ] (r • m)) = _
        rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.coe_restrictScalars,
          g.map_smul]
      show balancedMapAux (S := S) g ((s * f r) ⊗ₜ[ℤ] m - s ⊗ₜ[ℤ] (r • m)) ∈
        Submodule.span S {x | ∃ (r : R) (s : S) (m : M'), x = (s * f r) ⊗ₜ[ℤ] m - s ⊗ₜ[ℤ] (r • m)}
      rw [map_sub, h1, h2]
      exact Submodule.subset_span ⟨r, s, g m, rfl⟩)

@[simp]
theorem Balanced.map_tmul (g : M →ₗ[R] M') (s : S) (m : M) :
    Balanced.map f g (Balanced.tmul f s m) = Balanced.tmul f s (g m) := by
  rw [Balanced.tmul, Balanced.map, Balanced.tmul, Submodule.mapQ_apply]
  rfl

@[simp]
theorem Balanced.map_id : Balanced.map f (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    rw [Balanced.map, Submodule.mapQ_apply]
    show Submodule.Quotient.mk
      ((TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (LinearMap.id : M →ₗ[ℤ] M)) y) =
        Submodule.Quotient.mk y
    rw [TensorProduct.map_id]
    rfl

end Map

end Work.ORCoherence
