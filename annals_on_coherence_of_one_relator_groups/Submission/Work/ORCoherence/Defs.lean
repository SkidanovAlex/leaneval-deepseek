import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

set_option autoImplicit false

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

variable {R S : Type*}

section Balanced

variable [Ring R] [Ring S] (f : R →+* S)

/-- The `R`-balanced relations inside `S ⊗[ℤ] M`; they generate the kernel of the
canonical map `S ⊗[ℤ] M ⟶ S ⊗[R] M`. -/
def balancedRel (M : Type*) [AddCommGroup M] [Module R M] : Submodule S (S ⊗[ℤ] M) :=
  Submodule.span S
    {x | ∃ (r : R) (s : S) (m : M), x = (s * f r) ⊗ₜ[ℤ] m - s ⊗ₜ[ℤ] (r • m)}

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The balanced tensor product `S ⊗[R] M`, for `M` a left `R`-module and `S` a ring
equipped with a ring homomorphism `f` from `R` (so that `S` is an `R`-bimodule). -/
abbrev Balanced : Type _ := (S ⊗[ℤ] M) ⧸ balancedRel f M

variable {M}

/-- The class of the pure tensor `s ⊗ m` in `S ⊗[R] M`. -/
def Balanced.tmul (s : S) (m : M) : Balanced f M :=
  Submodule.Quotient.mk (p := balancedRel f M) (s ⊗ₜ[ℤ] m)

@[simp]
theorem Balanced.tmul_zero (s : S) : Balanced.tmul f s (0 : M) = 0 := by
  rw [Balanced.tmul, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]

@[simp]
theorem Balanced.zero_tmul (m : M) : Balanced.tmul f (0 : S) m = 0 := by
  rw [Balanced.tmul, TensorProduct.zero_tmul, Submodule.Quotient.mk_zero]

theorem Balanced.tmul_add (s : S) (m₁ m₂ : M) :
    Balanced.tmul f s (m₁ + m₂) = Balanced.tmul f s m₁ + Balanced.tmul f s m₂ := by
  rw [Balanced.tmul, Balanced.tmul, Balanced.tmul, TensorProduct.tmul_add,
    Submodule.Quotient.mk_add]

theorem Balanced.add_tmul (s₁ s₂ : S) (m : M) :
    Balanced.tmul f (s₁ + s₂) m = Balanced.tmul f s₁ m + Balanced.tmul f s₂ m := by
  rw [Balanced.tmul, Balanced.tmul, Balanced.tmul, TensorProduct.add_tmul,
    Submodule.Quotient.mk_add]

/-- The defining relation of the balanced tensor product. -/
theorem Balanced.tmul_smul (s : S) (r : R) (m : M) :
    Balanced.tmul f (s * f r) m = Balanced.tmul f s (r • m) := by
  rw [Balanced.tmul, Balanced.tmul, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨r, s, m, rfl⟩

/-- The `S`-module structure on the balanced tensor product. -/
theorem Balanced.smul_tmul (t s : S) (m : M) :
    t • Balanced.tmul f s m = Balanced.tmul f (t * s) m := by
  rw [Balanced.tmul, ← Submodule.Quotient.mk_smul (balancedRel f M) t (s ⊗ₜ[ℤ] m), Balanced.tmul,
    TensorProduct.smul_tmul', smul_eq_mul]

variable {N : Type*} [AddCommGroup N] [Module S N]

/-- Auxiliary construction for the universal property of the balanced tensor product. -/
noncomputable def balancedLiftAux (φ : M →ₗ[ℤ] N) : S ⊗[ℤ] M →ₗ[ℤ] N :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun s m => s • φ m)
    (fun s₁ s₂ m => add_smul s₁ s₂ (φ m))
    (fun c s m => smul_assoc c s (φ m))
    (fun s m₁ m₂ => by rw [map_add, smul_add])
    (fun c s m => by rw [map_smul]; exact (smul_comm c s (φ m)).symm))

theorem balancedLiftAux_tmul (φ : M →ₗ[ℤ] N) (s : S) (m : M) :
    balancedLiftAux φ (s ⊗ₜ[ℤ] m) = s • φ m := by
  erw [balancedLiftAux, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

theorem balancedLiftAux_smul (φ : M →ₗ[ℤ] N) (t : S) (x : S ⊗[ℤ] M) :
    balancedLiftAux φ (t • x) = t • balancedLiftAux φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, balancedLiftAux_tmul, balancedLiftAux_tmul,
        mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The universal property of the balanced tensor product: an `S`-linear map out of
`S ⊗[R] M` is given by a `ℤ`-linear map `φ : M ⟶ N` compatible with the `R`-action. -/
noncomputable def Balanced.lift (φ : M →ₗ[ℤ] N)
    (hφ : ∀ (r : R) (m : M), f r • φ m = φ (r • m)) : Balanced f M →ₗ[S] N :=
  Submodule.liftQ (balancedRel f M)
    ({ toFun := balancedLiftAux φ
       map_add' := (balancedLiftAux φ).map_add
       map_smul' := balancedLiftAux_smul φ } : (S ⊗[ℤ] M) →ₗ[S] N)
    (by
      rw [balancedRel, Submodule.span_le]
      rintro x ⟨r, s, m, rfl⟩
      show balancedLiftAux φ ((s * f r) ⊗ₜ[ℤ] m - s ⊗ₜ[ℤ] (r • m)) = 0
      rw [map_sub, balancedLiftAux_tmul, balancedLiftAux_tmul, ← hφ r m, ← mul_smul, sub_self])

@[simp]
theorem Balanced.lift_tmul (φ : M →ₗ[ℤ] N)
    (hφ : ∀ (r : R) (m : M), f r • φ m = φ (r • m)) (s : S) (m : M) :
    Balanced.lift f φ hφ (Balanced.tmul f s m) = s • φ m := by
  rw [Balanced.tmul, Balanced.lift, Submodule.liftQ_apply]
  exact balancedLiftAux_tmul φ s m

@[simp]
theorem Balanced.lift_tmul_one (φ : M →ₗ[ℤ] N)
    (hφ : ∀ (r : R) (m : M), f r • φ m = φ (r • m)) (m : M) :
    Balanced.lift f φ hφ (Balanced.tmul f 1 m) = φ m := by
  rw [Balanced.lift_tmul, one_smul]

end Balanced

end Work.ORCoherence
