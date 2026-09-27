import Mathlib
import Submission.Work.KT.Defs

/-!
# Patching along a fibre product (`Work.KT.FPatch`)

Framework for the clutching construction used by `Work.KT.sphere_GL`.

`FiberProd ρ₁ ρ₂` is the fibre product of two rings `A₁`, `A₂` over a common quotient `A₀`:
the ring of pairs `(x₁,x₂)` with `ρ₁ x₁ = ρ₂ x₂` (the algebraic model of
`C(S¹) = C(I) ×_{C(S⁰)} C(I)`, two disks glued along their boundary).

For `γ : Matrix (Fin n) (Fin n) A₀` the *patched module* `patched γ` is
`{(f,g) ∈ A₁^n × A₂^n : ρ₁ f = γ * ρ₂ g}`: sections of the bundle over the glued space
obtained by clutching two trivial bundles along `γ`.
-/

namespace Work.KT

noncomputable section

open Matrix

variable {A₁ A₂ A₀ : Type}

/-- The fibre product of `A₁` and `A₂` over `A₀`. -/
def FiberProd [Ring A₁] [Ring A₂] [Ring A₀] (ρ₁ : A₁ →+* A₀) (ρ₂ : A₂ →+* A₀) :
    Subring (A₁ × A₂) where
  carrier := {z | ρ₁ z.1 = ρ₂ z.2}
  mul_mem' := by
    intro a b ha hb
    show ρ₁ (a.1 * b.1) = ρ₂ (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  add_mem' := by
    intro a b ha hb
    show ρ₁ (a.1 + b.1) = ρ₂ (a.2 + b.2)
    rw [map_add, map_add, ha, hb]
  zero_mem' := by
    show ρ₁ (0 : A₁) = ρ₂ (0 : A₂)
    rw [map_zero, map_zero]
  one_mem' := by
    show ρ₁ (1 : A₁) = ρ₂ (1 : A₂)
    rw [map_one, map_one]
  neg_mem' := by
    intro a ha
    show ρ₁ (-a.1) = ρ₂ (-a.2)
    rw [map_neg, map_neg, ha]

namespace FiberProd

section Basic

variable [Ring A₁] [Ring A₂] [Ring A₀] {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀}

/-- The projection of the fibre product onto the first factor. -/
def fstHom : FiberProd ρ₁ ρ₂ →+* A₁ :=
  (RingHom.fst A₁ A₂).comp (FiberProd ρ₁ ρ₂).subtype

/-- The projection of the fibre product onto the second factor. -/
def sndHom : FiberProd ρ₁ ρ₂ →+* A₂ :=
  (RingHom.snd A₁ A₂).comp (FiberProd ρ₁ ρ₂).subtype

@[simp] theorem fstHom_apply (z : FiberProd ρ₁ ρ₂) : fstHom z = z.1.1 := rfl
@[simp] theorem sndHom_apply (z : FiberProd ρ₁ ρ₂) : sndHom z = z.1.2 := rfl

instance instModule₁ : Module (FiberProd ρ₁ ρ₂) A₁ := Module.compHom A₁ fstHom
instance instModule₂ : Module (FiberProd ρ₁ ρ₂) A₂ := Module.compHom A₂ sndHom

/-- The defining relation of the fibre product. -/
theorem rho_fst (z : FiberProd ρ₁ ρ₂) : ρ₁ z.1.1 = ρ₂ z.1.2 := z.2

end Basic

section Patch

variable [Ring A₁] [Ring A₂] [Ring A₀] {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀}

/-- The *patched module*: pairs `(f,g)` with `ρ₁ f = γ * ρ₂ g`. -/
def patched (hcomm : ∀ x y : A₀, x * y = y * x) (n : ℕ) (γ : Matrix (Fin n) (Fin n) A₀) :
    Submodule (FiberProd ρ₁ ρ₂) ((Fin n → A₁) × (Fin n → A₂)) where
  carrier := {z | (fun i => ρ₁ (z.1 i)) = γ.mulVec (fun i => ρ₂ (z.2 i))}
  zero_mem' := by
    show (fun i => ρ₁ ((0 : (Fin n → A₁) × (Fin n → A₂)).1 i)) = _
    funext i
    simp [Matrix.mulVec, dotProduct]
  add_mem' := by
    intro x y hx hy
    have hx' : (fun i => ρ₁ (x.1 i)) = γ.mulVec (fun i => ρ₂ (x.2 i)) := hx
    have hy' : (fun i => ρ₁ (y.1 i)) = γ.mulVec (fun i => ρ₂ (y.2 i)) := hy
    show (fun i => ρ₁ ((x + y).1 i)) = γ.mulVec (fun i => ρ₂ ((x + y).2 i))
    have hv : (fun i => ρ₂ ((x + y).2 i)) = (fun i => ρ₂ (x.2 i)) + (fun i => ρ₂ (y.2 i)) := by
      funext i
      simp [map_add]
    rw [hv, Matrix.mulVec_add]
    funext i
    show ρ₁ ((x + y).1 i) = (γ.mulVec (fun i => ρ₂ (x.2 i))) i + (γ.mulVec (fun i => ρ₂ (y.2 i))) i
    show ρ₁ (x.1 i + y.1 i) = (γ.mulVec (fun i => ρ₂ (x.2 i))) i + (γ.mulVec (fun i => ρ₂ (y.2 i))) i
    rw [map_add, ← congrFun hx' i, ← congrFun hy' i]
  smul_mem' := by
    intro a x hx
    have h1 : (fun i => ρ₁ ((a • x.1) i)) = (fun i => ρ₂ a.1.2 * ρ₁ (x.1 i)) := by
      funext i
      show ρ₁ (fstHom a * x.1 i) = _
      rw [map_mul, fstHom_apply, a.2]
    have h2 : (fun i => ρ₂ ((a • x.2) i)) = (fun i => ρ₂ a.1.2 * ρ₂ (x.2 i)) := by
      funext i
      show ρ₂ (sndHom a * x.2 i) = _
      rw [map_mul, sndHom_apply]
    have hx' : (fun i => ρ₁ (x.1 i)) = γ.mulVec (fun i => ρ₂ (x.2 i)) := hx
    show (fun i => ρ₁ ((a • x.1) i)) = γ.mulVec (fun i => ρ₂ ((a • x.2) i))
    rw [h1, h2]
    funext i
    rw [congrFun hx' i]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← mul_assoc, hcomm (ρ₂ a.1.2) (γ i j)]

/-- The identity gluing has the free module as patched module. -/
def patchedOneIso (hcomm : ∀ x y : A₀, x * y = y * x) (n : ℕ) :
    patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n 1 ≃ₗ[FiberProd ρ₁ ρ₂]
      (Fin n → FiberProd ρ₁ ρ₂) where
  toFun z := fun i => ⟨(z.1.1 i, z.1.2 i), by
    have h : (fun i => ρ₁ (z.1.1 i)) =
        (1 : Matrix (Fin n) (Fin n) A₀).mulVec (fun i => ρ₂ (z.1.2 i)) := z.2
    have hh := congrFun h i
    rw [Matrix.one_mulVec] at hh
    exact hh⟩
  invFun f := ⟨(fun i => (f i).1.1, fun i => (f i).1.2), by
    show (fun i => ρ₁ ((f i).1.1)) =
      (1 : Matrix (Fin n) (Fin n) A₀).mulVec (fun i => ρ₂ ((f i).1.2))
    rw [Matrix.one_mulVec]
    funext i
    exact (f i).2⟩
  left_inv := by
    intro z
    ext i <;> rfl
  right_inv := by
    intro f
    ext i <;> rfl
  map_add' := by
    intro x y
    ext i <;> rfl
  map_smul' := by
    intro a x
    ext i <;> rfl

end Patch

end FiberProd

end

end Work.KT
