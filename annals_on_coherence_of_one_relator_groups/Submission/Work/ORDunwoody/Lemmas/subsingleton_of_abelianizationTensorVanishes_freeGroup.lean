import Mathlib
import Submission.Work.ORDunwoody.FP2

set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Work.ORDunwoody.Lemmas

/-- A free group `FreeGroup α` whose `k`-abelianization `H₁(-;k) = (FreeGroup α)^ab ⊗_ℤ k`
vanishes must be trivial, for `k` a nontrivial commutative ring.

Indeed `(FreeGroup α)^ab` is the free abelian group on `α`, so
`(FreeGroup α)^ab ⊗_ℤ k ≅ ⊕_{a : α} k`.  For `k` nontrivial this vanishes only when `α` is
empty, and `FreeGroup α` is trivial exactly when `α` is empty. -/
theorem subsingleton_of_abelianizationTensorVanishes_freeGroup {k : Type*} [CommRing k]
    [Nontrivial k] (α : Type*) (h : AbelianizationTensorVanishes k (FreeGroup α)) :
    Subsingleton (FreeGroup α) := by
  -- It suffices to show `α` is empty: then `FreeGroup α` is a subsingleton (indeed a `Unique`).
  have key : IsEmpty α := by
    rw [← not_nonempty_iff]
    rintro ⟨x⟩
    classical
    -- The coordinate functional at `x`, on the free abelian group on `α`.
    let g : FreeAbelianGroup α →ₗ[ℤ] ℤ :=
      (FreeAbelianGroup.lift (fun y => if y = x then (1 : ℤ) else 0)).toIntLinearMap
    have hgx : g (FreeAbelianGroup.of x) = 1 := by
      simp [g, FreeAbelianGroup.lift_apply_of]
    -- `AbelianizationTensorVanishes` is exactly the subsingleton statement for the tensor
    -- product with `FreeAbelianGroup α = Additive (Abelianization (FreeGroup α))`.
    have hh : Subsingleton (TensorProduct ℤ (FreeAbelianGroup α) k) := h
    -- Tensoring `g` with `k` and cancelling `ℤ ⊗_ℤ k ≅ k` gives a functional on the tensor
    -- product that takes a specified element to `1`.
    have hval : (TensorProduct.lid ℤ k)
        (LinearMap.rTensor k g (FreeAbelianGroup.of x ⊗ₜ[ℤ] (1 : k))) = 1 := by
      rw [LinearMap.rTensor_tmul, hgx, TensorProduct.lid_tmul]
      simp
    have heq : (FreeAbelianGroup.of x ⊗ₜ[ℤ] (1 : k)) = 0 := hh.elim _ _
    have h10 : (1 : k) = 0 := by
      rw [← hval, heq]
      simp
    exact one_ne_zero h10
  haveI : IsEmpty α := key
  infer_instance

end Work.ORDunwoody.Lemmas
