import Mathlib
import Submission.Work.PSTAB.Deps

namespace Work.PSTAB

open scoped IsMulCommutative in
theorem QuadraticLinear {E : Type*} [Group E] [IsMulCommutative E] (p : ℕ)
    [Module (ZMod p) (Additive E)] (σ : MulAut E)
    (hσ : ∀ x : E, σ (σ x * x⁻¹) = σ x * x⁻¹) :
    ((OddOrder.BG.Ch1_Preliminary.mulAutToEnd E p σ : Module.End (ZMod p) (Additive E)) - 1) ^ 2
      = 0 := by
  -- Write `M` for the `F_p`-endomorphism induced by `σ`.
  set M : Module.End (ZMod p) (Additive E) :=
    OddOrder.BG.Ch1_Preliminary.mulAutToEnd E p σ with hM
  -- `M` acts on `Additive E` by applying `σ` to the underlying group element.
  have happ : ∀ y : Additive E, M y = Additive.ofMul (σ (Additive.toMul y)) := fun _ => rfl
  -- `M - 1` sends `y` to `toMul y ↦ σ (toMul y) / toMul y`, which is fixed by `σ` by `hσ`;
  -- hence `M ((M - 1) y) = (M - 1) y`, i.e. `(M - 1)² = 0`.
  have hfix : ∀ y : Additive E, M ((M - 1) y) = (M - 1) y := by
    intro y
    apply Additive.toMul.injective
    rw [happ, toMul_ofMul]
    have h1 : Additive.toMul ((M - 1) y) = σ (Additive.toMul y) * (Additive.toMul y)⁻¹ := by
      rw [LinearMap.sub_apply, Module.End.one_apply, happ, toMul_sub, toMul_ofMul,
        div_eq_mul_inv]
    rw [h1]
    exact hσ (Additive.toMul y)
  ext x
  rw [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hfix,
    sub_self]
  rfl

end Work.PSTAB
