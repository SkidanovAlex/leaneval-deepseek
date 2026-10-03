import Mathlib
import Submission.Work.Section3.RkFinModel.Defs

set_option autoImplicit false

universe u

namespace Work.Section3.RkFinModel

/-- If `z ⊗ r = 0` in the `R`-balanced tensor product `S ⊗[R] L`, then for every additive map
`ψ : L →+ T` that is compatible with the `R`-action along `f` (`ψ (a • l) = f a • ψ l`),
we have `z • ψ r = 0`.

Indeed `S ⊗[ℤ] L → T`, `s ⊗ l ↦ s • ψ l` is `ℤ`-bilinear and kills the balance relations
(`(s·f a) • ψ l = s • (f a • ψ l) = s • ψ (a • l)`), so it descends to an additive map
`S ⊗[R] L →+ T`, and the conclusion is its value on the vanishing element `tmulM f z r`. -/
theorem smul_eq_zero_of_tmulM_eq_zero {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {L : Type u} [AddCommGroup L] [Module R L] {T : Type u} [AddCommGroup T] [Module S T]
    (ψ : L →+ T) (hψ : ∀ (a : R) (l : L), ψ (a • l) = f a • ψ l)
    {z : S} {r : L} (hz : Work.Section3.RkFinModel.BalancedTensorMod.tmulM f z r = 0) :
    z • ψ r = 0 := by
  -- The `ℤ`-bilinear pairing `β s l = s • ψ l`.
  let β : S →ₗ[ℤ] L →ₗ[ℤ] T := LinearMap.mk₂ ℤ (fun s l => s • ψ l)
    (fun m₁ m₂ n => by rw [add_smul])
    (fun c m n => by rw [smul_assoc])
    (fun m n₁ n₂ => by rw [map_add, smul_add])
    (fun c m n => by rw [map_zsmul, smul_comm])
  -- It is balanced: `β (s · f a) l = β s (a • l)`.
  have hβ : ∀ s : S, ∀ l : L, ∀ a : R, β (s * f a) l = β s (a • l) := by
    intro s l a
    show (s * f a) • ψ l = s • ψ (a • l)
    rw [mul_smul, ← hψ a l]
  -- Descend to `S ⊗[R] L` and evaluate at `tmulM f z r = 0`.
  have key : z • ψ r = β z r := rfl
  rw [key]
  have h := BalancedTensorMod.lift_tmulM f β hβ z r
  rw [hz, map_zero] at h
  rw [← h]

end Work.Section3.RkFinModel
