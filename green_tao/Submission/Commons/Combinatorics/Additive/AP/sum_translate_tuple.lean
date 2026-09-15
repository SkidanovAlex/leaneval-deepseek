import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.IsFormallyReal

namespace Commons.Combinatorics.Additive.AP

open Finset
open scoped BigOperators

/-- Change of variables `h_j ↦ h + h_j` in a sum over tuples, averaged over the common
shift `h` (translation invariance of the counting measure). -/
theorem sum_translate_tuple {G : Type*} [AddCommGroup G] [Fintype G] {d K : ℕ}
    (Ψ : (Fin K → Fin d → G) → ℝ) :
    ∑ H : Fin K → Fin d → G, Ψ H
      = ((Fintype.card G : ℝ) ^ d)⁻¹ *
        ∑ (h : Fin d → G) (H : Fin K → Fin d → G), Ψ (fun j => h + H j) := by
  -- For fixed `h`, the translation `H ↦ (fun j => h + H j)` is a bijection of
  -- `Fin K → Fin d → G`, so it leaves the sum over `H` invariant.
  have inner : ∀ h : Fin d → G,
      (∑ H : Fin K → Fin d → G, Ψ (fun j => h + H j)) = ∑ H, Ψ H := by
    intro h
    let τ : (Fin K → Fin d → G) ≃ (Fin K → Fin d → G) :=
      { toFun := fun H => fun j => h + H j
        invFun := fun H => fun j => H j - h
        left_inv := by intro H; funext j; exact add_sub_cancel_left _ _
        right_inv := by intro H; funext j; exact add_sub_cancel _ _ }
    exact Fintype.sum_equiv τ (fun H => Ψ (fun j => h + H j)) Ψ (fun H => rfl)
  -- Summing the invariant value over all `h` multiplies by `card (Fin d → G) = (card G)^d`.
  have hstep : (∑ (h : Fin d → G) (H : Fin K → Fin d → G), Ψ (fun j => h + H j))
      = (Fintype.card G : ℝ) ^ d * ∑ H : Fin K → Fin d → G, Ψ H := by
    rw [Finset.sum_product]
    rw [Finset.sum_congr rfl (fun h _ => inner h)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
  rw [hstep]
  have hG : (Fintype.card G : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by
      have : (0:ℕ) < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
      exact_mod_cast ne_of_gt this)
  rw [← mul_assoc, inv_mul_cancel₀ hG, one_mul]

end Commons.Combinatorics.Additive.AP