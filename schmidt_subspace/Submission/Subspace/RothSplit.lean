import Mathlib
import Submission.Subspace.RothWronskian
import Submission.Commons.Algebra.MvPolynomial.exists_scaling_integral_fin
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_int_tensor_eq_fin

/-!
# Splitting an integral product into integral factors

If an integer polynomial `V ∈ ℤ[x_0,…,x_n]` factors, over `ℚ`, as a product of a polynomial in
`x_0` alone and a polynomial in `x_1,…,x_n` alone, then the two factors can be taken *integral*,
and the affine height splits exactly: `hZ V = hZ W₁ + hZ W₂`.

This is the step that makes the height of the two Wronskians in Roth's lemma controllable by the
height of their product.
-/

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial
open Commons.NumberTheory.Height.MvPolynomial (gP)

/-- **Integral splitting of a tensor factorisation.** -/
theorem exists_integral_split {n : ℕ} (V : MvPolynomial (Fin (n + 1)) ℤ)
    (U₁ : MvPolynomial (Fin 1) ℚ) (U₂ : MvPolynomial (Fin n) ℚ) (h₁ : U₁ ≠ 0) (h₂ : U₂ ≠ 0)
    (hV : V.map (Int.castRingHom ℚ) =
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) U₁ *
        MvPolynomial.rename Fin.succ U₂) :
    ∃ (c : ℚ) (W₁ : MvPolynomial (Fin 1) ℤ) (W₂ : MvPolynomial (Fin n) ℤ),
      c ≠ 0 ∧ W₁ ≠ 0 ∧ W₂ ≠ 0 ∧
      U₁ = MvPolynomial.C c * W₁.map (Int.castRingHom ℚ) ∧
      U₂ = MvPolynomial.C c⁻¹ * W₂.map (Int.castRingHom ℚ) ∧
      V = MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ *
        MvPolynomial.rename Fin.succ W₂ ∧
      hZ V = hZ W₁ + hZ W₂ := by
  obtain ⟨c, hc, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩ :=
    Commons.Algebra.MvPolynomial.exists_scaling_integral_fin U₁ U₂ h₁ h₂ V hV
  have hcne : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hW₁ne : W₁ ≠ 0 := by
    intro h
    rw [h, map_zero] at hW₁
    rcases mul_eq_zero.mp hW₁.symm with h' | h'
    · exact hcne (by simpa using h')
    · exact h₁ h'
  have hW₂ne : W₂ ≠ 0 := by
    intro h
    rw [h, map_zero] at hW₂
    rcases mul_eq_zero.mp hW₂.symm with h' | h'
    · exact hc (by simpa using h')
    · exact h₂ h'
  have hU₁ : U₁ = MvPolynomial.C c * (W₁.map (Int.castRingHom ℚ)) := by
    rw [hW₁, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  have hU₂ : U₂ = MvPolynomial.C c⁻¹ * (W₂.map (Int.castRingHom ℚ)) := by
    rw [hW₂, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  have hkey : V.map (Int.castRingHom ℚ) =
      (MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ *
        MvPolynomial.rename Fin.succ W₂).map (Int.castRingHom ℚ) := by
    rw [hV, hU₁, hU₂, map_mul, map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_C,
      MvPolynomial.map_rename, MvPolynomial.map_rename]
    have hcc : (MvPolynomial.C c * MvPolynomial.C c⁻¹ : MvPolynomial (Fin (n + 1)) ℚ) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    have key : ∀ A B : MvPolynomial (Fin (n + 1)) ℚ,
        MvPolynomial.C c * A * (MvPolynomial.C c⁻¹ * B) = A * B := by
      intro A B
      calc MvPolynomial.C c * A * (MvPolynomial.C c⁻¹ * B)
          = (MvPolynomial.C c * MvPolynomial.C c⁻¹) * (A * B) := by ring
        _ = A * B := by rw [hcc, one_mul]
    exact key _ _
  have hVeq : V = MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ *
      MvPolynomial.rename Fin.succ W₂ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective hkey
  refine ⟨c, W₁, W₂, hc, hW₁ne, hW₂ne, hU₁, hU₂, hVeq, ?_⟩
  rw [hVeq, hZ_eq, hZ_eq, hZ_eq]
  exact Commons.NumberTheory.Height.MvPolynomial.polyHeight_int_tensor_eq_fin W₁ W₂ hW₁ne hW₂ne

end Submission.Subspace
