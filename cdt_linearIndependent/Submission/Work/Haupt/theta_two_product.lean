import Mathlib
import Submission.Work.Haupt.defs
import Submission.Work.Haupt.thetaCore
import Submission.Work.Haupt.ThetaProd_analytic
import Submission.Work.Haupt.ThetaSum_analytic
import Submission.Work.Haupt.ThetaProd_functional
import Submission.Work.Haupt.ThetaSum_functional
import Submission.Work.Haupt.ThetaSum_rigidity
import Submission.Work.Haupt.ThetaSum_pentagonal
import Submission.Work.Haupt.ThetaProd_pentagonal
import Submission.Work.Haupt.prod_even_split
import Submission.Work.Haupt.ThetaProd_self
import Submission.Work.Haupt.ThetaProd_self

/-!
# The `θ₂` product formula

`T2 x = ∑_{n ∈ ℤ} x^{n(n+1)} = 2 ∏_{m ≥ 1}(1 - x^{2m})(1 + x^{2m})² = T2prod x` for `‖x‖ < 1`.

The proof is the standard one for the Jacobi triple product at the point `z = x`:

* `ThetaProd x z = ∏_{n≥0}(1 + x^{2n+1}z)(1 + x^{2n+1}/z)` and
  `ThetaSum x z = ∑_{n∈ℤ}x^{n²}z^n` are both holomorphic on `ℂ \ {0}` and both satisfy the
  functional equation `F (x²z) = (xz)⁻¹ F z`; the rigidity lemma `ThetaSum_rigidity` then
  gives `ThetaProd x z = c · ThetaSum x z` for a constant `c`.
* `c` is determined at the *pentagonal point* `x = X³`, `z = -X`: there the theta product equals
  `∏(1-X^{6m+4})∏(1-X^{6m+2})` and the theta series equals Euler's pentagonal product
  `∏(1-X^{2m+2}) = ∏(1-X^{6m+6})∏(1-X^{6m+4})∏(1-X^{6m+2})`, so `c = (∏_{m≥0}(1-x^{2m+2}))⁻¹`.
* Evaluating at `z = x` gives `T2 x = T2prod x`.
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

theorem theta_two_product (x : ℂ) (hx : ‖x‖ < 1) : T2 x = T2prod x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [T2_zero, T2prod_zero]
  · -- the rigidity: the theta product is a constant multiple of the theta series
    obtain ⟨c, hc⟩ := ThetaSum_rigidity x hx hx0 (ThetaProd x) (ThetaProd_analytic x hx)
      (ThetaProd_functional x hx hx0)
    -- a cube root `X` of `x`, of norm `< 1`
    obtain ⟨X, hX3, hXn⟩ := exists_cube_root x hx
    have hX0 : X ≠ 0 := by
      rintro rfl
      simp only [zero_pow (by norm_num : (3:ℕ) ≠ 0)] at hX3
      exact hx0 hX3.symm
    -- abbreviation for the three products at the pentagonal point
    set A6 : ℂ := ∏' m : ℕ, (1 - X ^ (6 * m + 6)) with hA6
    set A4 : ℂ := ∏' m : ℕ, (1 - X ^ (6 * m + 4)) with hA4
    set A2 : ℂ := ∏' m : ℕ, (1 - X ^ (6 * m + 2)) with hA2
    -- the pentagonal evaluation of the functional equation
    have h_eval : A4 * A2 = c * (A6 * (A4 * A2)) := by
      have h1 : ThetaProd x (-X) = c * ThetaSum x (-X) := hc (-X) (neg_ne_zero.mpr hX0)
      rw [← hX3, ThetaProd_pentagonal X hXn, ThetaSum_pentagonal X hXn,
        prod_even_split X hXn, mul_assoc] at h1
      simpa only [← hA4, ← hA2, ← hA6, mul_assoc] using h1
    -- the products are nonzero
    have hA4A2 : A4 * A2 ≠ 0 := by
      have h : (∏' m : ℕ, (1 - X ^ (2 * m + 2))) ≠ 0 := prod_even_ne_zero X hXn
      rw [prod_even_split X hXn] at h
      rw [← hA4, ← hA2, ← hA6] at h
      have h64 : A6 * A4 ≠ 0 := (mul_ne_zero_iff.mp h).1
      exact mul_ne_zero (mul_ne_zero_iff.mp h64).2 (mul_ne_zero_iff.mp h).2
    -- hence `c * A6 = 1`
    have hcA6 : c * A6 = 1 := by
      have h2 : (c * A6) * (A4 * A2) = (1 : ℂ) * (A4 * A2) := by
        rw [one_mul]
        calc (c * A6) * (A4 * A2) = c * (A6 * (A4 * A2)) := by ring
          _ = A4 * A2 := h_eval.symm
      exact mul_right_cancel₀ hA4A2 h2
    -- identify `A6` with the product over `x`
    have hA6x : A6 = (∏' m : ℕ, (1 - x ^ (2 * m + 2))) := by
      rw [hA6, ← hX3]
      refine tprod_congr fun m => ?_
      rw [show (X ^ 3) ^ (2 * m + 2) = X ^ (6 * m + 6) by
        rw [← pow_mul, show 3 * (2 * m + 2) = 6 * m + 6 by ring]]
    have hcP : c * (∏' m : ℕ, (1 - x ^ (2 * m + 2))) = 1 := by rw [← hA6x]; exact hcA6
    have hcne : c ≠ 0 := by
      intro h
      rw [h, zero_mul] at hcP
      exact one_ne_zero hcP.symm
    have hinv : c⁻¹ = (∏' m : ℕ, (1 - x ^ (2 * m + 2))) := inv_eq_of_mul_eq_one_right hcP
    -- evaluate at `z = x`
    have hx_eval : ThetaProd x x = c * ThetaSum x x := hc x hx0
    have hS : ThetaSum x x = c⁻¹ * ThetaProd x x := by
      rw [hx_eval, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    have hself := ThetaProd_self x hx hx0
    have hsplit := T2prod_split x hx
    rw [T2_eq_ThetaSum_self x hx0, hS, hinv, hself]
    rw [hsplit]
    ring

end

end Work.Haupt
