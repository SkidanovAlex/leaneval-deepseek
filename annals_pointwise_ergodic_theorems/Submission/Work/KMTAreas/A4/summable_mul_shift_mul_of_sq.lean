import Mathlib

namespace Work.KMTAreas.A4

/-- Cauchy–Schwarz (in the elementary form `2ab ≤ a² + b²`) for two square-summable
sequences over `ℤ`, with bounded weights and arbitrary integer shifts.

The product `f (· + d) * g (· + e)` is summable because
`‖f (x+d)‖ * ‖g (x+e)‖ ≤ ‖f (x+d)‖ ^ 2 + ‖g (x+e)‖ ^ 2`, and the right hand side is
summable (translations of `ℤ` preserve summability); multiplying by a bound `C` for `φ`
preserves summability, and the pointwise norm bound upgrades this to summability of the
complex-valued product. -/
theorem summable_mul_shift_mul_of_sq {f g φ : ℤ → ℂ} (d e : ℤ)
    (hf : Summable (fun x : ℤ => ‖f x‖ ^ 2))
    (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2))
    (hφ : ∃ C : ℝ, ∀ x : ℤ, ‖φ x‖ ≤ C) :
    Summable (fun x : ℤ => f (x + d) * g (x + e) * φ x) := by
  obtain ⟨C, hC⟩ := hφ
  have hCb : ∀ x : ℤ, ‖φ x‖ ≤ max C 0 := fun x => le_trans (hC x) (le_max_left _ _)
  -- Translating the index preserves summability.
  have hfs : Summable (fun x : ℤ => ‖f (x + d)‖ ^ 2) :=
    (Equiv.summable_iff (f := fun y : ℤ => ‖f y‖ ^ 2) (Equiv.addRight d)).mpr hf
  have hgs : Summable (fun x : ℤ => ‖g (x + e)‖ ^ 2) :=
    (Equiv.summable_iff (f := fun y : ℤ => ‖g y‖ ^ 2) (Equiv.addRight e)).mpr hg
  -- `2ab ≤ a² + b²`.
  have hmaj : Summable (fun x : ℤ => ‖f (x + d)‖ ^ 2 + ‖g (x + e)‖ ^ 2) := hfs.add hgs
  have hprod : Summable (fun x : ℤ => ‖f (x + d)‖ * ‖g (x + e)‖) :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun x => by nlinarith [sq_nonneg (‖f (x + d)‖ - ‖g (x + e)‖)]) hmaj
  have hprodC : Summable (fun x : ℤ => max C 0 * (‖f (x + d)‖ * ‖g (x + e)‖)) :=
    hprod.mul_left (max C 0)
  -- Dominate the norm of the product and conclude by `Summable.of_norm`.
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hprodC)
  rw [norm_mul, norm_mul]
  calc ‖f (x + d)‖ * ‖g (x + e)‖ * ‖φ x‖
      ≤ ‖f (x + d)‖ * ‖g (x + e)‖ * max C 0 :=
        mul_le_mul_of_nonneg_left (hCb x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = max C 0 * (‖f (x + d)‖ * ‖g (x + e)‖) := by ring

end Work.KMTAreas.A4
