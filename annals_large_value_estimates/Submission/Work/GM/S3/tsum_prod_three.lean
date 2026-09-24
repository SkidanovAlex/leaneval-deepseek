import Mathlib

namespace Work.GM.S3

/-- Fubini for a product of three summable families indexed by `ℤ` (note `ℤ × ℤ × ℤ` is
`ℤ × (ℤ × ℤ)`).  Route: `Summable.tsum_prod` twice, then `tsum_mul_left` / `tsum_mul_right`
(or `tsum_mul_tsum_of_summable_norm`, `summable_mul_of_summable_norm`). -/
theorem tsum_prod_three (f₁ f₂ f₃ : ℤ → ℝ) (h₁ : Summable f₁) (h₂ : Summable f₂)
    (h₃ : Summable f₃) :
    tsum (fun m : ℤ × ℤ × ℤ => f₁ m.1 * f₂ m.2.1 * f₃ m.2.2)
      = tsum (fun a : ℤ => f₁ a) * tsum (fun b : ℤ => f₂ b) * tsum (fun c : ℤ => f₃ c) := by
  -- `tsum_mul_tsum_of_summable_norm` turns a product of two `tsum`s into a `tsum` over the pair,
  -- provided both families are absolutely summable.
  have hm23 : Summable (fun q : ℤ × ℤ => f₂ q.1 * f₃ q.2) :=
    summable_mul_of_summable_norm h₂.norm h₃.norm
  -- Outer Fubini: `ℤ × (ℤ × ℤ)`, splitting off `f₁`.
  have hA := tsum_mul_tsum_of_summable_norm h₁.norm hm23.norm
  -- Inner Fubini: the `ℤ × ℤ` factor for `f₂ * f₃`.
  have hB := tsum_mul_tsum_of_summable_norm h₂.norm h₃.norm
  -- Reassociate the summand `(f₁ * f₂) * f₃` to `f₁ * (f₂ * f₃)`.
  have hsum_eq : tsum (fun m : ℤ × ℤ × ℤ => f₁ m.1 * f₂ m.2.1 * f₃ m.2.2)
      = tsum (fun m : ℤ × ℤ × ℤ => f₁ m.1 * (f₂ m.2.1 * f₃ m.2.2)) :=
    tsum_congr fun m => by ring
  rw [hsum_eq, ← hA, ← hB]
  ring

end Work.GM.S3
