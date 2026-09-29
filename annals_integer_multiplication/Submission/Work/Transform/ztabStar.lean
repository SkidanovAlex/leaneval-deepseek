import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.bluesteinDefs

namespace Work.Transform

/-- `ζ^c = e^{πi c/r}` written with `expPi`. -/
lemma zeta_eq_expPi (r c : ℕ) : zeta r c = expPi ((c : ℝ) / (r : ℝ)) := by
  rw [zeta, expPi]
  congr 1
  rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast, mul_div_assoc]

/-- Conjugate of `ζ^c`, as an `expPi`. -/
lemma star_zeta (r c : ℕ) : star (zeta r c) = expPi (-((c : ℝ) / (r : ℝ))) := by
  rw [zeta_eq_expPi, star_expPi]

/-- `expPi x * expPi (-x) = 1`. -/
lemma expPi_mul_expPi_neg (x : ℝ) : expPi x * expPi (-x) = 1 := by
  rw [← expPi_add, add_neg_cancel, expPi_zero]

/-- **Conjugation of `ζ` and of a fixed-point complex number.**

Three facts used to transfer the error bound of the forward `ζ`-table to its conjugate table in
`Work.Transform.ztabWord`:

1. `star (zeta r c) = zetaInv r c`: `ζ^c = e^{πi c/r}` has modulus `1`, so its conjugate is its
   inverse; `Work.Transform.zetaInv r c = (zeta r c)⁻¹` and
   `zeta r c = e^{πi c/r} = expPi (c/r)` with `Work.Transform.expPi` of
   `Submission/Work/Transform/bluesteinDefs.lean` (`star_expPi` gives
   `star (expPi z) = expPi (-z)`; equivalently `norm_zeta = 1` and `star z = z⁻¹`);
2. `fxC p (z.1, -z.2) = star (fxC p z)`: `fxC p z = (z.1 + z.2 * I) / 2^p` with the real
   denominator `2^p`, so conjugating negates the imaginary part;
3. `‖star a - star b‖ = ‖a - b‖` for `a b : ℂ` (conjugation is an isometry). -/
theorem ztabStar :
    (∀ (r c : ℕ), star (Work.Transform.zeta r c) = Work.Transform.zetaInv r c) ∧
    (∀ (p : ℕ) (z : ℤ × ℤ), HvdH.fxC p (z.1, -z.2) = star (HvdH.fxC p z)) ∧
    (∀ (a b : ℂ), ‖star a - star b‖ = ‖a - b‖) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r c
    rw [star_zeta, zetaInv, zeta_eq_expPi]
    exact eq_inv_of_mul_eq_one_right (expPi_mul_expPi_neg _)
  · intro p z
    unfold HvdH.fxC
    simp
  · intro a b
    rw [← star_sub, norm_star]

end Work.Transform
