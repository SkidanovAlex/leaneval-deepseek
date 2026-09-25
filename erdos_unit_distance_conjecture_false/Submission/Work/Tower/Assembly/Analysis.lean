import Submission.Work.Tower.Assembly.Setup
import Submission.Work.Tower.Unramified.All

/-!
# Assembly: elementary real analysis for the root discriminant
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace Assembly

/-- Root discriminant from the absolute discriminant and the degree. -/
lemma rootDiscr_eq_rpow {F : Type*} [Field F] [NumberField F] {n : ℕ} {D : ℕ}
    (hn : Module.finrank ℚ F = n) (hd : |NumberField.discr F| = (D : ℤ)) :
    NumberField.rootDiscr F = (D : ℝ) ^ ((n : ℝ)⁻¹) := by
  rw [NumberField.rootDiscr_def, hd, hn]
  norm_num

/-- `(x ^ 2) ^ (1/3) = exp ((2/3) log x)` for `x > 0`. -/
lemma rpow_two_third (x : ℝ) (hx : 0 < x) :
    (x ^ 2 : ℝ) ^ ((3 : ℝ)⁻¹) = Real.exp ((2 / 3) * Real.log x) := by
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < x ^ 2), Real.log_pow, Real.exp_eq_exp]
  ring

/-- The root discriminant bound for the base field: if `|disc F| = (∏ rᵢ)²` and `[F:ℚ] = 3`, then
`rootDiscr F = exp ((2/3) * ∑ log rᵢ)`. -/
lemma rootDiscr_eq_exp {F : Type*} [Field F] [NumberField F] {ℓ : ℕ} (r : Fin ℓ → ℕ)
    (hr : ∀ i, 0 < r i) (h3 : Module.finrank ℚ F = 3)
    (hd : |NumberField.discr F| = ((∏ i, r i : ℕ) : ℤ) ^ 2) :
    NumberField.rootDiscr F = Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) := by
  have hpos : (0 : ℝ) < ((∏ i, r i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun i _ => hr i
  have hlog : Real.log ((∏ i, r i : ℕ) : ℝ) = ∑ i, Real.log (r i : ℝ) := by
    rw [show ((∏ i, r i : ℕ) : ℝ) = ∏ i, (r i : ℝ) by push_cast; rfl]
    rw [Real.log_prod (fun i _ => by exact_mod_cast (hr i).ne')]
  have hcast : (((∏ i, r i : ℕ) ^ 2 : ℕ) : ℝ) = (((∏ i, r i : ℕ) : ℝ) ^ 2) := by
    push_cast; ring
  have hDvd : |NumberField.discr F| = (((∏ i, r i : ℕ) ^ 2 : ℕ) : ℤ) := by
    rw [hd]; push_cast; ring
  rw [rootDiscr_eq_rpow h3 hDvd, hcast, ← hlog]
  exact rpow_two_third _ hpos

end Assembly
end Tower
end Work
