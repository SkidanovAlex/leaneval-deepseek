import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.eNorm_veronese_bounds

/-!
# Lower bound for the Veronese embedding in the Euclidean norm

For `d ≥ 1` and every integer vector `x : Fin (n+1) → ℤ`,

`c · ‖x‖^d ≤ ‖ν_{d,n}(x)‖`

with the explicit positive constant `c = (1/√(n+1))^d`.  This is the lower half of the
two-sided bound `‖ν(x)‖ ≍ ‖x‖^d` proved in `Work.HP.eNorm_veronese_bounds`; here we simply
specialise it to the case `d ≥ 2`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

theorem veronese_enorm_lower (d n : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin (n + 1) → ℤ, c * (eNorm x) ^ d ≤ eNorm (veronese d n x) := by
  obtain ⟨c, _c₂, hc, _hc₂, h⟩ := eNorm_veronese_bounds d n (by omega)
  exact ⟨c, hc, fun x => (h x).1⟩

end Work.HP
