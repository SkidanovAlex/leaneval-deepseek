import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem abs_Transport_slotMaj_le {f : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hslot : ∀ θ : ℝ, |Work.Spaces.mixed 0 1 f z θ| ≤ Maj z) :
    ∀ θ : ℝ, |Work.Coercivity.Transport f z θ| ≤ 3 * Maj z / (1 + z) := by
  intro θ
  -- `Transport f z θ = 3 · D_θ f z θ / (1+z)` and `D_θ f = mixed 0 1 f`, definitionally.
  rw [show Work.Coercivity.Transport f z θ
      = 3 * Work.Spaces.mixed 0 1 f z θ / (1 + z) from rfl]
  have hz1 : (0:ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos hz1, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hslot θ) (by norm_num)) hz1.le

end Work.FTS.StrongEps.E5Aux2
