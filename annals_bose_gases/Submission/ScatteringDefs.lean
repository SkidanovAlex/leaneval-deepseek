import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Definitional facts about the scattering length `a v` and `𝓡 v`.

`a v` branches on whether a radial scattering solution exists; `𝓡 v =
∫ v / (8π a v)`.  These facts make the case structure explicit.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
open _root_.BoseGases.IsScatteringSolution
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If a radial scattering solution exists, the scattering length is `(8π)⁻¹ ∫ v(1−w)` for
the chosen solution `w`. -/
lemma a_eq_integral_of_exists (v : ℝ³ → ℝ) (h : ∃ w, IsRadial w ∧ IsScatteringSolution w v) :
    a v = (8 * π)⁻¹ * ∫ x, v x * (1 - (Classical.choose h) x) := by
  unfold a
  rw [dif_pos h]

/-- If no radial scattering solution exists, the scattering length vanishes. -/
lemma a_eq_zero_of_not_exists (v : ℝ³ → ℝ) (h : ¬ ∃ w, IsRadial w ∧ IsScatteringSolution w v) :
    a v = 0 := by
  unfold a
  rw [dif_neg h]

/-- `𝓡 v` is the integral of `v / (8π a v)`. -/
lemma R_eq_integral (v : ℝ³ → ℝ) : 𝓡 v = ∫ x, v x / (8 * π * a v) := by
  rfl

/-- `8π a v` is nonzero when `a v` is. -/
lemma eight_pi_mul_a_ne_zero {v : ℝ³ → ℝ} (ha : a v ≠ 0) : 8 * π * a v ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) Real.pi_ne_zero) ha

end BoseGases

end Submission
