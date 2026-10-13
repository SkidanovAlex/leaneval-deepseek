import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe
import Submission.Work.FTS.StrongEps.E5Aux2.AngFacts
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem L12dens_transport_abs_le {f : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ} {z : ℝ}
    (hMaj0 : ∀ r : ℝ, 0 ≤ Maj r)
    (hslot : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ 1 →
      |Work.Spaces.mixed j i f r θ| ≤ Maj r)
    (hz : 0 < z) :
    |Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) z| ≤ 6 * Maj z / z := by
  have h1z : 0 < 1 + z := by linarith
  have hM : 0 ≤ Maj z := hMaj0 z
  -- `D_θ f = sin(2θ) ∂_θ f` is the `(j,i) = (0,1)` slot of the hypothesis.
  have hD : ∀ θ : ℝ, |Work.Spaces.Dth f z θ| ≤ Maj z := fun θ => by
    have h := hslot z hz θ 0 1 (by norm_num)
    simpa [Work.Spaces.mixed, Work.Spaces.Dth] using h
  have hA : 0 ≤ 6 * Maj z := mul_nonneg (by norm_num) hM
  -- Angular domination: `K θ = 3 sinθ cos²θ ≤ 2 cos θ`, and
  -- `|Transport f z θ| = 3 |D_θ f z θ| / (1+z) ≤ 3 Maj z / (1+z) ≤ 3 Maj z`.
  have hdom : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Coercivity.Transport f z θ|
      ≤ (6 * Maj z) * Real.cos θ := by
    intro θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hK : Work.Spaces.K θ ≤ 2 * Real.cos θ := by
      rw [Work.Spaces.K]
      have hs := Real.sin_le_one (2 * θ)
      have hs2 := Real.sin_two_mul θ
      nlinarith [hc, hs, hs2]
    have htr : |Work.Coercivity.Transport f z θ| ≤ 3 * Maj z / (1 + z) := by
      rw [Work.Coercivity.Transport, abs_div, abs_mul, abs_of_pos h1z,
        show |(3 : ℝ)| = 3 by norm_num]
      exact div_le_div_of_nonneg_right (by linarith [hD θ]) h1z.le
    calc Work.Spaces.K θ * |Work.Coercivity.Transport f z θ|
        ≤ (2 * Real.cos θ) * (3 * Maj z / (1 + z)) :=
          mul_le_mul hK htr (abs_nonneg _) (by linarith [hc])
      _ = (6 * Maj z / (1 + z)) * Real.cos θ := by ring
      _ ≤ (6 * Maj z) * Real.cos θ :=
          mul_le_mul_of_nonneg_right
            (div_le_self (mul_nonneg (by norm_num) hM) (by linarith)) hc
  exact AbsL12densLe (Y := Work.Coercivity.Transport f) (s := z) (A := 6 * Maj z)
    hz hA hdom

end Work.FTS.StrongEps.E5Aux2
