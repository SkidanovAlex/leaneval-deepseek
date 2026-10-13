import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

/-- The elementary inequality `sin t - t * cos t ≤ t ^ 3 / 3` for `t ≥ 0`.

(It is the statement that `t ↦ t ^ 3 / 3 - (sin t - t cos t)` is nondecreasing on `[0, ∞)`,
its derivative being `t * (t - sin t) ≥ 0`.) -/
theorem sin_sub_mul_cos_le_cube_div_three (t : ℝ) (ht : 0 ≤ t) :
    Real.sin t - t * Real.cos t ≤ t ^ 3 / 3 := by
  let f : ℝ → ℝ := fun x => x ^ 3 / 3 - (Real.sin x - x * Real.cos x)
  have hderiv (x : ℝ) : deriv f x = x ^ 2 - x * Real.sin x := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [hderiv]
      have hx0 : 0 < x := by simpa using hx
      nlinarith [Real.sin_lt hx0]
  have h0 : f 0 = 0 := by simp [f]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [h0, f] at this
  linarith

/-- The numerical crux: for `0 < t < π/2`,
`(sin t - t cos t) (1 + cos²t) / sin³t ≤ π³ / 12`.

The proof is the sharp chain `sin t - t cos t ≤ t³/3` (previous lemma), `1 + cos²t ≤ 2`, and
Jordan's inequality `2t/π ≤ sin t` (so `sin³t ≥ (2t/π)³`), which combine to
`(t³/3)·2/(2t/π)³ = π³/12`. -/
theorem sin_sub_mul_cos_div_sin_cube_le (t : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi / 2) :
    (Real.sin t - t * Real.cos t) * (1 + Real.cos t ^ 2) / Real.sin t ^ 3
      ≤ Real.pi ^ 3 / 12 := by
  have hsin_pos : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos, ht1])
  have hS : Real.sin t - t * Real.cos t ≤ t ^ 3 / 3 :=
    sin_sub_mul_cos_le_cube_div_three t ht0.le
  have hc2 : 1 + Real.cos t ^ 2 ≤ 2 := by
    have := Real.cos_sq_le_one t
    linarith
  have hJ1 : (Real.sin t - t * Real.cos t) * (1 + Real.cos t ^ 2) ≤ 2 * t ^ 3 / 3 := by
    have h1 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 1 + Real.cos t ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ t ^ 3 / 3)
    nlinarith [h1, h2]
  have hsin3 : (2 / Real.pi * t) ^ 3 ≤ Real.sin t ^ 3 := by
    have h := Real.mul_le_sin ht0.le (le_of_lt ht1)
    exact pow_le_pow_left₀ (by positivity) h 3
  have hR : 2 * t ^ 3 / 3 ≤ (Real.pi ^ 3 / 12) * Real.sin t ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hsin3 (by positivity : (0 : ℝ) ≤ Real.pi ^ 3 / 12)
    have heq : (Real.pi ^ 3 / 12) * (2 / Real.pi * t) ^ 3 = 2 * t ^ 3 / 3 := by
      field_simp
      ring
    linarith [h, heq]
  rw [div_le_iff₀ (pow_pos hsin_pos 3)]
  linarith [hJ1, hR]

theorem axisJterm_le (θ0 Jv ε : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hε : 0 ≤ ε)
    (hJ : |Jv| ≤ ε * (Real.sin (Real.pi / 2 - θ0) - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0))) :
    |Jv * (1 + Real.sin θ0 ^ 2) / Real.cos θ0 ^ 3| ≤ ε * (Real.pi ^ 3 / 12) := by
  set t := Real.pi / 2 - θ0 with ht
  have ht0 : 0 < t := by rw [ht]; linarith [hθ0.2]
  have ht1 : t < Real.pi / 2 := by rw [ht]; linarith [hθ0.1]
  have hcos_pos : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩
  have hsin_eq : Real.sin θ0 = Real.cos t := by
    rw [ht]; exact (Real.cos_pi_div_two_sub θ0).symm
  have hcos_eq : Real.cos θ0 = Real.sin t := by
    rw [ht]; exact (Real.sin_pi_div_two_sub θ0).symm
  have hJ' : |Jv| ≤ ε * (Real.sin t - t * Real.cos t) := by
    have hthis : Real.sin (Real.pi / 2 - θ0) - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0)
        = Real.sin t - t * Real.cos t := by
      rw [ht]
    rw [hthis] at hJ
    exact hJ
  have hA : 0 < 1 + Real.sin θ0 ^ 2 := by positivity
  have hB : 0 < Real.cos θ0 ^ 3 := pow_pos hcos_pos 3
  have hL : |Jv * (1 + Real.sin θ0 ^ 2) / Real.cos θ0 ^ 3|
      = |Jv| * (1 + Real.cos t ^ 2) / Real.sin t ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hB, hsin_eq, hcos_eq]
  rw [hL]
  have hsin_pos : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos, ht1])
  have hF : 0 ≤ (1 + Real.cos t ^ 2) / Real.sin t ^ 3 :=
    div_nonneg (by positivity) (pow_nonneg hsin_pos.le 3)
  calc |Jv| * (1 + Real.cos t ^ 2) / Real.sin t ^ 3
      = |Jv| * ((1 + Real.cos t ^ 2) / Real.sin t ^ 3) := by ring
    _ ≤ ε * (Real.sin t - t * Real.cos t) * ((1 + Real.cos t ^ 2) / Real.sin t ^ 3) :=
        mul_le_mul_of_nonneg_right hJ' hF
    _ = ε * ((Real.sin t - t * Real.cos t) * (1 + Real.cos t ^ 2) / Real.sin t ^ 3) := by ring
    _ ≤ ε * (Real.pi ^ 3 / 12) :=
        mul_le_mul_of_nonneg_left (sin_sub_mul_cos_div_sin_cube_le t ht0 ht1) hε

end Work.FTS_StreamBdry.SB25Aux
