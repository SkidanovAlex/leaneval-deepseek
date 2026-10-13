import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Dz_alg
import Submission.Work.Coercivity.Dz_zero_at_zero
import Submission.Work.Coercivity.Dz_bound_near_zero
import Submission.Work.Coercivity.Dz_deriv_bound
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- **Near-zero coercivity data.**  If `f` is smooth on a neighbourhood of the closed
quadrant and the boundary quantity `z (D_z f · w)²` vanishes at `z = 0⁺` for every
`θ ∈ [0,π/2]`, then near `z = 0` the function `D_z f`, the boundary quantity
`z (D_z f · w)²` and the derivative `∂_z (z (D_z f · w)²)` are all bounded by the powers
of `z` given below. -/
theorem Dz_near_zero_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
        |Spaces.Dz f z θ| ≤ C * z ^ 2 ∧
        |z * (Spaces.Dz f z θ * Spaces.w z) ^ 2| ≤ C * z ∧
        |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C := by
  -- The boundary condition forces `∂_z f(0,θ) = 0`.
  have h0 : ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0 := Dz_zero_at_zero f hsm hbd
  -- Hence `∂_z f = O(z)` and `∂_z² f = O(1)` uniformly on a small box.
  obtain ⟨M, δ, hδpos, hδle1, hMnn, hbdM⟩ := Dz_bound_near_zero f hsm h0
  set C : ℝ := max 1 (max M (80 * M ^ 2)) with hCdef
  have hCM : M ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left M (80 * M ^ 2)) (le_max_right 1 (max M (80 * M ^ 2)))
  have hC80 : 80 * M ^ 2 ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right M (80 * M ^ 2)) (le_max_right 1 (max M (80 * M ^ 2)))
  have hC16 : 16 * M ^ 2 ≤ C := by
    have h1 : (16:ℝ) * M ^ 2 ≤ 80 * M ^ 2 := by nlinarith [sq_nonneg M]
    exact le_trans h1 hC80
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨C, δ, hCpos, hδpos, ?_⟩
  intro z hz θ hθ
  obtain ⟨h1z, h2z⟩ := hbdM z hz θ hθ
  have hzpos : 0 < z := hz.1
  have hzle1 : z ≤ 1 := le_of_lt (lt_of_lt_of_le hz.2 hδle1)
  -- (1) `|D_z f| ≤ C z²`.
  have hDzb : |Spaces.Dz f z θ| ≤ M * z ^ 2 := by
    have hstep : |Spaces.Dz f z θ| = z * |Spaces.pz f z θ| := by
      rw [Spaces.Dz, abs_mul, abs_of_pos hzpos]
    rw [hstep]
    calc z * |Spaces.pz f z θ| ≤ z * (M * z) :=
          mul_le_mul_of_nonneg_left h1z (le_of_lt hzpos)
      _ = M * z ^ 2 := by ring
  -- (2) `|z (D_z f · w)²| ≤ C z`.
  have hw : |Spaces.w z| ≤ 4 / z ^ 2 := by
    have h1 : |Spaces.w z| = (1 + z) ^ 2 / z ^ 2 := by
      rw [Spaces.w, abs_div, abs_of_nonneg (sq_nonneg (1 + z)), abs_of_nonneg (sq_nonneg z)]
    rw [h1]
    have h1z2 : (1 + z) ^ 2 ≤ 4 := by
      have hprod : 0 ≤ (1 - z) * (z + 3) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact div_le_div_of_nonneg_right h1z2 (sq_nonneg z)
  have hDzw : |Spaces.Dz f z θ * Spaces.w z| ≤ 4 * M := by
    rw [abs_mul]
    calc |Spaces.Dz f z θ| * |Spaces.w z| ≤ (M * z ^ 2) * (4 / z ^ 2) :=
          mul_le_mul hDzb hw (abs_nonneg _) (mul_nonneg hMnn (sq_nonneg z))
      _ = 4 * M := by field_simp
  -- (3) `|∂_z (z (D_z f · w)²)| ≤ C`.
  have h3 : |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C := by
    have h := Dz_deriv_bound f hsm hθ hzpos hzle1 h1z h2z
    have hval : 32 * M * M + 48 * M ^ 2 = 80 * M ^ 2 := by ring
    rw [hval] at h
    linarith [h, hC80]
  refine ⟨?_, ?_, h3⟩
  · calc |Spaces.Dz f z θ| ≤ M * z ^ 2 := hDzb
      _ ≤ C * z ^ 2 := mul_le_mul_of_nonneg_right hCM (sq_nonneg z)
  · have hsq : (Spaces.Dz f z θ * Spaces.w z) ^ 2 ≤ (4 * M) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0:ℝ) ≤ 4 * M)]
      exact hDzw
    rw [abs_mul, abs_of_pos hzpos, abs_of_nonneg (sq_nonneg _)]
    calc z * (Spaces.Dz f z θ * Spaces.w z) ^ 2 ≤ z * (4 * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (le_of_lt hzpos)
      _ = 16 * M ^ 2 * z := by ring
      _ ≤ C * z := mul_le_mul_of_nonneg_right hC16 (le_of_lt hzpos)

end Work.Coercivity
