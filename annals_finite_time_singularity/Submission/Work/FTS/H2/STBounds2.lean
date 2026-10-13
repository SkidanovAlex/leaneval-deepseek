import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.H2.STBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `min θ (π/2 - θ) ≤ (π/4)·sin(2θ)` on `Iθ`. -/
theorem min_le_sin (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    min θ (π / 2 - θ) ≤ (π / 4) * Real.sin (2 * θ) := by
  have h := sin_two_ge_min θ hθ
  have h4 : ((π / 4) * (4 / π)) * min θ (π / 2 - θ) ≤ (π / 4) * Real.sin (2 * θ) := by
    calc ((π / 4) * (4 / π)) * min θ (π / 2 - θ)
        = (π / 4) * ((4 / π) * min θ (π / 2 - θ)) := by ring
      _ ≤ (π / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h (by positivity)
  have he : (π / 4) * (4 / π) = 1 := by field_simp
  rwa [he, one_mul] at h4

/-- The scaled `z`-derivative bound, for `z > 0`. -/
theorem z_pzIter_bound {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hvt : Spaces.VanishTheta f) (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) :
    ∀ k ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Spaces.Iθ,
      |z ^ k * Spaces.pzIter k f z θ|
        ≤ 100 * Real.sin (2 * θ) * Spaces.WlInf α 4 (Spaces.pth f) := by
  intro k hk z hz θ hθ
  set W := Spaces.WlInf α 4 (Spaces.pth f) with hWdef
  have hWnn : 0 ≤ W := WlInf_nonneg hW
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
  · subst hθ0
    rw [pzIter_eq_zero_of_slice_zero (fun z => hvt.1 z) k z]
    simp [Real.sin_zero]
  rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
  · subst hθ1
    rw [pzIter_eq_zero_of_slice_zero (fun z => hvt.2 z) k z]
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp
  have h2 := (pzIter_bound_aux hsm hcont hvt hW k hk).1 z hz θ ⟨hθ0, hθ1⟩
  have h3 := (pzIter_bound_aux hsm hcont hvt hW k hk).2 z hz θ ⟨hθ0, hθ1⟩
  have h4 : |Spaces.pzIter k f z θ| ≤ 100 * min θ (π / 2 - θ) * W / (z + 1) ^ k := by
    rcases min_choice (α := ℝ) (a := θ) (b := π / 2 - θ) with hh | hh
    · rw [hh]; simpa only [hWdef] using h2
    · rw [hh]; simpa only [hWdef] using h3
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz.le k)]
  have h5 : (0:ℝ) < (z + 1) ^ k := pow_pos (by linarith [Set.mem_Ioi.mp hz]) _
  have h6 : z ^ k / (z + 1) ^ k ≤ 1 := by
    rw [div_le_one h5]; exact pow_le_pow_left₀ hz.le (by linarith [Set.mem_Ioi.mp hz]) _
  have h9 := min_le_sin θ hθ
  calc z ^ k * |Spaces.pzIter k f z θ|
      ≤ z ^ k * (100 * min θ (π / 2 - θ) * W / (z + 1) ^ k) :=
        mul_le_mul_of_nonneg_left h4 (pow_nonneg hz.le k)
    _ = (z ^ k / (z + 1) ^ k) * (100 * min θ (π / 2 - θ) * W) := by
        field_simp
    _ ≤ 1 * (100 * min θ (π / 2 - θ) * W) :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = 100 * min θ (π / 2 - θ) * W := one_mul _
    _ ≤ 100 * Real.sin (2 * θ) * W := by
        have h10 : 100 * min θ (π / 2 - θ) * W ≤ 100 * ((π / 4) * Real.sin (2 * θ)) * W :=
          mul_le_mul_of_nonneg_right (by linarith [h9]) hWnn
        have h12 : (0:ℝ) ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
        have h11 : 100 * ((π / 4) * Real.sin (2 * θ)) * W ≤ 100 * Real.sin (2 * θ) * W := by
          have h13 : (π / 4) * Real.sin (2 * θ) ≤ Real.sin (2 * θ) := by
            nlinarith [Real.pi_lt_four, h12]
          have h14 : (0:ℝ) ≤ 100 * W := by positivity
          calc 100 * ((π / 4) * Real.sin (2 * θ)) * W
              = 100 * W * ((π / 4) * Real.sin (2 * θ)) := by ring
            _ ≤ 100 * W * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h13 h14
            _ = 100 * Real.sin (2 * θ) * W := by ring
        linarith [h10, h11]

end Work.FTS.H2
