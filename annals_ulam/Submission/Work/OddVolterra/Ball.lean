import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The unperturbed (ball) moment equations

For `h = 0`, `f = semicircle`, `x = y = profileX` the two moment equations hold with
`C = oddSemicircleMomentConstant n`: this is the base configuration of the transition-slope
argument.  The first equation is the scaling identity `oddSemicircleMoment_scale`, the second
is the vanishing of the odd-integrand integral `oddSemicircleWeight_t_integral_zero`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra

open Commons.Geometry.Ulam

noncomputable section

/-- The ball radicand: for `h = 0` and `f = semicircle` the integrand of the first moment
equation is `(1 - (1+s²) t²)^n √(1 - (1+s²) t²)`. -/
lemma ball_psi (s t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    psi (fun _ : ℝ => 0) semicircle s t = 1 - (1 + s ^ 2) * t ^ 2 := by
  unfold psi line
  rw [semicircle_sq_of_mem_Icc ht]
  ring

lemma neg_profileX_mem_Icc (s : ℝ) : -(profileX s) ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := profileX_mem_Icc s
  exact ⟨by linarith, by linarith⟩

/-- The first moment equation holds for the ball configuration with `h = 0`. -/
theorem ball_momentF (n : ℕ) {s : ℝ} (hs : 0 < s) :
    momentF n (fun _ : ℝ => 0) profileX profileX semicircle s =
      oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2) := by
  have hpos : 0 < profileX s := profileX_pos s hs
  have hle : -profileX s ≤ profileX s := by linarith
  have hmem1 : -(profileX s) ∈ Set.Icc (-1 : ℝ) 1 := neg_profileX_mem_Icc s
  have hmem2 : profileX s ∈ Set.Icc (-1 : ℝ) 1 := profileX_mem_Icc s
  have hmain :
      (∫ t in (-profileX s)..(profileX s),
          psi (fun _ : ℝ => 0) semicircle s t ^ n *
            Real.sqrt (psi (fun _ : ℝ => 0) semicircle s t))
        = ∫ t in (-profileX s)..(profileX s),
            (1 - (1 + s ^ 2) * t ^ 2) ^ n * Real.sqrt (1 - (1 + s ^ 2) * t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans hmem1.1 ht.1, le_trans ht.2 hmem2.2⟩
    beta_reduce
    rw [ball_psi s t htIcc]
  unfold momentF momentIntegrand
  rw [hmain]
  exact oddSemicircleMoment_scale n hs

/-- The second (centroid) moment equation holds for the ball configuration with `h = 0`. -/
theorem ball_momentH (n : ℕ) {s : ℝ} (hs : 0 < s) :
    momentH n (fun _ : ℝ => 0) profileX profileX semicircle s = 0 := by
  have hpos : 0 < profileX s := profileX_pos s hs
  have hle : -profileX s ≤ profileX s := by linarith
  have hmem1 : -(profileX s) ∈ Set.Icc (-1 : ℝ) 1 := neg_profileX_mem_Icc s
  have hmain :
      (∫ t in (-profileX s)..(profileX s),
          psi (fun _ : ℝ => 0) semicircle s t ^ (n - 1) *
            Real.sqrt (psi (fun _ : ℝ => 0) semicircle s t) * lineSlope (fun _ : ℝ => 0) s t)
        = ∫ t in (-profileX s)..(profileX s), oddSemicircleWeight n s t * t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans hmem1.1 ht.1, le_trans ht.2 (profileX_mem_Icc s).2⟩
    beta_reduce
    rw [ball_psi s t htIcc]
    unfold oddSemicircleWeight lineSlope
    simp
  unfold momentH centroidIntegrand
  rw [hmain]
  exact oddSemicircleWeight_t_integral_zero n s (profileX s)

end

end Work.OddVolterra
