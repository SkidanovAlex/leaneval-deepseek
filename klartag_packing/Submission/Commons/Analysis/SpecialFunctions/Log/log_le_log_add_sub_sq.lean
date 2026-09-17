import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.SpecialFunctions.Log

/-- A second-order Taylor bound for `Real.log` on `[a₀ - r, a₀ + r]`: for `0 ≤ r < a₀`
and `|x| ≤ r`,
`log (a₀ + x) ≤ log a₀ + x / a₀ - x ^ 2 / (2 * (a₀ + r) ^ 2)`.
The function `y ↦ log (a₀ + y) - y / a₀ + y ^ 2 / (2 * (a₀ + r) ^ 2)` is increasing on
`[-r, 0]` and decreasing on `[0, r]`, so it is maximized at `0`. -/
theorem log_le_log_add_sub_sq {a₀ r x : ℝ} (ha₀ : 0 < a₀) (hr : 0 ≤ r) (har : r < a₀)
    (hx : |x| ≤ r) :
    Real.log (a₀ + x) ≤ Real.log a₀ + x / a₀ - x ^ 2 / (2 * (a₀ + r) ^ 2) := by
  obtain ⟨hx_left, hx_right⟩ := abs_le.mp hx
  set b : ℝ := a₀ + r with hb
  have hb_pos : 0 < b := by rw [hb]; linarith
  have ha0_le_b : a₀ ≤ b := by rw [hb]; linarith
  set G : ℝ → ℝ := fun y => Real.log (a₀ + y) - Real.log a₀ - y / a₀ + y ^ 2 / (2 * b ^ 2) with hG
  have hG0 : G 0 = 0 := by simp [hG]
  have hhasderiv : ∀ y : ℝ, 0 < a₀ + y →
      HasDerivAt G (1 / (a₀ + y) - 1 / a₀ + y / b ^ 2) y := by
    intro y hy
    rw [hG]
    have h2 : HasDerivAt (fun x : ℝ => a₀ + x) 1 y := (hasDerivAt_id y).const_add a₀
    have h1 : HasDerivAt (fun x : ℝ => Real.log (a₀ + x)) (1 / (a₀ + y)) y :=
      h2.log (by positivity)
    have h4 : HasDerivAt (fun x : ℝ => x / a₀) (1 / a₀) y := by
      simpa using (hasDerivAt_id y).div_const a₀
    have h5 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * b ^ 2)) (y / b ^ 2) y := by
      have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      have h6 := hp.div_const (2 * b ^ 2)
      have h6' : (2 * y) / (2 * b ^ 2) = y / b ^ 2 := mul_div_mul_left y (b ^ 2) (by norm_num)
      rw [h6'] at h6
      exact h6
    have hmain := ((h1.sub_const (Real.log a₀)).sub h4).add h5
    have hfun : ((fun x => Real.log (a₀ + x) - Real.log a₀) - fun x => x / a₀)
          + (fun x => x ^ 2 / (2 * b ^ 2))
        = fun y => Real.log (a₀ + y) - Real.log a₀ - y / a₀ + y ^ 2 / (2 * b ^ 2) := by
      funext z; simp only [Pi.add_apply, Pi.sub_apply]
    rw [hfun] at hmain
    exact hmain
  have hderiv : ∀ y : ℝ, 0 < a₀ + y → deriv G y = 1 / (a₀ + y) - 1 / a₀ + y / b ^ 2 :=
    fun y hy => (hhasderiv y hy).deriv
  have hsign_left : ∀ y ∈ Set.Icc (-r) 0, 0 ≤ deriv G y := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hypos : 0 < a₀ + y := by linarith
    rw [hderiv y hypos]
    have hkey : (1:ℝ) / (a₀ + y) - 1 / a₀ + y / b ^ 2
        = y * (a₀ * (a₀ + y) - b ^ 2) / (a₀ * (a₀ + y) * b ^ 2) := by
      field_simp
      ring
    rw [hkey]
    apply div_nonneg
    · have hkey2 : a₀ * (a₀ + y) - b ^ 2 ≤ 0 := by
        have hle : a₀ * (a₀ + y) ≤ b * b :=
          mul_le_mul ha0_le_b (by linarith) (le_of_lt hypos) (le_of_lt hb_pos)
        nlinarith [hle]
      exact mul_nonneg_of_nonpos_of_nonpos hy2 hkey2
    · positivity
  have hsign_right : ∀ y ∈ Set.Icc 0 r, deriv G y ≤ 0 := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hypos : 0 < a₀ + y := by linarith
    rw [hderiv y hypos]
    have hkey : (1:ℝ) / (a₀ + y) - 1 / a₀ + y / b ^ 2
        = y * (a₀ * (a₀ + y) - b ^ 2) / (a₀ * (a₀ + y) * b ^ 2) := by
      field_simp
      ring
    rw [hkey]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hkey2 : a₀ * (a₀ + y) - b ^ 2 ≤ 0 := by
        have hle : a₀ * (a₀ + y) ≤ b * b :=
          mul_le_mul ha0_le_b (by rw [hb]; linarith) (le_of_lt hypos) (le_of_lt hb_pos)
        nlinarith [hle]
      exact mul_nonpos_of_nonneg_of_nonpos hy1 hkey2
    · positivity
  have hcont_left : ContinuousOn G (Set.Icc (-r) 0) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    have hypos : 0 < a₀ + y := by obtain ⟨h1, h2⟩ := hy; linarith
    exact (hhasderiv y hypos).continuousAt
  have hcont_right : ContinuousOn G (Set.Icc 0 r) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    have hypos : 0 < a₀ + y := by obtain ⟨h1, h2⟩ := hy; linarith
    exact (hhasderiv y hypos).continuousAt
  have hdiff_left : DifferentiableOn ℝ G (interior (Set.Icc (-r) 0)) := by
    intro y hy
    have hyD : y ∈ Set.Icc (-r) 0 := interior_subset hy
    have hypos : 0 < a₀ + y := by obtain ⟨h1, h2⟩ := hyD; linarith
    exact (hhasderiv y hypos).differentiableAt.differentiableWithinAt
  have hdiff_right : DifferentiableOn ℝ G (interior (Set.Icc 0 r)) := by
    intro y hy
    have hyD : y ∈ Set.Icc 0 r := interior_subset hy
    have hypos : 0 < a₀ + y := by obtain ⟨h1, h2⟩ := hyD; linarith
    exact (hhasderiv y hypos).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn G (Set.Icc (-r) 0) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont_left hdiff_left
      (fun y hy => hsign_left y (interior_subset hy))
  have hanti : AntitoneOn G (Set.Icc 0 r) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont_right hdiff_right
      (fun y hy => hsign_right y (interior_subset hy))
  have hle : G x ≤ G 0 := by
    rcases le_or_gt x 0 with hxle | hxgt
    · exact hmono ⟨hx_left, hxle⟩ ⟨by linarith, le_refl 0⟩ hxle
    · exact hanti ⟨le_refl 0, hr⟩ ⟨le_of_lt hxgt, hx_right⟩ (le_of_lt hxgt)
  rw [hG0] at hle
  rw [hG] at hle
  simp only at hle
  rw [hb] at hle
  linarith

end Commons.Analysis.SpecialFunctions.Log