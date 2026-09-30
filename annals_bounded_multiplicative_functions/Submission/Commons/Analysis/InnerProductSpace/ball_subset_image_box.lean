import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.InnerProductSpace

/-- If the linear map `w ↦ ∑ i, w i • s i` expands norms by at least a factor `c > 0`,
then it maps the box `[-1,1]^l` onto the ball of radius `c`. -/
theorem ball_subset_image_box {l : ℕ} {c : ℝ} (hc : 0 < c)
    (s : Fin l → EuclideanSpace ℝ (Fin l))
    (hs : ∀ w : Fin l → ℝ, c * ‖w‖ ≤ ‖∑ i : Fin l, w i • s i‖) :
    Metric.ball 0 c ⊆
      (fun w : Fin l → ℝ => ∑ i : Fin l, w i • s i) '' {w : Fin l → ℝ | ∀ i, |w i| ≤ 1} := by
  intro v hv
  rw [Metric.mem_ball, dist_eq_norm] at hv
  have hv' : ‖v‖ < c := by simpa using hv
  -- The linear map `T w = ∑ i, w i • s i`.
  let T : (Fin l → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin l) := Fintype.linearCombination ℝ s
  have hT : ∀ w : Fin l → ℝ, T w = ∑ i : Fin l, w i • s i :=
    fun w => Fintype.linearCombination_apply ℝ s w
  -- `T` is injective, because it strictly expands norms.
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : c * ‖w‖ ≤ ‖T w‖ := by rw [hT w]; exact hs w
    rw [hw, norm_zero] at h1
    have h3 : ‖w‖ ≤ 0 := by
      have : c * ‖w‖ ≤ c * 0 := by simpa using h1
      exact le_of_mul_le_mul_left this hc
    have h4 : ‖w‖ = 0 := le_antisymm h3 (norm_nonneg w)
    simpa using h4
  -- Injectivity plus equal dimensions gives surjectivity.
  have hfin : Module.finrank ℝ (Fin l → ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin l)) := by simp
  have hT_surj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hT_inj
  obtain ⟨w, hw⟩ := hT_surj v
  refine ⟨w, ?_, ?_⟩
  · -- The preimage `w` lies in the box.
    intro i
    have h1 : c * ‖w‖ ≤ ‖v‖ := by
      have : c * ‖w‖ ≤ ‖T w‖ := by rw [hT w]; exact hs w
      rwa [hw] at this
    have h2 : ‖w‖ < 1 := by
      have : c * ‖w‖ < c * 1 := by
        have := lt_of_le_of_lt h1 hv'
        simpa using this
      nlinarith [hc, this, norm_nonneg w]
    calc |w i| = ‖w i‖ := (Real.norm_eq_abs (w i)).symm
      _ ≤ ‖w‖ := norm_le_pi_norm w i
      _ ≤ 1 := le_of_lt h2
  · simpa [hT] using hw

end Commons.Analysis.InnerProductSpace