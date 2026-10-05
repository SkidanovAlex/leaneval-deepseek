import Mathlib
import Submission.Work.RPCore.Defs

namespace Work.RPCore.Saddle

open Work.RPCore.Port.Whitney.RetractionSucc

/-- **No escape from the linking obstruction.**

Let `c : ℝ^k → ℝ × (ℝ^k × ℝ^l)` be continuous and assume that on the unit sphere `c` agrees with
the "identity" embedding `u ↦ (a₀, (u, 0))`.  Then the middle `ℝ^k`-component of `c` vanishes
somewhere in the closed unit ball.

Equivalently: the continuous map `f u = (c u).2.1` is the identity on the unit sphere, so if it
were zero-free on the whole closed ball, then `u ↦ ‖f u‖⁻¹ • f u` would be a continuous retraction
of the closed ball onto its boundary sphere — impossible by
`Work.RPCore.Port.Whitney.noRetractionBallSphere`. -/
theorem linking_no_escape {k : ℕ} (hk : 1 ≤ k) {l : ℕ} (a₀ : ℝ)
    (c : EuclideanSpace ℝ (Fin k) → ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))
    (hc : Continuous c) (hbc : ∀ u, ‖u‖ = 1 → c u = (a₀, (u, 0))) :
    ∃ u, ‖u‖ ≤ 1 ∧ (c u).2.1 = 0 := by
  by_contra hcon
  -- Suppose the middle component is zero-free on the closed unit ball.
  have hno : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ 1 → (c u).2.1 ≠ 0 := by
    intro u hu hzero
    exact hcon ⟨u, hu, hzero⟩
  -- The middle component as a self-map of `ℝ^k`, which is the identity on the unit sphere.
  set f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun u => (c u).2.1 with hf
  have hf_cont : Continuous f := by
    rw [hf]; exact hc.snd.fst
  have hf_sphere : ∀ u, ‖u‖ = 1 → f u = u := by
    intro u hu
    rw [hf]
    change (c u).2.1 = u
    rw [hbc u hu]
  -- Clamp the argument into the closed unit ball so that we get a globally defined,
  -- everywhere-nonzero map whose normalisation is a global continuous retraction.
  set g : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun z => f (radialClamp z) with hg
  have hg_cont : Continuous g := by
    rw [hg]; exact hf_cont.comp continuous_radialClamp
  have hg_ne : ∀ z, g z ≠ 0 := by
    intro z
    rw [hg]
    exact hno (radialClamp z) (norm_radialClamp_le z)
  -- The resulting retraction of the closed unit ball onto the unit sphere.
  set F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun z => (‖g z‖)⁻¹ • g z with hF
  have hF_cont : Continuous F := by
    rw [hF]
    exact ((hg_cont.norm).inv₀ (fun z => norm_ne_zero_iff.mpr (hg_ne z))).smul hg_cont
  have hF_fix : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1, F z = z := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    rw [hF]
    change (‖g z‖)⁻¹ • g z = z
    have hclamp : radialClamp z = z := radialClamp_eq_of_le_one (le_of_eq hz)
    have hgz : g z = z := by
      rw [hg]
      change f (radialClamp z) = z
      rw [hclamp, hf_sphere z hz]
    rw [hgz, hz]
    simp
  have hF_ball : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
      F z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    rw [hF]
    show ‖(‖g z‖)⁻¹ • g z‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg (g z))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg_ne z))
  exact Work.RPCore.Port.Whitney.noRetractionBallSphere (N := k)
    (c := (0 : EuclideanSpace ℝ (Fin k))) (r := 1) (by norm_num) ⟨F, hF_cont, hF_fix, hF_ball⟩

end Work.RPCore.Saddle
