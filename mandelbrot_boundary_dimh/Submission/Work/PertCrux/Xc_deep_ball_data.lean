import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Parab.Setup
import Submission.Work.Parab.inversion.exists_mul_log_lt
import Submission.Work.Pert.tools
import Submission.Work.PertCrux.Xc_strip_log_bounds
import Submission.Work.PertCrux.Xc_local_three
import Submission.Work.PertCrux.Xc_strip_ball_geometry

namespace Work.PertCrux

open Complex Metric

/-- **Deep-ball data for the Cayley curve of a parabolic datum.**

For every `T ≥ 0` there are constants `c₁ > 0` and `M₁ > 0` such that for every `M ≥ M₁` and
every point `u` of the deep horizontal strip `Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}`,
the closed ball of radius `c₁ (1 + log (2M))` around `u`

* lies in the sector `QLeft ξ₀` (where the Fatou coordinate `φ₀` is defined),
* is a holomorphy disc for the Cayley curve `Xc d = τ₀ ∘ φ₀`, on which `‖(Xc d)' - 1‖ ≤ 1/2`,
* and the curve displaces `u` by at most a quarter of that radius.

The three first conclusions are harvested from `Xc_strip_ball_geometry` (the elementary geometry
of the strip: a point at distance `≤ r ≤ M/16` from the strip stays in the left half-plane
`{Re z < -ξ₀}`, and so does its `‖z‖/10`-ball) and `Xc_local_three` (the sector-local data at a
point, a corollary of `Xcurve_bounds`).  The fourth is the logarithmic displacement bound
`Xc_strip_log_bounds`, with `c₁ = 4C` so that the strip estimate `C (1 + log M)` is absorbed by
`c₁ (1 + log 2M) / 4 = C (1 + log 2M)`. -/
theorem Xc_deep_ball_data {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ M₁ : ℝ, 0 < M₁ ∧
    ∀ M : ℝ, M₁ ≤ M → ∀ u : ℂ, u ∈ Work.Pert.Dstrip M T →
      (∀ z : ℂ, ‖z - u‖ ≤ c₁ * (1 + Real.log (2 * M)) → z ∈ MandelDim.QLeft d.ξ₀) ∧
      (∀ z : ℂ, ‖z - u‖ ≤ c₁ * (1 + Real.log (2 * M)) →
        DifferentiableAt ℂ (Work.Pert.Xc d) z) ∧
      (∀ z : ℂ, ‖z - u‖ ≤ c₁ * (1 + Real.log (2 * M)) →
        ‖deriv (Work.Pert.Xc d) z - 1‖ ≤ 1 / 2) ∧
      ‖Work.Pert.Xc d u - u‖ ≤ c₁ * (1 + Real.log (2 * M)) / 4 := by
  -- the logarithmic displacement bound on the strip
  obtain ⟨C, M_C, hCpos, _hM_Cpos, hstrip⟩ := Xc_strip_log_bounds d
  -- the sector-local data at a deep point
  obtain ⟨R, _hRpos, hloc⟩ := Xc_local_three d
  -- the strip/ball geometry
  obtain ⟨M_G, _hM_Gpos, hgeom⟩ := Xc_strip_ball_geometry d R
  -- the absorption `4C (1 + log (2M)) ≤ M/16` for large `M`
  obtain ⟨M_abs, _hM_abs_pos, hM_abs⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := 4 * C) (b := 4 * C) (c := 1 / 16)
      (by norm_num)
  refine ⟨4 * C, by linarith, max M_G (max M_C (max M_abs (max 1 T))), ?_, ?_⟩
  · -- positivity of the scale `M₁`
    refine lt_of_lt_of_le one_pos ?_
    exact le_trans (le_max_left 1 T)
      (le_trans (le_max_right M_abs (max 1 T))
        (le_trans (le_max_right M_C (max M_abs (max 1 T)))
          (le_max_right M_G (max M_C (max M_abs (max 1 T))))))
  · intro M hM u hu
    have hMG : M_G ≤ M :=
      le_trans (le_max_left M_G (max M_C (max M_abs (max 1 T)))) hM
    have hMC : M_C ≤ M :=
      le_trans (le_max_left M_C (max M_abs (max 1 T)))
        (le_trans (le_max_right M_G (max M_C (max M_abs (max 1 T)))) hM)
    have hMabs : M_abs ≤ M :=
      le_trans (le_max_left M_abs (max 1 T))
        (le_trans (le_max_right M_C (max M_abs (max 1 T)))
          (le_trans (le_max_right M_G (max M_C (max M_abs (max 1 T)))) hM))
    have hM1 : (1 : ℝ) ≤ M :=
      le_trans (le_max_left 1 T)
        (le_trans (le_max_right M_abs (max 1 T))
          (le_trans (le_max_right M_C (max M_abs (max 1 T)))
            (le_trans (le_max_right M_G (max M_C (max M_abs (max 1 T)))) hM)))
    have hMT : T ≤ M :=
      le_trans (le_max_right 1 T)
        (le_trans (le_max_right M_abs (max 1 T))
          (le_trans (le_max_right M_C (max M_abs (max 1 T)))
            (le_trans (le_max_right M_G (max M_C (max M_abs (max 1 T)))) hM)))
    have hMpos : 0 < M := by linarith
    have hr_nonneg : 0 ≤ 4 * C * (1 + Real.log (2 * M)) := by
      have hlog : (0 : ℝ) ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
      have h1 : (0 : ℝ) ≤ 1 + Real.log (2 * M) := by linarith
      exact mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * C) h1
    have hr_le : 4 * C * (1 + Real.log (2 * M)) ≤ M / 16 := by
      have h := hM_abs M hMabs
      nlinarith [h]
    -- the geometry, specialized to the radius `4C (1 + log 2M)`
    have hgeom' : ∀ z : ℂ, ‖z - u‖ ≤ 4 * C * (1 + Real.log (2 * M)) →
        z ∈ MandelDim.QLeft d.ξ₀ ∧ Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ ∧
          R ≤ ‖z‖ :=
      fun z hz => hgeom M hMG T hT hMT (4 * C * (1 + Real.log (2 * M)))
        hr_nonneg hr_le u hu z hz
    refine ⟨fun z hz => (hgeom' z hz).1,
      fun z hz => (hloc z (hgeom' z hz).1 (hgeom' z hz).2.2 (hgeom' z hz).2.1).1,
      fun z hz => (hloc z (hgeom' z hz).1 (hgeom' z hz).2.2 (hgeom' z hz).2.1).2, ?_⟩
    -- the displacement estimate at the centre `u`
    have h1 := (hstrip M hMC T hT hMT u hu).1
    have hlogle : Real.log M ≤ Real.log (2 * M) := Real.log_le_log hMpos (by linarith)
    have hkey : C * (1 + Real.log M) ≤ 4 * C * (1 + Real.log (2 * M)) / 4 := by
      have h4 : 4 * C * (1 + Real.log (2 * M)) / 4 = C * (1 + Real.log (2 * M)) := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left (by linarith) hCpos.le
    linarith

end Work.PertCrux
