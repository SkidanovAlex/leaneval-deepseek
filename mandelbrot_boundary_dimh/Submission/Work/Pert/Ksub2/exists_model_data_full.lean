import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ

/-!
# Model data for a parabolic germ (`exists_model_data_full`)

Given a parabolic germ `f₀ z = z + z² + O(z³)` (Shishikura's normalised cusp germ, encoded by
`MandelDim.IsParabolicGerm f₀ D₀`), produce a radius `ρ ≤ 1/8`, a Lipschitz constant `D ≥ 0` and
a holomorphic function `hF` on `ball 0 ρ` with

* `hF 0 = 1` and `f₀ z = z + z² hF z` for `z ∈ ball 0 ρ`,
* `‖hF z‖ ≤ 3/2` and `‖deriv hF z‖ ≤ D` for `z ∈ ball 0 ρ`,
* `closedBall 0 ρ ⊆ D₀`.

This is the `(ρ, D, hF)` model datum consumed by the perturbative layer (`Ksub`, `Ksub2`).
The existence of `hF` with the qualitative properties (including the **2**-bound) is
`Work.FatouCoord.Petal.exists_parabolic_germ_bounds`; the only extra content here is shrinking the
ball so that the sharper bound `3/2` holds, which is available by continuity at `0` since `hF 0 = 1`.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Pert.Ksub2

theorem exists_model_data_full {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ (hF : ℂ → ℂ) (ρ D : ℝ), 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 0 ≤ D ∧ hF 0 = 1 ∧
      Metric.closedBall (0 : ℂ) ρ ⊆ D₀ ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF z) ∧
      DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) ρ) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv hF z‖ ≤ D) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖hF z‖ ≤ 3 / 2) := by
  obtain ⟨hDopen, h0D, hdiff, hf0, hd1, hd2⟩ := hd
  -- a ball around `0` contained in `D₀`
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds h0D)
  have hfan : AnalyticAt ℂ f₀ 0 := hdiff.analyticAt (hDopen.mem_nhds h0D)
  have hd1' : iteratedDeriv 1 f₀ 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hd2' : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd2
  obtain ⟨hF, r', A'', A''', hr', hA'', hA''', hFeq, hFdiff, hFclose, hFbound, hFderiv⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := iteratedDeriv 3 f₀ 0 / 6)
      hfan hf0 hd1' hd2' (by ring)
  -- the normalisation `hF 0 = 1`
  have hF0 : hF 0 = 1 := by
    have hc := hFclose 0 (mem_ball_self hr')
    simp only [mul_zero, sub_zero, norm_zero, pow_two] at hc
    have h0 : hF 0 - 1 = 0 := norm_eq_zero.mp (le_antisymm hc (norm_nonneg _))
    exact sub_eq_zero.mp h0
  -- continuity at `0` gives a ball on which `‖hF‖ ≤ 3/2`
  have hcont : ContinuousAt hF 0 :=
    ((hFdiff.continuousOn 0 (mem_ball_self hr')).continuousAt (Metric.ball_mem_nhds 0 hr'))
  have hle : ∀ᶠ z in 𝓝 (0 : ℂ), ‖hF z‖ ≤ 3 / 2 := by
    have htend : Tendsto hF (𝓝 0) (𝓝 1) := by
      have h := hcont.tendsto
      rwa [hF0] at h
    have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), dist (hF z) 1 < 1 / 2 :=
      (Metric.tendsto_nhds.mp htend) (1 / 2) (by norm_num)
    filter_upwards [h1] with z hz
    have hz' : ‖hF z - 1‖ < 1 / 2 := by rwa [dist_eq_norm] at hz
    have hb1 : ‖hF z‖ ≤ ‖hF z - 1‖ + 1 := by
      have h := norm_add_le (hF z - 1) (1 : ℂ)
      rwa [show (hF z - 1) + 1 = hF z from by ring, norm_one] at h
    linarith
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hle
  -- the final radius
  set R : ℝ := min (r' / 2) (min (ρ' / 2) (ρ₀ / 2)) with hRdef
  set ρ : ℝ := min R (1 / 8) with hρdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρpos : 0 < ρ := lt_min hRpos (by norm_num)
  have hρle : ρ ≤ 1 / 8 := min_le_right _ _
  have hρR : ρ ≤ R := min_le_left _ _
  have hRr' : R < r' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRρ' : R < ρ' :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hRρ₀ : R < ρ₀ :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  have hρr' : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) r' :=
    ball_subset_ball (le_of_lt (lt_of_le_of_lt hρR hRr'))
  have hρρ' : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) ρ' :=
    ball_subset_ball (le_of_lt (lt_of_le_of_lt hρR hRρ'))
  have hρρ₀ : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) ρ₀ :=
    closedBall_subset_ball (lt_of_le_of_lt hρR hRρ₀)
  exact ⟨hF, ρ, A''', hρpos, hρle, hA''', hF0, fun z hz => hρ₀sub (hρρ₀ hz),
    fun z hz => hFeq z (hρr' hz), hFdiff.mono hρr', fun z hz => hFderiv z (hρr' hz),
    fun z hz => hρ'sub (hρρ' hz)⟩

end Work.Pert.Ksub2
