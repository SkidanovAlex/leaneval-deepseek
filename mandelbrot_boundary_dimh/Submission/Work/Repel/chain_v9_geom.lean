import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.boxes_v3

/-! # `Work.Repel.chain_v9_geom` : elementary geometry of the §6 cells

Helper lemmas for `Work.Repel.chain_returns_v9`.  All statements here are elementary consequences
of the `PertData` field `φ_star_close` (`‖τ₀ (φ w) - w‖ ≤ η/40` on `Dsm η ∪ Dsm (-η)`).
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- A point of `Dsm η` with `0 < η` has modulus in `[3η/4, 5η/4]`. -/
lemma norm_bounds_of_mem_Dsm {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : w ∈ Dsm η) :
    3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
  have h := hw
  rw [Dsm, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hη] at h
  have h1 : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have h2 : |‖w‖ - η| ≤ η / 4 := by
    have h3 : |‖w‖ - ‖Complex.I * (η : ℂ)‖| ≤ ‖w - Complex.I * (η : ℂ)‖ := abs_norm_sub_norm_le _ _
    rw [h1] at h3
    linarith
  rw [abs_le] at h2
  exact ⟨by linarith, by linarith⟩

/-- `Dsm (-η)` has the same modulus bounds as `Dsm η`. -/
lemma norm_bounds_of_mem_Dsm_neg {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : w ∈ Dsm (-η)) :
    3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
  have h := hw
  rw [Dsm, Metric.mem_closedBall, dist_eq_norm, abs_neg, abs_of_pos hη] at h
  have h1 : ‖Complex.I * ((-η : ℝ) : ℂ)‖ = η := by
    rw [norm_mul, Complex.norm_I, one_mul]
    rw [show ((-η : ℝ) : ℂ) = -((η : ℝ) : ℂ) by push_cast; ring]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have h2 : |‖w‖ - η| ≤ η / 4 := by
    have h3 : |‖w‖ - ‖Complex.I * ((-η : ℝ) : ℂ)‖| ≤ ‖w - Complex.I * ((-η : ℝ) : ℂ)‖ :=
      abs_norm_sub_norm_le _ _
    rw [h1] at h3
    linarith
  rw [abs_le] at h2
  exact ⟨by linarith, by linarith⟩

/-- **The level-`η` Fatou coordinate is comparable to `-1/w` on `Dsm ±η`.**
`40/(51η) ≤ ‖φ w‖ ≤ 40/(29η)` for `w ∈ Dsm η ∪ Dsm (-η)`, `η > 0`. -/
theorem phi_norm_bounds {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : ParabData f₀ D₀} {f : ℂ → ℂ} {Df : Set ℂ}
    {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ} (P : PertData d f Df η y₁ K K' δ) (hη : 0 < η)
    {w : ℂ} (hw : w ∈ Dsm η ∪ Dsm (-η)) :
    40 / (51 * η) ≤ ‖P.φ w‖ ∧ ‖P.φ w‖ ≤ 40 / (29 * η) := by
  have hcl0 := P.φ_star_close w hw
  -- `‖τ₀ (φ w)‖` is within `η/40` of `‖w‖`
  have hcl := P.φ_star_close w hw
  rw [abs_of_pos hη] at hcl
  have hn : |‖MandelDim.tau0 (P.φ w)‖ - ‖w‖| ≤ η / 40 := by
    have h3 : |‖MandelDim.tau0 (P.φ w)‖ - ‖w‖| ≤ ‖MandelDim.tau0 (P.φ w) - w‖ :=
      abs_norm_sub_norm_le _ _
    linarith
  rw [abs_le] at hn
  obtain ⟨hlo, hhi⟩ : 3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
    rcases hw with h | h
    · exact norm_bounds_of_mem_Dsm hη h
    · exact norm_bounds_of_mem_Dsm_neg hη h
  have ht : ‖MandelDim.tau0 (P.φ w)‖ = 1 / ‖P.φ w‖ := by
    simp only [MandelDim.tau0]
    rw [norm_div, norm_neg, norm_one]
  rw [ht] at hn
  have hpos : 0 < ‖P.φ w‖ := by
    by_contra h0
    have h0' : ‖P.φ w‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [h0', div_zero] at hn
    linarith [hn.1, hlo]
  have h1 : (1 : ℝ) / ‖P.φ w‖ ≤ 51 * η / 40 := by linarith [hn.2, hhi]
  have h2 : (29 * η) / 40 ≤ 1 / ‖P.φ w‖ := by linarith [hn.1, hlo]
  constructor
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 51 * η)]
    have h := (div_le_iff₀ hpos).mp h1
    nlinarith [h]
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 29 * η)]
    have h := (le_div_iff₀ hpos).mp h2
    nlinarith [h]

/-- `Dsm η` and `Dsm (-η)` are contained in the domain of `φ`. -/
lemma Dsm_subset_Dφ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : ParabData f₀ D₀} {f : ℂ → ℂ} {Df : Set ℂ}
    {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ} (P : PertData d f Df η y₁ K K' δ) :
    Dsm η ∪ Dsm (-η) ⊆ P.Dφ := P.D_sub

/-- The level-0 counting disc `Dflat η` sits inside `Dsm η`. -/
lemma Dflat_subset_Dsm (η : ℝ) : Dflat η ⊆ Dsm η := by
  unfold Dflat Dsm
  exact Metric.closedBall_subset_closedBall (by nlinarith [abs_nonneg η])

/-- `π w = exp (2π i w)` is injective on every ball of radius `≤ 1/2`. -/
theorem piExp_injOn_ball {c : ℂ} {r : ℝ} (hr : r ≤ 1 / 2) :
    Set.InjOn MandelDim.piExp (Metric.ball c r) := by
  intro a ha b hb hab
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hab
  have h1 : dist a b < 1 := by
    have h2 : dist a b ≤ dist a c + dist c b := dist_triangle _ _ _
    rw [Metric.mem_ball] at ha hb
    rw [dist_comm b c] at hb
    linarith
  have hk2 : a - b = ((k : ℤ) : ℂ) := by rw [hk]; ring
  have hnorm : dist a b = |((k : ℤ) : ℝ)| := by
    rw [dist_eq_norm, hk2]
    rw [show ((k : ℤ) : ℂ) = (((k : ℤ) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hk0 : k = 0 := by
    have h2 : |((k : ℤ) : ℝ)| < 1 := by rw [← hnorm]; exact h1
    have h2' : -1 < ((k : ℤ) : ℝ) ∧ ((k : ℤ) : ℝ) < 1 := abs_lt.mp h2
    have h3 : ¬ ((1 : ℤ) ≤ k) := by
      intro hge
      have : (1 : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hge
      linarith [h2'.2]
    have h4 : ¬ (k ≤ -1) := by
      intro hle
      have : ((k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hle
      linarith [h2'.1]
    omega
  rw [hk0] at hk
  simpa using hk

end

end Work.Repel
