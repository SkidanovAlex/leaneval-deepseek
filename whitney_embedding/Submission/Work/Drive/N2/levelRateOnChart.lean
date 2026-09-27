import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.level_mono_of_modelAdaptedFlow

/-!
# The rate of the level of the model-adapted flow along a chart-confined trace

`Work.Drive.N2.levelRateOnChart`: on the closed chart region `C i` of a `WindowDatum`, the level
`f` of the model-adapted flow rises at the *chart* rate
`2 * chartMult (ρ i / 8) (‖φ i ·‖ ^ 2) * ‖φ i ·‖ ^ 2`, which is a non-negative quantity bounded
by `1`.

The proof is the chain rule applied to the normal form `f = f (x i) + chartQ (φ i) (s₁ i) (s₂ i)`
valid on the chart source (`D.hval`), together with the chart ODE (`D.hODE`) and the two
elementary facts `chartMult ≥ 0` and `2 σ * chartMult r σ ≤ 1` (`smoothTransition ≤ 1`).
-/

namespace Work.Drive.N2

open scoped Topology
open Set

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The multiplier is at most `1/(2σ)`**: `2 σ (chartMult r σ) ≤ 1`.  Below `r ^ 2 / 2` the
multiplier vanishes; above it the multiplier is `(2σ)⁻¹` times a `smoothTransition ≤ 1`. -/
theorem two_mul_chartMult_mul_le_one (r σ : ℝ) : 2 * chartMult r σ * σ ≤ 1 := by
  by_cases hσ : σ ≤ 0
  · have h1 : 2 * σ / r ^ 2 - 1 ≤ 0 := by
      have h2 : 2 * σ / r ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg r)
      linarith
    rw [chartMult, Real.smoothTransition.zero_of_nonpos h1]
    simp
  · push Not at hσ
    have h2 : (2 * σ) ≠ 0 := by positivity
    have key : 2 * σ * (2 * σ)⁻¹ = 1 := mul_inv_cancel₀ h2
    calc 2 * chartMult r σ * σ
        = Real.smoothTransition (2 * σ / r ^ 2 - 1) := by
          rw [chartMult]
          calc 2 * (Real.smoothTransition (2 * σ / r ^ 2 - 1) * (2 * σ)⁻¹) * σ
              = Real.smoothTransition (2 * σ / r ^ 2 - 1) * (2 * σ * (2 * σ)⁻¹) := by ring
            _ = Real.smoothTransition (2 * σ / r ^ 2 - 1) * 1 := by rw [key]
            _ = Real.smoothTransition (2 * σ / r ^ 2 - 1) := by ring
      _ ≤ 1 := Real.smoothTransition.le_one _

theorem levelRateOnChart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (i : Fin D.N)
    {y : M} {t : ℝ}
    (hconf : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C i) :
    HasDerivWithinAt (fun σ : ℝ => f (D.Φ (σ, y)))
        (2 * Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2) *
          ‖D.φ i (D.Φ (t, y))‖ ^ 2)
        (Set.Icc (min 0 t) (max 0 t)) t ∧
      0 ≤ 2 * Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2) *
          ‖D.φ i (D.Φ (t, y))‖ ^ 2 ∧
      2 * Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2) *
          ‖D.φ i (D.Φ (t, y))‖ ^ 2 ≤ 1 := by
  -- the trace is continuous and lands in the (open) chart source near `t`
  have hcont : Continuous fun σ : ℝ => D.Φ (σ, y) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hsrc : D.Φ (t, y) ∈ (D.φ i).source :=
    D.hCsub i (hconf t ⟨min_le_right 0 t, le_max_right 0 t⟩)
  have hnhds : (fun σ : ℝ => D.Φ (σ, y)) ⁻¹' (D.φ i).source ∈ 𝓝 t :=
    hcont.continuousAt.preimage_mem_nhds ((D.φ i).open_source.mem_nhds hsrc)
  -- the chart ODE at `t` and the chain rule with the quadratic normal form
  obtain ⟨hd0, hd1⟩ := D.hODE i y t hconf
  have hQ := levelMono_hasDerivAt_chartQ i D.φ D.s₁ D.s₂
    (chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2)) (D.hsgn i) hd0 hd1
  have hev : (fun σ : ℝ => f (D.Φ (σ, y))) =ᶠ[𝓝 t]
      (fun σ : ℝ => f (D.x i) + chartQ (D.φ i) (D.s₁ i) (D.s₂ i) (D.Φ (σ, y))) := by
    filter_upwards [hnhds] with σ hσ
    rw [D.hval i (D.Φ (σ, y)) hσ]
  have hmain : HasDerivAt (fun σ : ℝ => f (D.Φ (σ, y)))
      (2 * chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2)
        * ‖D.φ i (D.Φ (t, y))‖ ^ 2) t := by
    have h := (hQ.const_add (f (D.x i))).congr_of_eventuallyEq hev
    rwa [norm_uVec (D.φ i (D.Φ (t, y)))] at h
  refine ⟨hmain.hasDerivWithinAt, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (chartMult_nonneg _ _)) (sq_nonneg _)
  · exact two_mul_chartMult_mul_le_one (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2)

end Work.Drive.N2
