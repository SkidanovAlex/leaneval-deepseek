import Mathlib
import Submission.Work.EKLC6Core.monotone_shell_bound_ae

/-!
# `thin_boundary_ae` — Pisa 7.27 (the `µ`-thin boundary of a ball)

For a finite Borel measure `μ` on a (pseudo)metric space `X`, a centre `x : X` and Lebesgue
almost every radius `r > 0` there is `c ≥ 0` with

`μ (∂_η B_r(x)) ≤ c η`  for all `η > 0`,

where the `η`-neighbourhood of the boundary of `B_r(x)` is realised as

`∂_η B_r(x) = Metric.thickening η (ball x r) ∩ Metric.thickening η ((ball x r)ᶜ)`.

(Note: in the statement below, `ᶜ` is a `postfix:1024` notation, hence
`Metric.thickening η (Metric.ball x r)ᶜ` parses as `Metric.thickening η ((Metric.ball x r)ᶜ)` —
the thickening of the *complement* of the ball, i.e. exactly the boundary layer of Pisa 7.27,
not the vacuous `A ∩ Aᶜ`.)

The proof splits into three independent pieces:

* `thickening_boundary_subset` (geometry): `∂_η B_r(x) ⊆ ball x (r+η) \ closedBall x (r-η)`;
* `thickening_boundary_measure_le` (measure arithmetic): hence
  `μ (∂_η B_r(x)) ≤ ofReal (f (r+η) - f (r-η))` with `f ρ = (μ (ball x ρ)).toReal`;
* `monotone_global_bound_ae` (analysis): for a monotone `0 ≤ f ≤ M` on `ℝ`, almost every `r`
  admits `c ≥ 0` with `f (r+η) - f (r-η) ≤ c η` for *all* `η > 0`.  The local (`η` small) part is
  `Work.EKLC6Core.monotone_shell_bound_ae` (a.e. differentiability of a monotone function);
  the global part uses only the trivial bound `f (r+η) ≤ M` and `f ≥ 0`.
-/

namespace Work.EKLC6Core

open MeasureTheory

section Geometry

variable {X : Type*} [PseudoMetricSpace X]

/-- **Geometry.**  The `η`-thickening of the boundary of `Metric.ball x r`, that is
`thickening η (ball x r) ∩ thickening η ((ball x r)ᶜ)`, lies in the annulus
`ball x (r + η) \ closedBall x (r - η)`.

The two witness points (one inside, one outside the open ball) give, by the triangle
inequality, the two strict inequalities `dist x y < r + η` and `r - η < dist x y`. -/
theorem thickening_boundary_subset (x : X) {r η : ℝ} :
    Metric.thickening η (Metric.ball x r) ∩ Metric.thickening η (Metric.ball x r)ᶜ
      ⊆ Metric.ball x (r + η) \ Metric.closedBall x (r - η) := by
  intro y hy
  rw [Set.mem_inter_iff, Metric.mem_thickening_iff, Metric.mem_thickening_iff] at hy
  obtain ⟨⟨w, hw, hyw⟩, z, hz, hyz⟩ := hy
  rw [Metric.mem_ball] at hw
  rw [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hz
  rw [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le]
  constructor
  · have h1 : dist y x ≤ dist y w + dist w x := dist_triangle y w x
    linarith
  · have h1 : dist x z ≤ dist x y + dist y z := dist_triangle x y z
    have h2 : dist z x = dist x z := dist_comm z x
    have h3 : dist y x = dist x y := dist_comm y x
    linarith

end Geometry

section MeasureBound

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Measure arithmetic.**  For a finite measure `μ` and `η > 0`,
`μ (∂_η B_r(x)) ≤ ofReal (f (r+η) - f (r-η))`, where `f ρ = (μ (ball x ρ)).toReal`. -/
theorem thickening_boundary_measure_le (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (x : X) {r η : ℝ} (hη : 0 < η) :
    μ (Metric.thickening η (Metric.ball x r) ∩ Metric.thickening η (Metric.ball x r)ᶜ)
      ≤ ENNReal.ofReal
          ((μ (Metric.ball x (r + η))).toReal - (μ (Metric.ball x (r - η))).toReal) := by
  have hsub : Metric.thickening η (Metric.ball x r) ∩ Metric.thickening η (Metric.ball x r)ᶜ
      ⊆ Metric.ball x (r + η) \ Metric.closedBall x (r - η) :=
    thickening_boundary_subset (X := X) x
  have hle : μ (Metric.ball x (r - η)) ≤ μ (Metric.ball x (r + η)) :=
    measure_mono (Metric.ball_subset_ball (by linarith))
  have hfin : μ (Metric.ball x (r + η)) - μ (Metric.ball x (r - η)) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt tsub_le_self (measure_lt_top μ _))
  calc μ (Metric.thickening η (Metric.ball x r) ∩ Metric.thickening η (Metric.ball x r)ᶜ)
      ≤ μ (Metric.ball x (r + η) \ Metric.closedBall x (r - η)) := measure_mono hsub
    _ = μ (Metric.ball x (r + η)) - μ (Metric.closedBall x (r - η)) :=
        measure_sdiff (Metric.closedBall_subset_ball (by linarith [hη]))
          (Metric.isClosed_closedBall.measurableSet.nullMeasurableSet) (measure_ne_top μ _)
    _ ≤ μ (Metric.ball x (r + η)) - μ (Metric.ball x (r - η)) :=
        tsub_le_tsub_left (measure_mono Metric.ball_subset_closedBall) _
    _ = ENNReal.ofReal
          ((μ (Metric.ball x (r + η))).toReal - (μ (Metric.ball x (r - η))).toReal) := by
        rw [← ENNReal.ofReal_toReal hfin,
          ENNReal.toReal_sub_of_le hle (measure_ne_top μ (Metric.ball x (r + η)))]

end MeasureBound

section Analysis

/-- **Analytic core.**  If `F : ℝ → ℝ` is monotone with `0 ≤ F ≤ M`, then for almost every `r`
there is `c ≥ 0` with `F (r + η) - F (r - η) ≤ c η` for **every** `η > 0`.

`Work.EKLC6Core.monotone_shell_bound_ae` (a.e. differentiability of a monotone function) gives
the bound for small `η`; for `η ≥ h₀` one uses `F (r+η) - F (r-η) ≤ F (r+η) ≤ M ≤ (M/h₀) η`. -/
theorem monotone_global_bound_ae {F : ℝ → ℝ} (hF : Monotone F) {M : ℝ}
    (h0 : ∀ ρ, 0 ≤ F ρ) (hM : ∀ ρ, F ρ ≤ M) :
    ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η → F (r + η) - F (r - η) ≤ c * η := by
  filter_upwards [monotone_shell_bound_ae F hF] with r hr
  obtain ⟨c₀, h₀, hc₀, hh₀, hbd⟩ := hr
  have hM0 : 0 ≤ M := le_trans (h0 0) (hM 0)
  refine ⟨max c₀ (M / h₀), le_trans hc₀.le (le_max_left _ _), fun η hη => ?_⟩
  rcases lt_or_ge η h₀ with hlt | hge
  · exact le_trans (hbd η hη hlt) (mul_le_mul_of_nonneg_right (le_max_left _ _) hη.le)
  · calc F (r + η) - F (r - η) ≤ F (r + η) := by linarith [h0 (r - η)]
      _ ≤ M := hM _
      _ = M / h₀ * h₀ := (div_mul_cancel₀ M hh₀.ne').symm
      _ ≤ M / h₀ * η := mul_le_mul_of_nonneg_left hge (div_nonneg hM0 hh₀.le)
      _ ≤ max c₀ (M / h₀) * η := mul_le_mul_of_nonneg_right (le_max_right _ _) hη.le

end Analysis

/-- **Pisa 7.27** (`thin_boundary_ae`).  For a finite measure `μ` on a Borel pseudo-metric
space, a centre `x` and Lebesgue-almost every radius `r > 0`, the `η`-neighbourhood of the
boundary of the ball `B_r(x)` has measure `O(η)`. -/
theorem thin_boundary_ae {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ] (x : X) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η →
        μ (Metric.thickening η (Metric.ball x r) ∩ Metric.thickening η (Metric.ball x r)ᶜ)
          ≤ ENNReal.ofReal (c * η) := by
  let F : ℝ → ℝ := fun ρ => (μ (Metric.ball x ρ)).toReal
  have hFmono : Monotone F := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top μ (Metric.ball x b))
      (measure_mono (Metric.ball_subset_ball hab))
  have hF0 : ∀ ρ, 0 ≤ F ρ := fun _ => ENNReal.toReal_nonneg
  have hFM : ∀ ρ, F ρ ≤ (μ Set.univ).toReal := fun ρ =>
    ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))
  have h := monotone_global_bound_ae hFmono hF0 hFM
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h] with r hr _
  obtain ⟨c, hc0, hcb⟩ := hr
  refine ⟨c, hc0, fun η hη => ?_⟩
  refine le_trans (thickening_boundary_measure_le μ x hη) ?_
  show ENNReal.ofReal
      ((μ (Metric.ball x (r + η))).toReal - (μ (Metric.ball x (r - η))).toReal)
        ≤ ENNReal.ofReal (c * η)
  exact ENNReal.ofReal_le_ofReal (hcb η hη)

end Work.EKLC6Core
