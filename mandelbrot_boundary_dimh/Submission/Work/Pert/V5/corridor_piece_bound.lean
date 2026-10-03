import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.horiz_dev_le_clear

namespace Work.Pert.V5

theorem corridor_piece_bound {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s x y : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hxy : x ≤ y) (hlen : y - x ≤ 16 * (M + 2 + Ξ))
    (hgate : ∀ ξ ∈ Set.Icc x y, ((ξ : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α)
    (hclear : ∀ ξ ∈ Set.Icc x y, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖)
    (hlo : ∀ ξ ∈ Set.Icc x y,
      Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
                              (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I)))
    (hpos : ∀ ξ ∈ Set.Icc x y,
      1 ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
              (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I))) :
    ‖(Φm ((y : ℂ) + (s : ℂ) * Complex.I) - ((y : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((x : ℂ) + (s : ℂ) * Complex.I) - ((x : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
  -- The two endpoints of the piece lie in the gate (`hgate` on the closed interval).
  have ha : ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := hgate x ⟨le_rfl, hxy⟩
  have hb : ((y : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := hgate y ⟨hxy, le_rfl⟩
  -- The cleared horizontal deviation bound, whose logarithmic slot carries the *actual* length.
  have hbase := horiz_dev_le_clear (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (s := s) (a := x) (b := y)
    hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE hNT hΦm ha hb hxy hlen hclear hlo hpos
  -- The length is `≤ 16 (M + 2 + Ξ)`, so its logarithm is dominated by the stated one.
  have hlog : Real.log (2 + y - x) ≤ Real.log (2 + 16 * (M + 2 + Ξ)) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have hstep : 1 + Real.log (2 + y - x) ≤ 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by
    linarith
  have h2 : 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + y - x))
      ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  linarith [hbase, h2]

end Work.Pert.V5
