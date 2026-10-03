import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Phi_dev_le_on_gate_upper
import Submission.Work.Pert.Phi_dev_le_on_gate_lower
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.deriv_Phi_close_on_gate
import Submission.Work.Pert.V5.Geom
import Submission.Work.Pert.V5.horiz_dev_le
import Submission.Work.Pert.V5.Assembly2
import Submission.Work.Pert.V5.corridor_left_wk
import Submission.Work.Pert.V5.corridor_right_wk2

/-!
## Route to this theorem (session 23)

The bound is assembled by `Work.Pert.V5.gate_lin_asm_gen`
(`Submission/Work/Pert/V5/Assembly2.lean`), which proves

  `∃ C, 0 < C ∧ C ≤ (Kp+1+C₂) 2^40 (1+Ξ+1/Ξ+1/rr) ∧
     ∀ z ∈ Qm Ξ α, band, 4 Rde ≤ |z.im| ⟹ ‖Φm z - z‖ ≤ C (1+log(2+M)) + |z.im|/8`

from the target's hypotheses **plus** the horizontal-corridor certificate `hcorr` (a subdivision of
the horizontal corridor at height `z₀.im` into `N` short pieces with margins `≥ √2 Rde`, plus a
remainder `W` paid out of the `|z.im|/8` slack and the `Kp`-slot).  The certificate is supplied by
the two delegated lemmas `Work.Pert.V5.corridor_left_wk` (case `z.re ≤ z₀.re`) and
`Work.Pert.V5.corridor_right_wk` (case `z₀.re ≤ z.re`), split by `le_total`.  The ingredients are
`pin_dev_le` (pin term), `dev_vert_band` (vertical leg at the band abscissa),
`horiz_dev_le_clear` / `horiz_dev_le_split` / `horiz_dev_le_split_right` (horizontal legs),
`band_horiz_dev_le` / `window_horiz_dev_le` (low-margin pieces),
`clear_lattice_band` / `clear_lattice_gate` (clearance).

`d : ParabData f₀ D₀` and `hEup` are not used by this route; the statement of the theorem is
unchanged.  See `Submission/Work/Pert/V5/NOTES_session23.md` for the full case analysis.
-/

namespace Work.Pert

theorem Phi_dev_gate_lin_v5 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement)
    {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hInF1 : MandelDim.InF1 α)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hEup : ∃ Mτ κ Yτ : ℝ, (0 : ℝ) < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Yτ < z.im →
      ‖Work.Pert.tauC σ α z‖ ≤ Mτ * Real.exp (-(κ * z.im)))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ))
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ (Kp + 1 + C₂) * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re → z.re ≤ -(Ξ + 2 ^ 10) →
        4 * Rde ≤ |z.im| →
          ‖Φm z - z‖ ≤ C * (1 + Real.log (2 + M)) + |z.im| / 8 := by
  refine Work.Pert.V5.gate_lin_asm_gen hF hΞ hrr hM hKp hRde hC₂
    hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm hz₀ hpin hpinbd ?_
  intro z hz hzlo hzhi ht
  rcases le_total z.re z₀.re with h | h
  · exact Work.Pert.V5.corridor_left_wk hF hΞ hrr hM hKp hRde hC₂ hInF1 hα hQAdm hσ hnorm
      hu hu2 hτQ hDE hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi ht h
  · exact Work.Pert.V5.corridor_right_wk2 hF hΞ hrr hM hKp hRde hC₂ hInF1 hα hQAdm hσ hnorm
      hu hu2 hτQ hDE hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi ht h

end Work.Pert
