import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.EuDefs
import Submission.Work.Pert.EuBasicBounds
import Submission.Work.Pert.EuCenterBounds
import Submission.Work.Pert.EuDecomp
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp

/-!
# PERT · `Work.Pert.EuDevBounds`

Shishikura (4.2.5), the deviation bounds for the composite chart `E_u = τ₀ ∘ τ_f - id`.

Under `1 - σ u₀ = e^{2πiα}`, `‖u₀ - 1‖ ≤ 1/1024`, `2π‖α‖η ≤ 1/64`, `η ≥ 100`, the deviation
`E_u ζ = τ₀(τ_f ζ) - ζ = (e^{-sζ} - 1)/σ - ζ` (with `s = 2πiα`) is nearly constant on the two
discs `closedBall (±iη) (13η/40)`, and its values at the two centres are nearly equal
(cross) and nearly opposite (sum).  With `ψ = (e^s-1)/s` and `t = -s·iη = 2παη`:

* `E_u ζ - E_u (iη) = (ζ - iη)·(u₀e^{t}/ψ - 1) + u₀e^{t}·(e^{-s(ζ-iη)} - 1 + s(ζ-iη))/(1-e^s)`;
* `E_u (iη) - E_u (-iη) = 2iη·(u₀ sinh t/(tψ) - 1)`,   `E_u (iη) + E_u (-iη) = 2(cosh t - 1)/σ`.

The bricks used are `Work.Pert.EuDecomp` (the identities), `Work.Pert.EuBasicBounds` (the
elementary size bounds) and `Work.Pert.EuCenterBounds` (the two centre clauses).
-/

namespace Work.Pert

open Complex MandelDim

noncomputable section

/-- Estimate on one of the two discs: given the exact decomposition of
`E_u ζ - E_u c` in terms of the shift `w = ζ - c` and the two size bounds for `g = e^{±t}`,
the oscillation is at most `η/148`. -/
private theorem Eu_ball_le {σ α u₀ : ℂ} {η : ℝ} {ζ c w g : ℂ} (hη : 0 < η)
    (hw : ζ - c = w)
    (hr : ‖w‖ ≤ 13 * η / 40)
    (hb : ‖u₀ * g / euPsi α - 1‖ ≤ 171 / 10000)
    (hc : ‖u₀ * g / (1 - Complex.exp (euS α))‖ * ‖euS α‖ ≤ 103 / 100)
    (hX : ‖euS α‖ * η ≤ 1 / 64)
    (hdec : Eu σ α ζ - Eu σ α c
      = w * (u₀ * g / euPsi α - 1)
        + u₀ * g * (Complex.exp (-(euS α * w)) - 1 + euS α * w)
          / (1 - Complex.exp (euS α))) :
    ‖Eu σ α ζ - Eu σ α c‖ ≤ η / 148 := by
  subst hw
  rw [hdec]
  have hX0 : (0:ℝ) ≤ ‖euS α‖ := norm_nonneg _
  have hr0 : (0:ℝ) ≤ 13 * η / 40 := by positivity
  have hXR : ‖euS α‖ * ‖ζ - c‖ ≤ 13/2560 := by
    have h1 : ‖euS α‖ * ‖ζ - c‖ ≤ ‖euS α‖ * (13*η/40) :=
      mul_le_mul_of_nonneg_left hr hX0
    have h2 : ‖euS α‖ * (13*η/40) = (13/40) * (‖euS α‖ * η) := by ring
    have h3 : (13/40 : ℝ) * (‖euS α‖ * η) ≤ 13/2560 := by nlinarith [hX]
    linarith [h1, h2 ▸ h3]
  have hE1 : ‖Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c)‖
      ≤ 29/48 * (‖euS α‖ * ‖ζ - c‖)^2 := by
    have hs : ‖-(euS α * (ζ - c))‖ ≤ 1/2 := by
      rw [norm_neg, norm_mul]; linarith [hXR]
    have h := norm_exp_sub_one_sub_id_le_sharp (z := -(euS α * (ζ - c))) hs
    have h' : Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c)
        = Complex.exp (-(euS α * (ζ - c))) - 1 - (-(euS α * (ζ - c))) := by ring
    rw [h']
    calc ‖Complex.exp (-(euS α * (ζ - c))) - 1 - (-(euS α * (ζ - c)))‖
        ≤ 29/48 * ‖-(euS α * (ζ - c))‖^2 := h
      _ = 29/48 * (‖euS α‖ * ‖ζ - c‖)^2 := by rw [norm_neg, norm_mul]
  have hterm1 : ‖(ζ - c) * (u₀ * g / euPsi α - 1)‖ ≤ (13*η/40) * (171/10000) := by
    rw [norm_mul]
    exact mul_le_mul hr hb (norm_nonneg _) hr0
  have hterm2 : ‖u₀ * g * (Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c))
      / (1 - Complex.exp (euS α))‖ ≤ (29/48)*(103/100)*(13/2560)*(13*η/40) := by
    have hsplit : u₀ * g * (Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c))
        / (1 - Complex.exp (euS α))
        = (u₀ * g / (1 - Complex.exp (euS α)))
          * (Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c)) := by ring
    rw [hsplit, norm_mul]
    calc ‖u₀ * g / (1 - Complex.exp (euS α))‖
          * ‖Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c)‖
        ≤ ‖u₀ * g / (1 - Complex.exp (euS α))‖
          * (29/48 * (‖euS α‖ * ‖ζ - c‖)^2) :=
          mul_le_mul_of_nonneg_left hE1 (norm_nonneg _)
      _ = (29/48) * ((‖u₀ * g / (1 - Complex.exp (euS α))‖ * ‖euS α‖)
            * (‖ζ - c‖ * (‖euS α‖ * ‖ζ - c‖))) := by ring
      _ ≤ (29/48) * ((103/100) * ((13*η/40) * (13/2560))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hc (mul_le_mul hr hXR (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr0)
            (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num)
      _ = (29/48)*(103/100)*(13/2560)*(13*η/40) := by ring
  calc ‖(ζ - c) * (u₀ * g / euPsi α - 1)
        + u₀ * g * (Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c))
          / (1 - Complex.exp (euS α))‖
      ≤ ‖(ζ - c) * (u₀ * g / euPsi α - 1)‖
        + ‖u₀ * g * (Complex.exp (-(euS α * (ζ - c))) - 1 + euS α * (ζ - c))
          / (1 - Complex.exp (euS α))‖ := norm_add_le _ _
    _ ≤ (13*η/40) * (171/10000) + (29/48)*(103/100)*(13/2560)*(13*η/40) :=
        add_le_add hterm1 hterm2
    _ ≤ η/148 := by
        have hc2 : (13/40 : ℝ) * (171/10000) + (29/48)*(103/100)*(13/2560)*(13/40) ≤ 1/148 := by
          norm_num
        have he : (13*η/40) * (171/10000) + (29/48)*(103/100)*(13/2560)*(13*η/40)
            = ((13/40)*(171/10000) + (29/48)*(103/100)*(13/2560)*(13/40)) * η := by ring
        rw [he, show η/148 = (1/148)*η by ring]
        exact mul_le_mul_of_nonneg_right hc2 (le_of_lt hη)

theorem EuDevBounds {σ α u₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hη100 : 100 ≤ η) (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hu₀ : ‖u₀ - 1‖ ≤ 1 / 1024)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    (heq : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    (∀ ζ ∈ Metric.closedBall (Complex.I * (η : ℂ)) (13 * η / 40),
      ‖(MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ)
        - (MandelDim.tau0 (Work.Pert.tauC σ α (Complex.I * (η : ℂ))) - Complex.I * (η : ℂ))‖
          ≤ η / 148)
    ∧ (∀ ζ ∈ Metric.closedBall (-(Complex.I * (η : ℂ))) (13 * η / 40),
      ‖(MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ)
        - (MandelDim.tau0 (Work.Pert.tauC σ α (-(Complex.I * (η : ℂ)))) - (-(Complex.I * (η : ℂ))))‖
          ≤ η / 148)
    ∧ ‖(MandelDim.tau0 (Work.Pert.tauC σ α (Complex.I * (η : ℂ))) - Complex.I * (η : ℂ))
        - (MandelDim.tau0 (Work.Pert.tauC σ α (-(Complex.I * (η : ℂ)))) - (-(Complex.I * (η : ℂ))))‖
          ≤ η / 450
    ∧ ‖(MandelDim.tau0 (Work.Pert.tauC σ α (Complex.I * (η : ℂ))) - Complex.I * (η : ℂ))
        + (MandelDim.tau0 (Work.Pert.tauC σ α (-(Complex.I * (η : ℂ)))) - (-(Complex.I * (η : ℂ))))‖
          ≤ η / 60 := by
  have hu₀nz : u₀ ≠ 0 := by
    intro h
    rw [h] at hu₀
    norm_num at hu₀
  obtain ⟨hsη, -, -, -, -, hb1, hb2, hc1, hc2⟩ :=
    EuBasicBounds hη hη100 hσ hα hu₀ hαη heq
  obtain ⟨hdec1, hdec2, -, -⟩ := EuDecomp hσ hα hu₀nz heq
  obtain ⟨hctr1, hctr2⟩ := EuCenterBounds hη hη100 hσ hα hu₀ hαη heq
  refine ⟨?_, ?_, hctr1, hctr2⟩
  · intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    exact Eu_ball_le (c := Complex.I * (η:ℂ)) (w := ζ - Complex.I * (η:ℂ))
      (g := Complex.exp (euT α η)) hη rfl hζ hb1 hc1 hsη (hdec1 ζ)
  · intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    have hζ' : ‖ζ + Complex.I * (η:ℂ)‖ ≤ 13 * η / 40 := by
      simpa using hζ
    exact Eu_ball_le (c := -(Complex.I * (η:ℂ))) (w := ζ + Complex.I * (η:ℂ))
      (g := Complex.exp (-(euT α η))) hη (by ring) hζ' hb2 hc2 hsη (hdec2 ζ)


end

end Work.Pert
