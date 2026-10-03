import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic

/-!
# `Work.Pert.pert2v2.gate_coord_end_asymptotic` — the (A.4.1) end asymptotics of the gate
coordinates, from `MandelDim.FatouEnds`

`MandelDim.FatouEnds` (a **field of `FatouStatement`**, so available in the whole area) says: if a
near-translation `F` is *exponentially* close to `z ↦ z + ρ` at the upper end of a `Qreg`-region
`Q`, then every Fatou coordinate `Φ` on `Q` satisfies `Φ z = z/ρ + c + o(1)` there, uniformly in a
window of width `2` around any prescribed horizontal line.

With `ρ := 1` and the explicit exponential decay of `liftF u σ α` from the translation by `1`
(`Work.Pert.LiftExp.liftF_sub_translation_le_explicit` — the deviation is `O(‖tauC σ α z‖)`, and
`tauC` decays like `exp (2π Im (α z))` inside the gate) this produces, for **every** Fatou
coordinate on `Qm Ξ α` / `Qp Ξ α`,

  `∃ c, ∀ x ε > 0, ∃ Y', ∀ z ∈ Q, Y' < z.im → |z.re - x| ≤ 2 → ‖Φ z - z - c‖ < ε`,

i.e. exactly the `hEndm`/`hEndp` hypotheses of `Work.Pert.RBlock2.hornmap_end_limit`,
`Work.Pert.RBlock2.gate_T_relation_constant` and `Work.Pert.pert2v2.high_band_R_close_v2`.  Before
this file no producer of those hypotheses existed in the workspace.
-/

namespace Work.Pert.pert2v2

open MandelDim

/-- **Upper-end asymptotics of a gate coordinate, lower gate.**  Direct instantiation of
`FatouEnds` at `ρ = 1`. -/
theorem gate_coord_end_asymptotic_Qm {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hdec : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im))) :
    ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im →
      |z.re - x| ≤ 2 → ‖Φ z - z - c‖ < ε := by
  obtain ⟨M, κ, Y, hM, hκ, hdec⟩ := hdec
  have hFE := hF.2.2.2.2.2 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (Work.Pert.liftF u σ α) Φ 1 M κ Y
    hQAdm hNT.1 hΦ hκ (by norm_num)
  obtain ⟨c, hc⟩ := hFE.1 hdec
  refine ⟨c, fun x ε hε => ?_⟩
  obtain ⟨Y', hY'⟩ := hc x ε hε
  exact ⟨Y', fun z hz hzx => by simpa using hY' z hz hzx⟩

/-- **Upper-end asymptotics of a gate coordinate, upper gate.**  Same, on `Qp Ξ α`. -/
theorem gate_coord_end_asymptotic_Qp {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ))) (some (-(Ξ : ℂ) + 1 / α)))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qp Ξ α))
    (hdec : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qp Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im))) :
    ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qp Ξ α, Y' < z.im →
      |z.re - x| ≤ 2 → ‖Φ z - z - c‖ < ε := by
  obtain ⟨M, κ, Y, hM, hκ, hdec⟩ := hdec
  have hFE := hF.2.2.2.2.2 (some ((Ξ : ℂ))) (some (-(Ξ : ℂ) + 1 / α)) (Work.Pert.liftF u σ α) Φ 1 M κ Y
    hQAdm hNT.1 hΦ hκ (by norm_num)
  obtain ⟨c, hc⟩ := hFE.1 hdec
  refine ⟨c, fun x ε hε => ?_⟩
  obtain ⟨Y', hY'⟩ := hc x ε hε
  exact ⟨Y', fun z hz hzx => by simpa using hY' z hz hzx⟩

end Work.Pert.pert2v2
