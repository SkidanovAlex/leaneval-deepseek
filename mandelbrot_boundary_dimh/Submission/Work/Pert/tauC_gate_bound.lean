import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.scale_tau

/-!
# PERT · `Work.Pert.tauC_gate_bound`

Shishikura (A.1.7)(ii), the `τ`-bound on the lower gate `Qm ξ α`: for a perturbation with normal
form data `(σ, α)` and `‖σ‖ ≤ 8π‖α‖`, `‖α‖ ξ ≤ 1`,

  `∀ ζ ∈ Qm ξ α, ‖τ_f ζ‖ ≤ 16π/ξ`.

`Qm ξ α = Qreg (ξ - 1/α) (-ξ)` keeps distance `≥ ξ/2` from the lattice `ℤ/α`
(`Work.Pert.scale_lattice`), and `Work.Pert.scale_tau` (the `ρmin`-parameterised `τ`-bound)
converts that distance into the bound `16π ρmin/10^6`.  The statement here is exactly the
instance `ρmin = 10^6/ξ` of that lemma, i.e. the constant `ξ₁ = 10^6` of the paper is replaced by
the *arbitrary* gate parameter `ξ` with the reciprocal normalisation `‖α‖ ξ ≤ 1`.
-/

namespace Work.Pert

theorem tauC_gate_bound {α σ : ℂ} {ξ : ℝ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α)
    (hσs : ‖σ‖ ≤ 8 * Real.pi * ‖α‖) (hsmall : ‖α‖ * ξ ≤ 1) :
    ∀ ζ ∈ Work.Pert.Qm ξ α, ‖Work.Pert.tauC σ α ζ‖ ≤ 16 * Real.pi / ξ := by
  -- `InF1` gives `α ≠ 0`
  have hαre : 0 < α.re := by
    have h := hα
    simp only [MandelDim.InF1] at h
    have h2 := abs_nonneg α.im
    linarith
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hαre
    simp at hαre
  intro ζ hζ
  -- `ζ` lies in the lower gate, i.e. at distance `≥ ξ/2` from `ℤ/α`
  have hζ' : ζ ∈ MandelDim.Qreg (some ((ξ : ℂ) - 1 / α)) (some (-(ξ : ℂ))) := hζ
  have hlat : ∀ k : ℤ, ((10 : ℝ) ^ 6 / ((10 : ℝ) ^ 6 / ξ)) / 2 ≤ ‖ζ - (k : ℂ) / α‖ := by
    intro k
    have h := (scale_lattice hξ hα).2 hζ' k
    have heq : ((10 : ℝ) ^ 6 / ((10 : ℝ) ^ 6 / ξ)) / 2 = ξ / 2 := by field_simp
    rw [heq]
    exact h
  -- `‖α‖ ξ ≤ 1` is the smallness hypothesis of `scale_tau` at `ρmin = 10^6/ξ`
  have hαs : ‖α‖ ≤ ((10 : ℝ) ^ 6 / ξ) / (10 : ℝ) ^ 6 := by
    have h1 : ‖α‖ ≤ 1 / ξ := (le_div_iff₀ hξ).mpr hsmall
    have heq : ((10 : ℝ) ^ 6 / ξ) / (10 : ℝ) ^ 6 = 1 / ξ := by field_simp
    rw [heq]
    exact h1
  have hmain := (scale_tau (σ := σ) (α := α) (ρmin := (10 : ℝ) ^ 6 / ξ) (w := ζ)
    (by positivity) hσs hαs hαne hα hlat).2
  have heq : 16 * Real.pi * ((10 : ℝ) ^ 6 / ξ) / (10 : ℝ) ^ 6 = 16 * Real.pi / ξ := by
    field_simp
  rwa [heq] at hmain

end Work.Pert
