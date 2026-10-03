import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_scale_L1
import Submission.Work.Interfaces.FatouNarrow

namespace Work.Pert.LiftNTL2

open MandelDim

/-!
# PERT · `Work.Pert.LiftNTL2.liftF_nearTranslationL1`

Assembly of the `L¹` near-translation property of the perturbed lift `F_f = liftF u σ α` on the two
gate regions of Shishikura §4.2, in the *scale-free* form used by the requester: for every radius
`rr > 0` there are thresholds `Ξmin, εmin > 0` such that whenever the perturbation data
`(u, σ, α)` are small (`‖σ‖, ‖α‖ ≤ εmin`, `1 - σ u 0 = exp (2πiα)`, `α ∈ 𝓕₁`) and holomorphic-
nonvanishing on `ball 0 rr`, the lift is a near-translation *with integrable derivative defect* on
`Qm Ξ α` and `Qp Ξ α` for **every** `Ξ ≥ Ξmin`.

The mathematical content is entirely in `Work.Pert.gate_scale_L1` (Shishikura (A.1.7)(ii) with the
scale-dependent gate `ξ₁ = 10^12/min ρmin 1`): it produces the thresholds for the radius `rr`, and
the statement for a larger gate `Ξ ≥ ξ₁` follows from the monotonicity of `NearTranslationL1` in the
region (`Qm`/`Qp` shrink as `Ξ` grows).
-/

/-- `NearTranslationL1` is monotone in the region: a near-translation with integrable derivative
defect on a larger region is one on any smaller region. -/
theorem NearTranslationL1_mono {F : ℂ → ℂ} {Q Q' : Set ℂ}
    (h : MandelDim.NearTranslationL1 F Q') (hsub : Q ⊆ Q') :
    MandelDim.NearTranslationL1 F Q :=
  ⟨NearTranslationOn_mono h.1 hsub, fun x hx => h.2 x (fun y => hsub (hx y))⟩

theorem liftF_nearTranslationL1 (rr : ℝ) (hrr : 0 < rr) :
    ∃ Ξmin εmin : ℝ, 0 < Ξmin ∧ 0 < εmin ∧
      ∀ {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ}, Ξmin ≤ Ξ →
        MandelDim.InF1 α → α ≠ 0 → ‖σ‖ ≤ εmin → ‖α‖ ≤ εmin →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) ∧
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ α) := by
  obtain ⟨ξ₁, ε₀, hξ₁, hε₀, hgate⟩ := gate_scale_L1 rr hrr
  refine ⟨ξ₁, ε₀, hξ₁, hε₀, ?_⟩
  intro u σ α Ξ hΞ hInF1 hαne hσ hα hu hub hnorm
  have hmain := hgate (le_refl rr) hu hub hnorm hσ hα hαne hInF1
  exact ⟨NearTranslationL1_mono hmain.1 (Qm_subset_of_le hΞ),
    NearTranslationL1_mono hmain.2 (Qp_subset_of_le hΞ)⟩

end Work.Pert.LiftNTL2
