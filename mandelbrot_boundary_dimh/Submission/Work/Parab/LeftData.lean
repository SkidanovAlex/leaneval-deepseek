import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup

/-!
# The left (repelling) Ecalle coordinate data

`LeftCoordData f D` bundles the ζ-plane data produced by Shishikura's A.3 for a parabolic germ
`f` on `D`: a holomorphic injective coordinate `Φ ≈ id - a log(-·) - b` on an open set `L`
which contains the far left half-plane and both ends, satisfies the (conditional) Abel equation
for the chart dynamics `wMap f`, and whose image contains the far part of the sector
`QLeft ξ₁ = {|arg(w + ξ₁)| > π/3}`.

Everything downstream (the maximal domain `Dφ`, the interface's `φ = τ₀ ∘ Φ⁻¹`, the flower, the
ends) is built from this.  The fields `L_im` (both ends) and `L_left` (far left half-plane) are
exactly what the covering argument (`Work.Parab.coverCone.cover_cone`) needs; `Φ_img` is what
`Q_sub` needs.
-/

namespace Work.Parab

open Complex Set Metric Filter
open scoped Topology

noncomputable section

/-- The ζ-plane left coordinate data of `f` on `D`. -/
structure LeftCoordData (f : ℂ → ℂ) (D : Set ℂ) where
  /-- the coordinate (Shishikura's `Φ_{-,0}`) -/
  Φ : ℂ → ℂ
  /-- its domain -/
  L : Set ℂ
  /-- far left half-plane bound -/
  M₀ : ℝ
  /-- both ends bound -/
  M₁ : ℝ
  /-- sector bound -/
  ξ₁ : ℝ
  /-- logarithmic coefficient -/
  a : ℂ
  /-- constant -/
  b : ℂ
  M₀_pos : 0 < M₀
  M₁_pos : 0 < M₁
  ξ₁_pos : 0 < ξ₁
  L_open : IsOpen L
  /-- the left half-plane beyond `-M₀` is in the domain -/
  L_left : ∀ ζ : ℂ, ζ.re < -M₀ → ζ ∈ L
  /-- both ends are in the domain, within the wedge on which the asymptotic is available -/
  L_im : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L
  Φ_holo : DifferentiableOn ℂ Φ L
  /-- conditional Abel equation for the chart dynamics -/
  Φ_abel : ∀ ζ ∈ L, Work.FatouCoord.wMap f ζ ∈ L → Φ (Work.FatouCoord.wMap f ζ) = Φ ζ + 1
  Φ_inj : Set.InjOn Φ L
  /-- asymptotic `Φ ζ = ζ - a log(-ζ) - b + o(1)` -/
  Φ_asym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
    ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ < ε
  /-- the image contains the far part of the repelling sector -/
  Φ_img : ∀ w : ℂ, ξ₁ < ‖w‖ → w ∈ MandelDim.QLeft ξ₁ → ∃ ζ ∈ L, Φ ζ = w

end
end Work.Parab
