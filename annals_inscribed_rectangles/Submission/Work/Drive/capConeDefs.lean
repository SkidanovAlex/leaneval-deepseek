import Mathlib
import Submission.Work.Drive.cappedPlaneCharts

/-!
# The cone chart of the cap disk of the capping space, clamped into `[0,1]`

The cap half of Hugelmeyer's capping (`Submission/Work/Drive/CAPPING_ANALYSIS.md`) presents the cap
solid torus's disk of caps as the cone

> `(s,t) ↦ ((1-s) r₀ + s ρ t, Θ 0 + s (Θ t - Θ 0) + u, s · circleOf (Ψ t))`

(`Work.Drive.capConePt`) over the square `[0,1] × S¹` (cone parameter, curve parameter).  The chain
route needs this cone as a **smooth** chart of `Work.Drive.CappingSpace`.

The reason the chart has to be *clamped* is that the side conditions of the cap piece
(`0 < r`, `‖d‖ ≤ 1`) hold only for `s ∈ [0,1]`: for a globally defined (hence globally smooth) map
into the cap piece one needs the cone parameter to lie in `[0,1]` **everywhere**.  A smooth clamp
`σ : ℝ → [0,1]` cannot be the identity on all of `[0,1]` (at `s = 1` one would need `σ'(1) = 1` with
`σ ≤ 1`), but `Work.Drive.capConeClamp s = max 0 (min s 1)` *is* the identity on `[0,1]` — it is only
Lipschitz there, and the chart below is therefore smooth **on the set where the clamp is the identity**
(`{p | 0 ≤ p 0 ∧ p 0 ≤ 1}`), which is exactly the statement the chain machinery consumes.

This file contains only the definitions and their elementary properties; the smoothness statement is
`Work.Drive.contMDiffOn_capConeChart`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff
open Classical

noncomputable section

/-- The clamp of the cone parameter into `[0,1]`: `s ↦ max 0 (min s 1)`.  It is the identity on
`[0,1]` and every value lies in `[0,1]` (it is not smooth at `0` and `1`). -/
def capConeClamp (s : ℝ) : ℝ := max 0 (min s 1)

/-- The clamped cone parameter always lies in `[0,1]`. -/
lemma capConeClamp_mem (s : ℝ) : capConeClamp s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right s 1)⟩

/-- On `[0,1]` the clamp is the identity. -/
lemma capConeClamp_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : capConeClamp s = s := by
  rw [capConeClamp, min_eq_left hs.2, max_eq_right hs.1]

/-- The clamped cone parameter is `≤ 1`; in particular `‖s • circleOf φ‖ ≤ 1` for it. -/
lemma capConeClamp_le_one (s : ℝ) : capConeClamp s ≤ 1 := (capConeClamp_mem s).2

lemma capConeClamp_nonneg (s : ℝ) : 0 ≤ capConeClamp s := (capConeClamp_mem s).1

/-- **The cone chart of the cap disk, clamped.**  At the parameter `p = (s,t)` this is the class in
`CappingSpace` of the cap cone point with cone parameter `capConeClamp (p 0)` and curve parameter
`p 1`.  It is globally defined (the clamp keeps the cone parameter in `[0,1]`, so the side conditions
of the cap piece hold everywhere) and agrees with the honest cone `Work.Drive.capConePt` whenever
`0 ≤ p 0 ≤ 1`. -/
def capConeChart (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (hr₀ : 0 < r₀)
    (hρpos : ∀ t : ℝ, 0 < ρ t) (p : EuclideanSpace ℝ (Fin 2)) : CappingSpace :=
  Quotient.mk'' (Sum.inr (⟨capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1),
    capConePt_pos hr₀ hρpos Ψ Θ u (capConeClamp_mem (p 0)),
    capConePt_thd_norm_le_one r₀ ρ Ψ Θ u (capConeClamp_mem (p 0))⟩ : CapPiece))

/-- **The clamped cone chart is the honest cone chart on `{0 ≤ s ≤ 1}`.** -/
lemma capConeChart_eq_of_mem (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (hr₀ : 0 < r₀)
    (hρpos : ∀ t : ℝ, 0 < ρ t) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p 0 ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 0 < (capConePt r₀ ρ Ψ Θ u (p 0) (p 1)).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u (p 0) (p 1)).2.2‖ ≤ 1) :
    capConeChart r₀ ρ Ψ Θ u hr₀ hρpos p
      = Quotient.mk'' (Sum.inr (⟨capConePt r₀ ρ Ψ Θ u (p 0) (p 1), h1, h2⟩ : CapPiece)) := by
  refine Quotient.sound (Or.inl (congrArg Sum.inr (Subtype.ext ?_)))
  simp only [capConeChart, capConeClamp_of_mem hp]

/-- The cone chart lies in the cap piece with cone parameter in `[0,1]`, so it is also the class of a
`Work.Drive.capPtClass` (`cappedPlaneCharts.lean`). -/
lemma capConeChart_eq_capPtClass (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (hr₀ : 0 < r₀)
    (hρpos : ∀ t : ℝ, 0 < ρ t) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p 0 ∈ Set.Icc (0 : ℝ) 1) :
    capConeChart r₀ ρ Ψ Θ u hr₀ hρpos p
      = capPtClass r₀ ρ Ψ Θ u (p 0) (p 1)
          (capConePt_pos hr₀ hρpos Ψ Θ u hp)
          (capConePt_thd_norm_le_one r₀ ρ Ψ Θ u hp) :=
  capConeChart_eq_of_mem r₀ ρ Ψ Θ u hr₀ hρpos hp
    (capConePt_pos hr₀ hρpos Ψ Θ u hp)
    (capConePt_thd_norm_le_one r₀ ρ Ψ Θ u hp)

end

end Work.Drive
