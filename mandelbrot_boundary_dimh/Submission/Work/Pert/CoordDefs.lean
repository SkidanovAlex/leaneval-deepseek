import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.CoordDefs`

Shared definitions for the `PertCoordClose` assembly (Shishikura (4.2.5)).

* `Om η` — the two discs `closedBall (±iη) (13η/40)` on which the oscillation estimates live;
* `Qc η ξ₁ α` — the "safe core" of the gate `Qm ξ₁ α`: the points whose `η/100`-neighbourhood is
  still inside `Qm ξ₁ α`.  This is the region on which `FatouDerivEstimate` can be applied
  (a ball of radius `η/100` inside the gate);
* `Eu σ α ζ = τ₀ (τ_f ζ) - ζ` — the deviation of `τ₀ ∘ τ_f` from the identity;
* `dev Ψ ζ = Ψ ζ - ζ` — the deviation of a Fatou coordinate from the identity.
-/

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

/-- The two discs about `±iη` on which the oscillation of `Eu - dev` is measured. -/
def Om (η : ℝ) : Set ℂ :=
  Metric.closedBall (Complex.I * (η : ℂ)) (13 * η / 40) ∪
    Metric.closedBall (-(Complex.I * (η : ℂ))) (13 * η / 40)

/-- The "safe core" of the gate: points of `Qm ξ₁ α` whose `η/100`-ball stays in `Qm ξ₁ α`.
This is the region on which `MandelDim.FatouDerivEstimate` (which needs a full ball inside the
domain of the coordinate) can be applied. -/
def Qc (η ξ₁ : ℝ) (α : ℂ) : Set ℂ :=
  {ζ | ζ ∈ Work.Pert.Qm ξ₁ α ∧ Metric.closedBall ζ (η / 100) ⊆ Work.Pert.Qm ξ₁ α}

/-- `E_u ζ = τ₀ (τ_f ζ) - ζ`: the deviation of the composite chart `τ₀ ∘ τ_f` from the identity. -/
def Eu (σ α : ℂ) : ℂ → ℂ := fun ζ => MandelDim.tau0 (Work.Pert.tauC σ α ζ) - ζ

/-- `D ζ = Ψ ζ - ζ`: the deviation of a Fatou coordinate from the identity. -/
def dev (Ψ : ℂ → ℂ) : ℂ → ℂ := fun ζ => Ψ ζ - ζ

/-- The polygonal path vertex used for the cross estimate: `x₀ = -η` (the optimal choice for the
logarithmic `∫|dζ|/|ζ|` length between `iη` and `-iη`). -/
def x0 (η : ℝ) : ℝ := -η

/-- The "journey" set on which the pointwise bounds for the oscillation estimate of
`dev Ψ = Ψ - id` are required: the two fattened discs `Om η`, the two vertical segments
`{Re = 0, ξ₁ + η/50 ≤ |Im| ≤ 13η/40}`, and the two segments joining `±i(ξ₁+η/50)` to the waist
point `(-(ξ₁+η/20), 0)`.  The journey is chosen so that it lies in the "safe core" `Qc η ξ₁ α`
(`Om η ⊆ Qc` for `ξ₁ < η/2`, and on the journey `|Im| - Re ≥ ξ₁ + η/50 > ξ₁ + η√2/100`). -/
def Jour (η ξ₁ : ℝ) : Set ℂ :=
  Om η ∪ {ζ | ζ.re = 0 ∧ ξ₁ + η / 50 ≤ |ζ.im| ∧ |ζ.im| ≤ 13 * η / 40} ∪
    {ζ | ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ζ = (1 - t) * (Complex.I * ((ξ₁ + η / 50 : ℝ) : ℂ)) + t * (-(ξ₁ + η / 20))} ∪
    {ζ | ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ζ = (1 - t) * (-(Complex.I * ((ξ₁ + η / 50 : ℝ) : ℂ))) + t * (-(ξ₁ + η / 20))}

/-- The semicircular arc `{η e^{iθ} : θ ∈ [π/2, 3π/2]}`, which joins `iη` to `-iη` passing through
`-η`.  `Work.Pert.Om_arc_subset_Qc` already proves that it lies in the safe core `Qc η ξ₁ α`. -/
def ArcSet (η : ℝ) : Set ℂ :=
  {ζ | ∃ θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2),
    ζ = (η : ℂ) * Complex.exp (θ * Complex.I)}

/-- The **connected** journey on which the pointwise bounds for the oscillation estimate of
`dev Ψ = Ψ - id` are required: the two discs `Om η` together with the two chords joining `±iη` to
the point `-η` of the real axis.  A path `iη → -η → -iη` lies inside it (on the two chords), and
the whole set lies in the safe core `Qc η ξ₁ α` for `0 < ξ₁ < η/2` and `Re(1/α) > η/2 + 2ξ₁`:
each chord point `ζ = (-tη, (1-t)η)` satisfies `Re ζ - |Im ζ| = -η` and `‖ζ‖ ≤ √2 η`, which is
what the cone estimate of `Qm` needs.

NOTE (session 7): the older `Jour η ξ₁` of this file is **disconnected** (its vertical pieces stop
at `|Im| = 13η/40` while the discs `Om η` start at `|Im| = 27η/40`), so it carries no path from
`iη` to `-iη`; `JourA` replaces it for the cross-cut estimate. -/
def JourA (η : ℝ) : Set ℂ :=
  Om η ∪ {ζ | ∃ t ∈ Set.Icc (0 : ℝ) 1, ζ = (1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))} ∪
    {ζ | ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ζ = (1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))}


end

end Work.Pert
