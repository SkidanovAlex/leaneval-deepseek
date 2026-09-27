import ChallengeDeps

/-! Shared definitions for the equichordal route (design: Submission/Work/EQ/DESIGN.md). -/

namespace Work.EQ

open Complex

/-- The vertical eigenvalue `λ(a) = (1 - a)/(1 + a)` of the equichordal half-map at `A₁ = -1/2`
(and `1/λ` at `A₂ = 1/2`). For `0 < a < 1` it lies in `(0, 1)`. -/
noncomputable def eqLam (a : ℝ) : ℝ := (1 - a) / (1 + a)

/-- The normalised equichordal half-map on the plane `ℂ` (Rychlik's `U = G ∘ T₂`): with
`O₂ = b = a/2`, `U P = -P + (P - b)/|P - b|`. -/
noncomputable def eqU (a : ℝ) (P : ℂ) : ℂ :=
  -P + (P - ((a / 2 : ℝ) : ℂ)) / ((‖P - ((a / 2 : ℝ) : ℂ)‖ : ℝ) : ℂ)

/-- The point at distance `r` from the real point `c` in direction `θ`. -/
noncomputable def polarPt (c r θ : ℝ) : ℂ := (c : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- A normalised curve with two equichordal points: `O₁ = -a/2`, `O₂ = a/2`, every chord through
either point has length `1`; the curve is the polar graph of `ρ₁` about `O₁` and also the polar
graph of `ρ₂` about `O₂`. (`2π`-periodicity follows from the chord identities.) -/
def NormEqCurve (a : ℝ) (ρ₁ ρ₂ : ℝ → ℝ) : Prop :=
  Continuous ρ₁ ∧ Continuous ρ₂ ∧ (∀ θ, 0 < ρ₁ θ) ∧ (∀ θ, 0 < ρ₂ θ) ∧
    (∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1) ∧ (∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1) ∧
    Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) =
      Set.range (fun θ => polarPt (a / 2) (ρ₂ θ) θ)

/-- The functional equation of the linearised stable curve of `A₁`, cleared of denominators.
With `A = h (u/λ)`, `B = h u`, `C = h (λ u)` it reads
`(B - A)(C - B) + a B (C - A) √(1 + B²) = 0` (principal square root).  It is Rychlik's (52)
for `f = 1/h`:  `1/(f(u/λ) - f u) + 1/(f u - f(λu)) = (1/a)/√(1 + f u²)`. -/
def GermFE (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : Prop :=
  (h u - h (u / (eqLam a : ℂ))) * (h ((eqLam a : ℂ) * u) - h u) +
      (a : ℂ) * h u * (h ((eqLam a : ℂ) * u) - h (u / (eqLam a : ℂ))) *
        (1 + h u ^ 2) ^ (1 / 2 : ℂ) = 0

/-- `h` is the normalised linearised stable germ at `A₁`: holomorphic near `0`, `h 0 = 0`,
`h' 0 = -1`, real on the real axis, and solving `GermFE` on `ball 0 (λ r)`.
Geometrically `1/h u` and `1/h (λ u)` are the cotangents of the lines `O₁P`, `O₂P` of the point
`P` with linearising parameter `u`. -/
def IsStableGerm (a : ℝ) (h : ℂ → ℂ) (r : ℝ) : Prop :=
  0 < r ∧ AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧ h 0 = 0 ∧ deriv h 0 = -1 ∧
    (∀ t : ℝ, |t| < r → (h t).im = 0) ∧ ∀ u ∈ Metric.ball (0 : ℂ) (eqLam a * r), GermFE a h u

/-- The Cartesian point (as a complex number) with linearising parameter `t` on the germ:
`x = a h(λt)/(h(λt) - h t) - a/2`, `y = a h t h(λt)/(h(λt) - h t)`. For small `t > 0` it lies
in the upper half plane near `A₁ = -1/2`, and `eqU a (germPt a h t) = germPt a h (λ t)`. -/
noncomputable def germPt (a : ℝ) (h : ℂ → ℂ) (t : ℝ) : ℂ :=
  (((a * h ((eqLam a : ℂ) * t) / (h ((eqLam a : ℂ) * t) - h t)).re - a / 2 : ℝ) : ℂ) +
    (((a * h t * h ((eqLam a : ℂ) * t) / (h ((eqLam a : ℂ) * t) - h t)).re : ℝ) : ℂ) * Complex.I

/-- A real heteroclinic connection of the equichordal relation from `A₂` to `A₁`: `Γ` is a
continuous curve on `t > 0` in the open upper half plane, conjugating `eqU` to `t ↦ λ t`,
equal to the germ for small `t`, and invariant (as a set) under the bisector reflection
`P ↦ -conj P` (which carries the stable curve of `A₁` to the unstable curve of `A₂`). -/
def IsHeteroclinic (a : ℝ) (h : ℂ → ℂ) (r : ℝ) (Γ : ℝ → ℂ) : Prop :=
  IsStableGerm a h r ∧ ContinuousOn Γ (Set.Ioi 0) ∧ (∀ t, 0 < t → 0 < (Γ t).im) ∧
    (∀ t, 0 < t → eqU a (Γ t) = Γ (eqLam a * t)) ∧
    (∃ ε, 0 < ε ∧ ∀ t, 0 < t → t < ε → Γ t = germPt a h t) ∧
    ∀ t, 0 < t → ∃ s, 0 < s ∧ Γ s = -(starRingEnd ℂ) (Γ t)

end Work.EQ
