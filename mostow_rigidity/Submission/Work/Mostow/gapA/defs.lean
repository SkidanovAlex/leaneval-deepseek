import Mathlib
import Submission.Mostow.HLDefs

/-!
# Vocabulary for the `n = 3` gap-A (escape-short) development

The route for `n = 3` (see `Submission/Work/Mostow/gapA_three.lean` and
`REFS/lead-design/NOTES_LEAD_gapA.md`) needs three geometric objects attached to a pair of
boundary points `a ≠ b` of `Sph n` and to an isometry `b : PO n 1`:

* `geodSet a b` — the geodesic with endpoints `a` and `b`, described as the equality locus of
  the reverse Cauchy–Schwarz inequality for the two null vectors `(a,1)`, `(b,1)`
  (`levMulGe`: `1 - ⟪ξ,η⟫ ≤ 2 · lev ξ u · lev η u`, i.e. `exp (β_ξ u + β_η u) ≥ (1-⟪ξ,η⟫)/2`);
* `distGeod a b u` — the hyperbolic distance from `u` to that geodesic;
* `Tb b η` — the set of points at which `b` is `η`-near-identity.

An element of finite order different from `1` is a rotation about such a geodesic: this is the
content of `IsRotationAbout f a b θ`, which records both that the fixed set of `f` is exactly
`geodSet a b` and the hyperbolic displacement formula

`hdist u (f u) = 2 * arcsinh (sinh (distGeod a b u) * sin (θ/2))`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The geodesic with endpoints `a` and `b`, as the equality locus of the reverse
Cauchy–Schwarz inequality for the two null vectors `(a,1)`, `(b,1)`. -/
def geodSet (a b : E n) : Set (E n) :=
  {u : E n | Real.exp (busemann a u + busemann b u) = (1 - inner ℝ a b) / 2}

/-- The hyperbolic distance from `u` to the geodesic `geodSet a b`. -/
def distGeod (a b u : E n) : ℝ :=
  Real.arcosh (Real.sqrt (2 * Real.exp (busemann a u + busemann b u) / (1 - inner ℝ a b)))

/-- The set of points at which `b` is `η`-near-identity. -/
def Tb (b : PO n 1) (η : ℝ) : Set (E n) := {w : E n | NearIdAt b w η}

/-- `f` is a rotation about the geodesic `geodSet a b` by angle `θ`: its fixed set is exactly
that geodesic, and the displacement formula holds. -/
def IsRotationAbout (f : PO n 1) (a b : E n) (θ : ℝ) : Prop :=
  (∀ u : E n, f • u = u ↔ u ∈ geodSet a b) ∧
    ∀ u : E n, hdist u (f • u) =
      2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (θ / 2))

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- Orientation of an isometry of `ℍ³`: for `PO 3 1` the determinant of a lift is well defined,
because any two lifts differ by `-1` and `det (-A) = det A` for a `4 × 4` matrix. -/
def IsOriented (g : PO 3 1) : Prop := 0 < (mat (rep g)).det

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The rotation data produced by `Work.Mostow.gapA.rotData3` for a finite-order element which
is near-identity at `z`. -/
def RotData (Γ : Subgroup (PO 3 1)) (f : PO 3 1) (z : E 3) (η : ℝ) : Prop :=
  ∃ (a b : E 3) (θ : ℝ) (M : ℕ) (b₀ : PO 3 1),
    a ∈ Sph 3 ∧ b ∈ Sph 3 ∧ a ≠ b ∧ 0 < θ ∧ θ ≤ Real.pi ∧
    IsRotationAbout f a b θ ∧ 2 ≤ (orderOf f : ℝ) * Real.sin (θ / 2) ∧
    0 < M ∧ b₀ ∈ Γ ∧ orderOf b₀ = M ∧ IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)) ∧
    (∀ g : PO 3 1, g ∈ Γ → (∀ u : E 3, u ∈ geodSet a b → g • u = u) →
      (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ IsOriented g) ∧
    (∃ k : ℤ, f = b₀ ^ k) ∧
    Real.sinh (distGeod a b z) * Real.sin (Real.pi / (M : ℝ)) ≤ η / 2

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The radius of a tube around the axis on which the rotation `b₀` (of order `M`) is
`η_Z`-near-identity: `ρ = arsinh (η_Z / (2 sin (π/M))) - 1`. -/
def tubeR (M : ℕ) (η_Z : ℝ) : ℝ :=
  Real.arsinh (η_Z / (2 * Real.sin (Real.pi / (M : ℝ)))) - 1

end

end Work.Mostow
