import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-centre vocabulary (module `Submission.Work.Diff.C.geoCrux.RadialBase`)

The definitions underlying the two-centre modulus estimate:

* `rho0 c = π - arccos (1-c)`, the radius of the region in which the shape-operator hypotheses are
  available;
* `twoK σ τ = cot σ + cot (τ - σ)` — the two-centre shape sum;
* `twoL σ τ = cot σ - cot τ` — the base-point shape difference;
* `twoD ε₁ σ τ = ε₁ (1/sin σ + 1/sin (τ-σ))` — the shape-sum error;
* `twoE ε₁ σ τ = ε₁ (1/sin σ + 1/sin τ)` — the base-point shape-difference error.

They live here (rather than in `Submission.Work.Diff.C.geoCrux.radial_modulus`, which is where they
were first written) so that modules that only need the *vocabulary* can be placed below
`radial_modulus` in the import graph; the arithmetic lemmas about them stay in `radial_modulus`.
-/

namespace Work.Diff.C.geoCrux

/-- `ρ₀ = π - arccos (1-c)`, the radius of the region in which the hypotheses are available. -/
noncomputable def rho0 (c : ℝ) : ℝ := Real.pi - Real.arccos (1 - c)

/-- `κ(σ,τ) = cot σ + cot(τ-σ)`: the two-centre shape sum. -/
noncomputable def twoK (σ τ : ℝ) : ℝ := Real.cot σ + Real.cot (τ - σ)

/-- `λ(σ,τ) = cot σ - cot τ`: the base-point shape difference. -/
noncomputable def twoL (σ τ : ℝ) : ℝ := Real.cot σ - Real.cot τ

/-- `δ = ε₁ (1/sin σ + 1/sin(τ-σ))`: the shape-sum error. -/
noncomputable def twoD (ε₁ σ τ : ℝ) : ℝ := ε₁ * (1 / Real.sin σ + 1 / Real.sin (τ - σ))

/-- `η = ε₁ (1/sin σ + 1/sin τ)`: the base-point shape-difference error. -/
noncomputable def twoE (ε₁ σ τ : ℝ) : ℝ := ε₁ * (1 / Real.sin σ + 1 / Real.sin τ)

end Work.Diff.C.geoCrux
