/-
# `Work.FTS.PhiStar.StarDefs` — definitions of the `StarCore` route

The lead design `FTS/STARPKG_T2_LEAD.md` (2026-10-06) replaces the field-by-field targets of
`FTS/PhiStar` by one object

`Ŷ = Ycheck α Φs = ((z+1)/z)·Φ̃_*/sin 2θ`,   `Φ̃_* = PhiTs α Φs = Φ_* − (1/4α)sin 2θ·L₁₂(F_*)`,

whose *flat* bound (`VocabO2.FlatW 7 (Ycheck α Φs) (Cs·α)`) yields all eleven `StarPkgo2`
fields by algebra.  This file contains the two additional definitions of that route:

* `Linv` — the `σ`-normalised zero-moment Dirichlet inverse of `L₀` (node P-G).  With
  `μ = sin²θ cos³θ` and `h = L₀u`, `u = σv` satisfies `(μv')' = −(μ/σ)h`, i.e.

  `v' = −μ^{-1}∫_0^θ μh/σ`,   `v(0) = 0`;

  the right-hand side is regular at `θ = 0` because `μ/σ = sinθ cos²θ/2`, and bounded at
  `θ = π/2` exactly when `∫_0^{π/2} h sinθcos²θ = 0` (the moment condition).  This is the
  inversion that recovers one angular order at a time (node P-C3) without dividing `h` by `σ`.

* `RadialW` — the radial weight family of the T-operator analysis (node P-C2):
  `∂_z^k` up to order `8`, and `z^{k-8}∂_z^k` up to order `22`, uniformly in the mode `m ≥ 1`
  and in `α ≤ 1/5` (no resonance: `2m/α ≥ 2/α ≥ 10 > 8`).
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.VocabO2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The `σ`-normalised zero-moment Dirichlet solution `v = u/σ` of `L₀u = h`:
`v' = −μ^{-1}∫_0^θ μh/σ` with `μ = sin²θcos³θ`.  (At `θ = π/2` the expression is Lean's junk
`0`; only the open interval is used.) -/
def Linv (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ *
    (∫ θ' in (0 : ℝ)..θ,
      Real.sin θ' ^ 2 * Real.cos θ' ^ 3 * h θ' / Work.Construction.s2 θ'))

/-- The iterates `𝒜^j φ` of the radial operator `𝒜a = αz²a'' + (5+α)z a'` applied to
`φ = VocabO.phiR`; `phiAj 1 = VocabO.phiA`.  Node P-C1 needs `𝒜²φ`, `𝒜³φ`. -/
def phiAj : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ z => Work.FTS.VocabO.phiR z
  | (j + 1) => fun α z =>
      α * z ^ 2 * iteratedDeriv 2 (phiAj j α) z + (5 + α) * z * deriv (phiAj j α) z

/-- **The zero-moment Dirichlet inverse itself**: `LinvI h = ∫_0^θ Linv h`, i.e. the `v` with
`L₀(sin 2θ · v) = h`.  (`Linv` is its derivative `v'`; the consumer needs `v`, and the identity
`L₀(σ·LinvI h) = h` is the node `LinvI_solves`.) -/
def LinvI (h : ℝ → ℝ) : ℝ → ℝ := fun θ => ∫ θ' in (0 : ℝ)..θ, Linv h θ'

/-- `ψ₂ = sin 2θ · LinvI ψ`: the zero-moment Dirichlet solution of `L₀ψ₂ = ψ`
(the first telescoping step of node P-C1). -/
def Psi2 (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => Work.Construction.s2 θ * LinvI ψ θ

/-- `ψ₃ = sin 2θ · LinvI ψ₂`: the second telescoping step. -/
def Psi3 (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => Work.Construction.s2 θ * LinvI (Psi2 ψ) θ

/-- The radial T-operator weight family **near `z = 0`**: `|z^{k-8}∂_z^k f| ≤ K` for `k ≤ 22`
and `0 < z ≤ 1` (for `k ≤ 8` this is just `|∂_z^k f| ≤ K`).  The restriction `z ≤ 1` is
necessary: the mode-wise Green function only decays like `z^{-2}` at `z = ∞`, so the weighted
family is a statement about the singular end `z = 0`. -/
def RadialW (f : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ 22 → ∀ z : ℝ, 0 < z → z ≤ 1 → |z ^ (k - 8) * iteratedDeriv k f z| ≤ K

/-- Boundedness of the first `l` derivatives of a source on `(0,∞)`; the hypothesis under which
the mode-wise radial Green function is estimated in node P-C2. -/
def BddDeriv (l : ℕ) (c : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 < z → |iteratedDeriv k c z| ≤ K

end Work.FTS.PhiStar
