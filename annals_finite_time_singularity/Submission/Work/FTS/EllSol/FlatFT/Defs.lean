/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions for the Fourier proof of `flat2DAgmon`

`Work.FTS.EllSol.flat2DAgmon` is the flat 2-D Agmon interpolation

```
∫∫ (∂_t∂_θg)² σ_a ≤ C ( ∫∫ (∂_tg)² σ_η + √( ∫∫ (∂_t²g)² σ_η · ∫∫ (∂_θ²g)² σ_η ) )
```

with `σ_a = sin(2θ)^{2-γ(α)}`, `σ_η = sin(2θ)^{-η}`, `η = 99/100`, `γ(α) = 1 + α/10`.

## The route (see `NOTES_flat2DAgmon_route.md` for the full account)

The proof is the Plancherel derivation in `t` with the per-frequency (`ξ`) angular Agmon
inequality `Work.EllipticEst.Core.i0Aux.thetaInterpCore` (PROVED, constant `199`) applied to
the *slices* `Φ_ξ(θ) = (𝓕_t g(·,θ))(ξ)`:

* the slices are of class `C²` on `(0,π/2)` with **values** `0` at the endpoints (this only
  uses that each `t`-slice `g(·,θ)` has *uniformly compact support* in `t` — then
  `Φ_ξ(θ) = ∫_t g(t,θ) e^{-2πiξt} dt` is an absolutely convergent integral and the θ-derivatives
  may be taken under the integral sign);
* for a.e. `ξ` the three weighted integrals of `thetaInterpCore` are finite;
* multiplying by `(2πξ)²` and integrating over `ξ` turns `∫_θ Φ_ξ² σ_η`, `∫_θ (Φ_ξ'')² σ_η` into
  the `t`-slots `HkSq α 0 (D_zG)`, `HkSq α 0 (D_z²G)`, `HkSq α 0 (∂_θ²G)` via Plancherel, and the
  Cauchy–Schwarz pairing `((2πξ)²√A)·(√B)` produces exactly `√(P₂ Q₂)`.

The general statement then follows by the cutoff `g_N = η(t/N)·g` and Fatou/monotone
convergence (this is the part that avoids the fact that the slices of a general `g` are only
`H²(σ_η)`, not `C²`).

This file only fixes the vocabulary: the two weights, the "nice" class (uniformly compact
support in `t`), the slices `Φ_ξ`, and the four integral functionals.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The light angular weight `σ_a = sin(2θ)^{2-γ(α)}` of the left-hand side. -/
def wA (α : ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- The heavy angular weight `σ_η = sin(2θ)^{-η}`. -/
def wE : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

@[simp] theorem wA_def (α θ : ℝ) : wA α θ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := rfl
@[simp] theorem wE_def (θ : ℝ) : wE θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

theorem wA_eq_sigA (α θ : ℝ) : wA α θ = Work.FTS.EllipticEst.TT.sigA α θ := rfl
theorem wE_eq_sEta (θ : ℝ) : wE θ = Work.FTS.EllipticEst.sEta θ := rfl

/-- `σ_a ≤ σ_η` on `Iθ` (for `α ≤ 1`). -/
theorem wA_le_wE {α θ : ℝ} (hα : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) : wA α θ ≤ wE θ :=
  Work.FTS.EllipticEst.TT.sigA_le_sEta (α := α) (θ := θ) hα hθ

theorem wA_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wA α θ :=
  Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ

theorem wE_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wE θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg_of_mem_Iθ hθ) _

/-- The "nice" class of data for which the Plancherel derivation is performed directly: `g` is
`C²` on the open strip, vanishes at the two endpoints for every `t`, and has **uniformly
compact support** in `t` (i.e. `g t θ = 0` for `|t| > N`, uniformly in `θ`). -/
def NiceFlat (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
    (∀ t : ℝ, g t 0 = 0) ∧ (∀ t : ℝ, g t (Real.pi / 2) = 0) ∧
    ∃ N : ℝ, ∀ t θ : ℝ, N < |t| → g t θ = 0

/-- The explicit `t`-Fourier transform (Mathlib's `Real.fourier` convention) of a
complex-valued function of one real variable. -/
def slice1 (h : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ, h t * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))

/-- The `t`-Fourier slice `Φ_ξ(θ) = ∫_t g(t,θ) e^{-2πiξt} dt` (as a complex-valued function of
`θ`).  For `NiceFlat g` this is an absolutely convergent integral. -/
def slice (g : ℝ → ℝ → ℝ) (ξ θ : ℝ) : ℂ :=
  ∫ t : ℝ, (g t θ : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))

theorem slice_eq_slice1 (g : ℝ → ℝ → ℝ) (ξ θ : ℝ) :
    slice g ξ θ = slice1 (fun t => (g t θ : ℂ)) ξ := rfl

/-- `Xint`: the left-hand side `∫∫ (∂_t∂_θg)² σ_a` (iterated integral form). -/
def Xint (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pz (Work.Spaces.pth g) t θ) ^ 2 * wA α θ

/-- `A₁`: the first-order slot `∫∫ (∂_tg)² σ_η`. -/
def Aone (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz g t θ) ^ 2 * wE θ

/-- `A₂`: the second-order `t`-slot `∫∫ (∂_t²g)² σ_η`. -/
def Atwo (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pz g) t θ) ^ 2 * wE θ

/-- `A₃`: the second-order `θ`-slot `∫∫ (∂_θ²g)² σ_η`. -/
def Athree (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth g) t θ) ^ 2 * wE θ

/-- The per-`ξ` angular energy of the slice, with the light weight. -/
def sliceA (α : ℝ) (g : ℝ → ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, ‖deriv (fun θ' => slice g ξ θ') θ‖ ^ 2 * wA α θ

/-- The per-`ξ` angular energy of the slice, with the heavy weight. -/
def sliceP (g : ℝ → ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ

/-- The per-`ξ` angular energy of the second `θ`-derivative of the slice. -/
def sliceQ (g : ℝ → ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2 * wE θ

end

end Work.FTS.EllSol.FlatFT
