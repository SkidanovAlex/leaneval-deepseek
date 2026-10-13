/-
Copyright: work module for the Elgindi finite-time singularity project.

# The elliptic estimates of §'Elliptic Regularity Estimates' (Elgindi, Annals 194 (3) 2021)

This module fixes the vocabulary of the elliptic section (LaTeX lines 709--1039 of
`Papers/elgindi/Classical_Euler_arXiv_2.tex`).

## The equation

The axi-symmetric Biot--Savart law `-∂_rrψ - ∂_33ψ - (1/r)∂_rψ + ψ/r² = ω` becomes,
in the self-similar variables `R = ρ^α`, `θ` with `ψ = ρ²Ψ(R,θ)` (paper (PolarBSL)):

  `L(Ψ) = -α²R²∂_RRΨ - α(5+α)R∂_RΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ = F`.

`bslOp α Ψ` below is exactly the left hand side.  Note the variable name: in the
elliptic section the paper calls the radial variable `R`, in the modulation section
`z`; we use `z` throughout, so that the statements compose with the norms of
`Work.Spaces` (which are stated for the variable `z`), and `R`-derivatives are
`Work.Spaces.pz`.

## Conventions fixed here (downstream areas depend on these)

* `Fstar F z = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` is the angular moment appearing in the
  solvability condition of Proposition `prop:L2`; `OrthCond F` says it vanishes
  identically.  With `K(θ) = 3 sin θ cos²θ` one has `∫_0^{π/2} F(z,θ) K(θ) dθ = 3 Fstar F z`,
  i.e. `L₁₂(F)(z) = 3 ∫_z^∞ Fstar F ρ / ρ dρ` — so the *whole* singular part is a radial
  integral of `Fstar` alone (see `L12_eq_radial`).
* `L12` is `Work.FM.L12 Work.FM.Kpaper` (the fundamental-model operator, delivered);
  `L12dens` is the corresponding angular density.
* `Gstar α F = -(1/(4α)) L₁₂(F)`, `Gbar α F = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} Fstar F s ds`
  and `Gsing = Gstar + Gbar` are the three pieces of the function `G` of §'The singular term'
  (line 1010), chosen so that `α²z²G'' + α(5+α)zG' = (15/4) Fstar F`; consequently
  `L(Ψ + G sin 2θ) = F - (15/4) Fstar F · sin 2θ` has an *orthogonal* right hand side.
* `EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` is the quantity estimated in
  Theorem `RemovingL12` (line 1034).

## Discrepancies with the LaTeX source, resolved here

* Line 1015 of the source writes `G = ... - (3/(4α)) R^{-3/α} ∫_0^R ρ^{(3-α)/α} F_*(ρ) dρ`.
  The exponent `3/α` is a typo: the ODE solved by `G` forces the exponent `5/α`
  (as the paper's own Lemma `HardyInequality4`, line 1030, also uses); see `Gsing_ode`.
* Line 1013 writes `L(\hatΨ) = F + (…) sin 2θ` while line 939 (the same computation for
  `Φ_*`) defines `G` with the opposite sign; with our normalisation the correct identity is
  `L(Ψ + G sin 2θ) = F - (15/4) Fstar F · sin 2θ` (`bslOp_sinG`).
* The paper's `(15/4)` in the equation for `G` is written in a normalisation where `F_*`
  denotes `∫_0^{π/2} F K dθ = 3 Fstar F`; we use `Fstar = ∫_0^{π/2} F sin θ cos²θ dθ`, for
  which the identity `∫_0^{π/2} sin 2θ sin θ cos²θ dθ = 4/15` gives the cancellation
  `Fstar (F - (15/4) Fstar F sin 2θ) = 0` recorded in `Fstar_residual`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular data -/

/-- The angular profile `sin θ cos²θ` of the solvability condition. -/
def sinCos2 (θ : ℝ) : ℝ := Real.sin θ * Real.cos θ ^ 2

/-- `K(θ) = 3 sin θ cos²θ`, the angular weight of `L₁₂` (paper §Notation). -/
def Ktheta (θ : ℝ) : ℝ := 3 * Real.sin θ * Real.cos θ ^ 2

/-- `Ktheta` is the angular weight used by the fundamental model. -/
lemma Ktheta_eq_Kpaper : Ktheta = Work.FM.Kpaper := by
  funext θ; simp only [Ktheta, Work.FM.Kpaper]

/-- `Ktheta` is the angular weight `Work.Spaces.K`. -/
lemma Ktheta_eq_K : Ktheta = Work.Spaces.K := by
  funext θ; simp only [Ktheta, Work.Spaces.K]

/-! ## The elliptic operator `L` of (PolarBSL) -/

/-- The `α = 0` part of the elliptic operator:
`L₀(Ψ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`.  Its kernel contains `sin 2θ` and the kernel of its
adjoint contains `sin θ cos²θ` (`Lzero_sin_two`, `LzeroAdj_sinCos2`). -/
def Lzero (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.pthIter 2 Ψ z θ)
    + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ

/-- The second derivative of a one-variable function. -/
def d2 (f : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => deriv f θ') θ

/-- The formal adjoint of `L₀` on `L²(0,π/2)` with Dirichlet boundary conditions:
`L₀*(φ) = -φ'' - tan θ · φ' - 6φ`. -/
def LzeroAdj (φ : ℝ → ℝ) : ℝ → ℝ := fun θ => -d2 φ θ - Real.tan θ * deriv φ θ - 6 * φ θ

/-- The elliptic operator `L` of (PolarBSL), i.e. the axi-symmetric Biot--Savart operator in
the self-similar variables `R = ρ^α`, `θ` with `ψ = ρ²Ψ(R,θ)`:
`L(Ψ) = -α²R²∂_RRΨ - α(5+α)R∂_RΨ - ∂_θθΨ + ∂_θ(tan θ Ψ) - 6Ψ`. -/
def bslOp (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
    - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ + Lzero Ψ z θ

@[simp] lemma bslOp_apply (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    bslOp α Ψ z θ = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
      - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ + Lzero Ψ z θ := rfl

/-! ## The angular moment `F_*` and the orthogonality condition -/

/-- The angular moment `F_*(z) = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` of the paper. -/
def Fstar (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ

/-- The solvability condition of Proposition `prop:L2`: `F_* ≡ 0`. -/
def OrthCond (F : ℝ → ℝ → ℝ) : Prop := ∀ z, Fstar F z = 0

/-- The `L₁₂` density `∫_0^{π/2} K(θ) F(s,θ) dθ / s` of the paper. -/
def L12dens (F : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Ktheta θ * F s θ / s

/-- The integral operator `L₁₂(F)(z) = ∫_z^∞ ∫_0^{π/2} F(r,θ) K(θ)/r dθ dr` of the paper
(this is `Work.FM.L12 Work.FM.Kpaper`). -/
def L12 (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ r in Set.Ioi z, L12dens F r

/-- `L12` is the fundamental-model operator `L₁₂^K` with the paper's `K`. -/
lemma L12_eq_FM (F : ℝ → ℝ → ℝ) (z : ℝ) :
    L12 F z = Work.FM.L12 Work.FM.Kpaper F z := by
  rw [L12, Work.FM.L12]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [L12dens, Work.FM.L12dens]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [Ktheta, Work.FM.Kpaper])

/-- The radial integral `∫_z^∞ F_*(r)/r dr` in terms of which the whole singular term can be
written: `L₁₂(F)(z) = 3 ∫_z^∞ F_*(r)/r dr`. -/
def L12rad (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ r in Set.Ioi z, Fstar F r / r

/-! ## The singular term `G` of §'The singular term' -/

/-- `G_* = -(1/(4α)) L₁₂(F)`: the main term of the singular part. -/
def Gstar (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => -(1 / (4 * α)) * L12 F z

/-- The remainder `Ḡ = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds` of the singular part
(paper `\bar G`, line 1023, with the exponent corrected to `5/α`). -/
def Gbar (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => -(3 / (4 * α)) * z ^ (-(5 / α)) * ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Fstar F s

/-- `G = G_* + Ḡ`, the function of §'The singular term' solving
`α²z²G'' + α(5+α)zG' = (15/4)F_*`. -/
def Gsing (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => Gstar α F z + Gbar α F z

/-- `F ↦ F - (15/4) sin 2θ · F_*(z)`: the source left after adding `G sin 2θ` to a solution;
it is orthogonal to `sin θ cos²θ` (`Fstar_residual`). -/
def orthSource (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ - (15 / 4) * Real.sin (2 * θ) * Fstar F z

/-- The residual `Ψ - (1/(4α)) sin 2θ · L₁₂(F)` of Theorem `RemovingL12`. -/
def EllResid (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ - (1 / (4 * α)) * Real.sin (2 * θ) * L12 F z

/-! ## The class of solutions the estimates are stated for -/

/-- `Ψ` solves the elliptic problem (PolarBSL) with source `F` on the open quadrant, with the
Dirichlet conditions `Ψ(z,0) = Ψ(z,π/2) = 0` and with `Ψ(z,θ) → 0` as `z → ∞`. -/
def IsBslSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π/2 → bslOp α Ψ z θ = F z θ) ∧
    (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-- The standing hypotheses of the `H^k` elliptic estimates: `Ψ` is a smooth solution of
(PolarBSL) with source `F` (`IsBslSol`), and the `H^k`-integrands of `F`, `∂_θθΨ` and
`z²∂_zzΨ` are integrable, so that the corresponding `HkSq` are the honest squares of the
weighted `L²`-norms (without this the integral is `0` by convention and the estimates are
vacuous). -/
def IsEstData (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  Work.Spaces.SmoothNbhd Ψ ∧ IsBslSol α F Ψ ∧ Work.Spaces.HkMem α k F ∧
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) ∧
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)

end Work.Elliptic
