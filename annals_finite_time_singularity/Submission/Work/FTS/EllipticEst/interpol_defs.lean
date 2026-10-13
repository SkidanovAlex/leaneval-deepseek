/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for `interpol_mixed_weighted`

The four weighted integrals, the hypothesis package `Hyp` and the support predicate
`CompactZ` attached to the mixed weighted interpolation estimate

  `α² ∫∫ (D_z∂_θG)² w² sin(2θ)^{-η} ≤ C (α⁴ ∫∫ (D_z²G)² w² sin(2θ)^{-η}
      + ∫∫ (∂_θθG)² w² sin(2θ)^{-η} + α² ∫∫ (D_zG)² w² sin(2θ)^{-η})`.

This file contains definitions only (no `sorry`), so that the lemmas about these notions can be
proved in modules that do not inherit `sorryAx` from the statement of
`Work.FTS.EllipticEst.interpol_mixed_weighted`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- The first weighted integral `∫∫ (D_z∂_θG)² w² sin(2θ)^{-η}` of the interpolation
statement, as a function of `G` (an honest real number when the hypotheses of the statement
hold). -/
def mixInt (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The second weighted integral `∫∫ (D_z²G)² w² sin(2θ)^{-η}`. -/
def ddInt (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The third weighted integral `∫∫ (∂_θθG)² w² sin(2θ)^{-η}`. -/
def ttInt (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The fourth weighted integral `∫∫ (D_zG)² w² sin(2θ)^{-η}`. -/
def dInt (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The four integrability hypotheses of the interpolation lemma, bundled. -/
def FourInt (G : ℝ → ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz

/-- The full hypothesis package of the interpolation statement: smoothness on a neighbourhood
of the closed quadrant, vanishing on the two angular boundaries, decay of `D_z²G` along
`z → ∞` at every angle, and the four integrability conditions. -/
def Hyp (G : ℝ → ℝ → ℝ) : Prop :=
  Work.Spaces.SmoothNbhd G ∧ (∀ z : ℝ, G z 0 = 0) ∧ (∀ z : ℝ, G z (Real.pi / 2) = 0) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ)
        Filter.atTop (nhds 0)) ∧
    FourInt G

/-- `G` is supported in a compact subinterval `[δ, R]` of `(0, ∞)`. -/
def CompactZ (G : ℝ → ℝ → ℝ) : Prop :=
  ∃ δ R : ℝ, 0 < δ ∧ δ < R ∧ ∀ z ∉ Set.Icc δ R, ∀ θ, G z θ = 0

/-- The conclusion of the interpolation statement, as a predicate in the constant `C`. -/
def Concl (C : ℝ) : Prop :=
  ∀ (α : ℝ), 0 < α → α ≤ 1 / 4 → ∀ (G : ℝ → ℝ → ℝ),
    Hyp G → α ^ 2 * mixInt G ≤ C * (α ^ 4 * ddInt G + ttInt G + α ^ 2 * dInt G)

end Work.FTS.EllipticEst

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The weight `ρ = w(z)²·sin(2θ)^{-η}` of the interpolation estimate. -/
def rho (z θ : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `SG = -(D²G + b DG)` with `b(z) = (z-3)/(1+z)`, i.e. `S G = D^*DG` for the adjoint
`D^* = -(D + b)` of `D = D_z` with respect to the weight `rho`. -/
def SG (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dz (Work.Spaces.Dz G) z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)

/-- `TG = -(∂_θθG - 2η cot(2θ) ∂_θG)`, i.e. `T G = δ^*δG` for the adjoint
`δ^* = -∂_θ + 2η cot(2θ)` of `δ = ∂_θ` with respect to the weight `rho`. -/
def TG (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.pth (Work.Spaces.pth G) z θ
    - 2 * Work.Spaces.eta * Real.cos (2 * θ) / Real.sin (2 * θ) * Work.Spaces.pth G z θ)

/-- The `L²(ρ)` pairing `⟨f, g⟩_ρ = ∫∫ f g ρ` over the quadrant. -/
def pairing (f g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ * g z θ * rho z θ

end Work.FTS.EllipticEst
