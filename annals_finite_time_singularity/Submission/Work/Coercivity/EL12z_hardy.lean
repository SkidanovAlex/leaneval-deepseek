/-
# The Hardy inequality `|z⁻¹ L₁₂(f)|² ≤ 4 |L₁₂dens(f)|²` of the coercivity chapter

This is the *Hardy-weight* estimate of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), Lemma
  `HardyWeight` (tex 503): "Assume `f w ∈ L²` and `L₁₂(f) w ∈ L²`. Then
  `|L₁₂(f) w|_{L²} ≤ 4 |f w|_{L²}`", in the sharp `1/z²` component of the decomposition
  `w² = 1/z⁴ + 2/z² + 1` (compare tex 510--519), phrased for the radial function
  `z ↦ L₁₂(f)(z)` alone.

Writing `U = L₁₂(f) = L12f f` (so that `U'(z) = -L₁₂dens(f)(z)` on `(0,∞)`, see
`Work.FM.hasDerivAt_L12`), the lemma says

  `∫_0^∞ U(z)² / z² dz ≤ 4 ∫_0^∞ L₁₂dens(f)(z)² dz`,

which is the classical Hardy inequality `∫ U²/z² ≤ 4 ∫ (U')²` for `U` vanishing (in the
weighted sense `U(z)²/z → 0`) at `z = 0⁺` and at `z = +∞`.  Its proof is a single
integration by parts,

  `d/dz (U²/z) = 2 U U'/z - U²/z²`,  so  `∫ U²/z² = -2 ∫ U U'/z`,

at the level of the *density* `L₁₂dens(f)`: Cauchy–Schwarz in the form
`2|UU'|/z ≤ (1/2)(U/z)² + 2(U')²` turns the identity into
`A ≤ A/2 + 2B`, i.e. `A ≤ 4B`, where `A = ∫ U²/z²` and `B = ∫ (U')²`.

## Contents

* `hardy_core` — the abstract one-dimensional Hardy inequality, proved from the two
  independent pieces `Work.Coercivity.HardyCore.hardy_ftc` (the integration-by-parts
  identity `∫ g²/z² = ∫ 2 g g'/z`, valid because the boundary terms `g²/z` vanish at the
  two ends) and `Work.Coercivity.HardyCore.hardy_amgm` (the pointwise AM–GM domination of
  the cross term), which were proved in parallel under `Submission/Work/Coercivity/HardyCore/`.

* `EL12z_hardy` — the requested lemma: the Hardy inequality for `U = L₁₂(f)`, where the
  differentiability of `U`, the two boundary conditions and the integrability of `g²/z²`
  are read off from `HardyHyp`, and `∫ (L₁₂dens(f))²` is finite by hypothesis.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Defs
import Submission.Work.FM.Core2
import Submission.Work.Coercivity.HardyCore.hardy_ftc
import Submission.Work.Coercivity.HardyCore.hardy_amgm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- **The abstract Hardy inequality**: for `g` differentiable on `(0,∞)` with derivative
`g'`, whose "boundary term" `z ↦ g z ^ 2 / z` vanishes at `0⁺` and at `+∞`, and with
`g ^ 2 / z ^ 2` and `g' ^ 2` integrable on `(0,∞)`,

  `∫_0^∞ g(z)² / z² dz ≤ 4 ∫_0^∞ g'(z)² dz`.

This is the sharp Hardy constant `4`.  The two halves of the proof are
`∫_0^∞ g²/z² = ∫_0^∞ 2 g g'/z` (integration by parts) and the AM–GM bound
`∫ 2 g g'/z ≤ (1/2) ∫ g²/z² + 2 ∫ g'²`; combining them gives
`A ≤ A/2 + 2B`, hence `A ≤ 4B` for `A = ∫ g²/z²`, `B = ∫ g'²`. -/
theorem hardy_core (g g' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' z) z)
    (h0 : Tendsto (fun z => g z ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (htop : Tendsto (fun z => g z ^ 2 / z) atTop (𝓝 0))
    (hA : IntegrableOn (fun z => g z ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ)))
    (hB : IntegrableOn (fun z => g' z ^ 2) (Set.Ioi (0 : ℝ))) :
    ∫ z in Set.Ioi (0 : ℝ), g z ^ 2 / z ^ 2 ≤ 4 * ∫ z in Set.Ioi (0 : ℝ), (g' z) ^ 2 := by
  -- `A = ∫ 2 g g'/z` (integration by parts; `HardyHyp`-style boundary conditions).
  have h1 := HardyCore.hardy_ftc g g' hderiv h0 htop hA hB
  -- `∫ 2 g g'/z ≤ A/2 + 2B` (AM–GM).
  have h2 := HardyCore.hardy_amgm g g' hA hB
  linarith

/-- **The Hardy inequality for the fundamental model's `L₁₂`**: for `f` satisfying the
analytic hypotheses `HardyHyp` and with `L₁₂dens K f` square integrable,

  `∫_0^∞ (L₁₂(f)(z))² / z² dz ≤ 4 ∫_0^∞ (L₁₂dens(f)(z))² dz`.

Here `L₁₂(f) = ∫_z^∞ L₁₂dens(f)` is the radial function of the fundamental model, and
`L₁₂dens(f)(z) = ∫_θ K(θ) f(z,θ)/z dθ` is its (negative) derivative.  This is the sharp
`z^{-2}` component of the paper's Lemma `HardyWeight` (Annals 194 (3) 2021, tex 503). -/
theorem EL12z_hardy (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hQ : MeasureTheory.IntegrableOn (fun z => (FM.L12dens Spaces.K f z) ^ 2) (Set.Ioi 0)) :
    ∫ z in Set.Ioi (0 : ℝ), (L12f f z) ^ 2 / z ^ 2
      ≤ 4 * ∫ z in Set.Ioi (0 : ℝ), (FM.L12dens Spaces.K f z) ^ 2 := by
  -- `L₁₂(f)` is differentiable on `(0,∞)` with derivative `-L₁₂dens(f)`.
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (L12f f) (-(FM.L12dens Spaces.K f z)) z := fun z hz =>
    FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hf.hint (hf.hcont z hz) hz
  -- The two boundary terms `(L₁₂(f))²/z` vanish at `0⁺` and at `+∞`
  -- (`HardyHyp.bd0`/`HardyHyp.bdTop` at `j = 1`).
  have h0 : Tendsto (fun z => (L12f f z) ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hf.bd0 1 (by norm_num)).1
    have hexp : (2 * ((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
    rw [hexp] at h
    simpa [Real.rpow_one] using h
  have htop : Tendsto (fun z => (L12f f z) ^ 2 / z) atTop (𝓝 0) := by
    have h := (hf.bdTop 1 (by norm_num)).1
    have hexp : (2 * ((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
    rw [hexp] at h
    simpa [Real.rpow_one] using h
  -- `∫ (L₁₂(f))²/z²` is finite (`HardyHyp.intA` at `j = 1`).
  have hA : IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    have h := hf.intA 1 (by norm_num)
    simpa using h
  -- `∫ (L₁₂dens(f))²` is finite by hypothesis.
  have hB : IntegrableOn (fun z => (-(FM.L12dens Spaces.K f z)) ^ 2) (Set.Ioi 0) := by
    simpa using hQ
  have hmain := hardy_core (L12f f) (fun z => -(FM.L12dens Spaces.K f z))
    hderiv h0 htop hA hB
  simpa using hmain

end Work.Coercivity
