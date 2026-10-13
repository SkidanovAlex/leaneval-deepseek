/-
Work module for the Elgindi finite-time singularity project (H2W / Ae layer).

# `SliceSigmaHardyTwo` — the second-order weighted Hardy inequality for slices

For `g : ℝ → ℝ` of class `C²` on the open interval `(0, π/2)`, whose one-sided limits at
`0` and `π/2` both vanish, and whose second derivative is square-integrable against the
angular weight `sEta θ = sin(2θ)^{-η}` (`η = 99/100`):

  `∫⁻_θ∈Iθ ofReal (g θ² · sEta θ)  ≤  ofReal C · ∫⁻_θ∈θ ofReal ((g'' θ)² · sEta θ)`.

This is the second-order weighted Hardy inequality with the weight `sin(2θ)^{-η}`: the
weight blows up like `θ^{-η}` at `0⁺` and like `(π/2-θ)^{-η}` at `(π/2)⁻` (and is `≥ 1` in
between), and the two *vanishing endpoint limits* of `g` are exactly the two Dirichlet
boundary conditions that make the second-order Hardy inequality true (the critical exponent
`η = 1` is not reached: `η = 99/100 < 1`, so the second derivative does control `g`; the
inequality is false for `η ≥ 3` and, more importantly, false with only one endpoint
condition).

## Where the proof is, and why this module is a re-export

The statement — with the same hypotheses, the same conclusion and the constant `C = 10^6` —
is proved in

  `Submission/Work/FTS/EllipticEst/H2W/Ae/ZeroHardy/sliceZeroLimitHardy.lean`,
  `Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy`

(the module is imported below, and is `sorry`-free: `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`).  Since a colleague of this team has already
carried out that proof, this module delivers the *requested declaration name* on top of it,
in the same way as the twin `Submission/Work/FTS/EllipticEst/Auxiliary/Slice9PoincareAuxName.lean`
does for `Work.FTS.EllipticEst.Aux.slicePoincare9_fts`.

The mathematical route of that proof (the note
`Submission/Work/FTS/EllipticEst/H2W/Ae/SliceTwo/NOTES_greenSliceBound.md` records it in
detail):

* **Green identity.**  For `0 < a < θ < b < π/2`, integrating by parts twice against the
  Green kernel `ψ₁ t = c₁ (t-a)`, `ψ₂ t = c₂ (b-t)` (`c₁ = (b-θ)/(b-a)`, `c₂ = (θ-a)/(b-a)`,
  `c₁+c₂ = 1`) on `[a,θ]` and `[θ,b]` with respect to the second derivative gives the exact
  identity `g θ = c₁ g a + c₂ g b - ∫_a^θ ψ₁ g'' - ∫_θ^b ψ₂ g''` (the `g'(θ)` terms cancel);
  as `|ψᵢ| ≤ (b-a)/4 ≤ π/8` and `c₁, c₂ ≤ 1`,
  `|g θ| ≤ (π/8) ∫_a^b |g''| + |g a| + |g b|`.
* **Endpoint limits.**  Choosing `a` near `0` and `b` near `π/2` at which `|g| < ε` (possible
  by the two limit hypotheses) and letting `ε ↓ 0` gives the *sharp* pointwise bound
  `|g θ| ≤ (π/8) ∫_{Ioc 0 (π/2)} |g''|` (the constant `π/8` is the supremum of the Green
  kernel `θ(L-θ)/L`).
* **Weighted Cauchy–Schwarz.**  With `σ = sEta`,
  `(∫ |g''|)² ≤ (∫ (g'')² σ) (∫ σ^{-1})`, where `∫_{Iθ} σ ≤ 10^4`
  (`FTS.EllipticEst.integrableOn_thEta`) and `∫_{Iθ} σ^{-1} = ∫_{Iθ} sin(2θ)^η ≤ π/2`
  (`FTS.EllipticEst.integrableOn_sin_two_rpow`, `η ≥ 0`).
* **Assembly.**  `g² σ ≤ (π/8)² · 10^4 · (π/2) · (∫ (g'')²σ) · σ` pointwise a.e. on `Iθ`, and
  the `∫⁻` chain (`lintegral_mono`, `ofReal_integral_eq_lintegral_ofReal`) closes with the
  constant `10^6` since `(π/8)² (π/2) 10^4 < 10^6`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

/-- **Second-order weighted Hardy inequality for angular slices** (the `sEta` weight
`sin(2θ)^{-η}`, `η = 99/100`).  For `g` of class `C²` on `(0, π/2)` with vanishing one-sided
limits at both endpoints and `(g'')² sEta` integrable on `Iθ`, the function itself is
controlled by its second derivative in the same weighted `L²`:
`∫⁻_θ∈Iθ ofReal (g² sEta) ≤ ofReal C · ∫⁻_θ∈Iθ ofReal ((g'')² sEta)`.

Proved in `Submission/Work/FTS/EllipticEst/H2W/Ae/ZeroHardy/sliceZeroLimitHardy.lean` as
`Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy`; see the module docstring above
for the route (Green-function pointwise bound `|g θ| ≤ (π/8)∫|g''|` + weighted
Cauchy–Schwarz + the `∫⁻` assembly). -/
theorem SliceSigmaHardyTwo : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
    ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal C
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
  Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy

end Work.FTS.EllipticEst.H2W.Ae
