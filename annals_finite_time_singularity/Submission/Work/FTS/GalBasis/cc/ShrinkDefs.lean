/-
# `Work.FTS.GalBasis.cc.ShrinkDefs` — the integral functionals of the shrinking layers

Auxiliary definitions packaging the iterated integrals that occur in the two shrinking-set
lemmas (`Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta`,
`..._z`) and in the wrong-weight layer lemma (`...wrongWeight_layer_tendsto_zero`).  They exist
so that the statements of those lemmas can be written without notation.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

/-- `∫_{Iz} ∫_{Iθ} HkIntegrand α 4 f · 1_s(θ)`: the `ℋ⁴`-mass of `f` carried by the `θ`-set `s`. -/
def thetaShrinkInt (α : ℝ) (f : Fn) (s : Set ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.HkIntegrand α 4 f z θ * s.indicator (fun _ => (1 : ℝ)) θ

/-- `∫_{Iz} 1_t(z) · (∫_{Iθ} HkIntegrand α 4 f z θ)`: the `ℋ⁴`-mass of `f` carried by the
`z`-set `t`. -/
def zShrinkInt (α : ℝ) (f : Fn) (t : Set ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, t.indicator (fun _ => (1 : ℝ)) z *
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)

/-- `∫_{Iz} ∫_a^c (D_z^b f · Wt α)²`: the *wrong-weight* layer integral, i.e. the `γ`-weighted
`D_z`-slot of `f` of order `b`, integrated over the angular layer `(a,c)`.  (Note
`Wt α z θ = w z · sin(2θ)^{-γ/2`, so the integrand is the wrong-weight slot density squared.) -/
def wrongLayerInt (α : ℝ) (f : Fn) (b : ℕ) (a c : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in a..c, (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2

end Work.FTS.GalBasis.cc
