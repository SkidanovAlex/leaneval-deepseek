import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngClean

open MeasureTheory Set Filter
open scoped Real Topology

/-- At `k = 0` the `H^k`-integrand collapses to the single square
`(g z θ · w z / sin(2θ)^{η/2})²`: the `D_z`-sum has the one term `i = 0` and the mixed
double sum is empty. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The bridge `HkMem α 0 g ⟹ IPMem g g`.**

`Work.Spaces.HkMem α 0 g` is the honesty of `HkIntegrand α 0 g`, whose only summand is
`(g z θ · w z / sin(2θ)^(η/2))²`; `AngSecond.IPMem g g` is the honesty of
`g z θ · g z θ · w z² · σ θ`.  The bridge is the pointwise identity `AngSecond.sq_mul_W`,
valid for every `θ ∈ Iθ` (its endpoint case `sin(2θ) = 0` is handled by `Real.zero_rpow`), so
both conjuncts transfer by `IntegrableOn.congr`. -/
theorem HkMem_zero_IPMem {α : ℝ} {g : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 g) :
    Work.FTS.EllipticEst.AngSecond.IPMem g g := by
  -- `HkMem α 0 g` is the honesty of `(g z θ · w z / sin(2θ)^{η/2})²`.
  have hsq : ∀ z θ, θ ∈ Work.Spaces.Iθ → Work.Spaces.HkIntegrand α 0 g z θ
      = g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    fun z θ hθ => by rw [HkIntegrand_zero_eq α g z θ,
      Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ]
  -- The `θ`-slice of `IP g g` at a fixed `z`, written as the iterated integral of the
  -- `HkIntegrand`.
  have hslice : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    fun z => setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hsq z θ hθ)
  constructor
  · -- Slicewise honesty, transferred by `IntegrableOn.congr_fun`.
    intro z hz
    exact MeasureTheory.IntegrableOn.congr_fun (h.1 z hz)
      (fun θ hθ => hsq z θ hθ) measurableSet_Icc
  · -- Outer honesty, transferred by `IntegrableOn.congr_fun` and the slice identity.
    exact MeasureTheory.IntegrableOn.congr_fun h.2 (fun z _ => hslice z) measurableSet_Ici

end Work.FTS.EllipticEst.AngClean
