import Mathlib
import Submission.Work.Analysis.IonescuWainger.MajorArcs

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- Associativity of the heterogeneous `Lp` scalar multiplication
`Lp ℂ ⊤ μ × Lp ℂ q μ → Lp ℂ q μ` (whose exponent triple `⊤, q, q` is Hölder):
`m • (m' • g) = (m • m') • g` for `m m' ∈ L^∞` and `g ∈ L^q`.  This is the pointwise
identity `m(x) · (m'(x) · g(x)) = (m(x) · m'(x)) · g(x)`, transported through the
characterisation `Lp.coeFn_lpSMul` of the `Lp`-scalar-multiplication. -/
theorem lp_smul_smul_assoc {μ : Measure Circle} (m m' : Lp ℂ ⊤ μ) (g : Lp ℂ 2 μ) :
    m • (m' • g) = (m • m') • g := by
  refine Lp.ext ?_
  have h1 : (m • (m' • g) : Lp ℂ 2 μ) =ᵐ[μ] (⇑m • ⇑(m' • g) : Circle → ℂ) :=
    Lp.coeFn_lpSMul m (m' • g)
  have h2 : (m' • g : Lp ℂ 2 μ) =ᵐ[μ] (⇑m' • ⇑g : Circle → ℂ) :=
    Lp.coeFn_lpSMul m' g
  have h3 : ((m • m') • g : Lp ℂ 2 μ) =ᵐ[μ] (⇑(m • m') • ⇑g : Circle → ℂ) :=
    Lp.coeFn_lpSMul (m • m') g
  have h4 : (m • m' : Lp ℂ ⊤ μ) =ᵐ[μ] (⇑m • ⇑m' : Circle → ℂ) :=
    Lp.coeFn_lpSMul m m'
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Pi.smul_apply', hx1, hx2, hx3, hx4, smul_eq_mul, mul_assoc]

theorem circleMulOp_comp (m m' : MeasureTheory.Lp ℂ ⊤ circleMeasure) :
    (circleMulOp m).comp (circleMulOp m') = circleMulOp (m • m') := by
  apply ContinuousLinearMap.ext
  intro g
  simp only [ContinuousLinearMap.comp_apply, circleMulOp_apply]
  exact lp_smul_smul_assoc m m' g

end Work.Analysis.IonescuWainger
