import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

/-- The `m`-th angular mode coefficient of `Φ`:
`modeCoeff Φ m z = ∫_θ Φ(z,θ)·e_m(θ)·cos θ dθ` (the `e_m` are the Dirichlet eigenfunctions of
`Lzero`, orthogonal with respect to the weight `cos θ dθ`). -/
def modeCoeff (Φ : ℝ → ℝ → ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

/-- The weight `z^{(5-α)/α} · cos θ` of the self-adjointness pairing of `bslOp α`. -/
def bslWeight (α : ℝ) (p : ℝ × ℝ) : ℝ := p.1 ^ ((5 - α) / α) * Real.cos p.2

/-- The angular weight `sin(2θ)^{-(2+η)}` of the `i = 0` slice term of `HkIntegrand`
(`η = 99/100`). -/
def rootWeight (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The `z`-slice energy of `Φ` against the weight `sin(2θ)^{-(2+η)}`. -/
def sliceEnergy (Φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2 * rootWeight θ



/-- The radial part of `bslOp` applied to a pure `z`-function (the Euler operator). -/
def radOp (α : ℝ) (ρ : ℝ → ℝ) (z : ℝ) : ℝ :=
  α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z

/-! ## The shrinking angular cut-off

The weak identity is proved by pairing `bslOp α Φ = 0` against the *compactly supported* test
functions `ρ(z)·(χ_n(θ)·e_m(θ))` (so that the proved self-adjointness identity
`Work.EllipticEst.ModalSolution.bslOp_ibp` applies) and letting `n → ∞`: `χ_n → 1` in the
interior, while the two boundary layers contribute `O(δ_n^{(1+η)/2})`.

`δ_n = 1/(n+1)`; `χ_n` is `1` on `[2δ_n, π/2 - 2δ_n]` and `0` off `[δ_n, π/2 - δ_n]`. -/

/-- The shrinking length scale `δ_n = 1/(n+1)`. -/
def delta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The shrinking angular cut-off: smooth, `1` on `[2δ_n, π/2-2δ_n]`, `0` off
`[δ_n, π/2-δ_n]`. -/
def angCut (n : ℕ) (θ : ℝ) : ℝ :=
  Real.smoothTransition (θ / delta n - 1) * Real.smoothTransition ((π / 2 - θ) / delta n - 1)

/-- The angular layer on which `angCut n` is not (yet) equal to `1`. -/
def layer (n : ℕ) : Set ℝ :=
  Set.Ioo 0 (2 * delta n) ∪ Set.Ioo (π / 2 - 2 * delta n) (π / 2)

/-- The indicator of the layer, as a function. -/
def layerInd (n : ℕ) (θ : ℝ) : ℝ := Set.indicator (layer n) (fun _ => (1 : ℝ)) θ

@[simp] lemma modeCoeff_apply (Φ : ℝ → ℝ → ℝ) (m : ℕ) (z : ℝ) :
    modeCoeff Φ m z
      = ∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := rfl

@[simp] lemma bslWeight_apply (α z θ : ℝ) :
    bslWeight α (z, θ) = z ^ ((5 - α) / α) * Real.cos θ := rfl

lemma eFam_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_zero, Real.sin_zero, one_mul,
    Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]

/-- The angular eigen-relation, in the `Lzero1` form used by the separable expansion of
`bslOp`. -/
lemma Lzero1_eFam (m : ℕ) {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ :=
  Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 1

end Work.FTS.StrongEps.EComparison
