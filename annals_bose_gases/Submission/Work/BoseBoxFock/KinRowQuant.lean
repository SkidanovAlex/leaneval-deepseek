import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- The **full lattice momentum** `(2π/ℓ)n = ℓ⁻¹ • vec n` (`kmomLab` without the `Lab N`
truncation). -/
def kmomInt (ℓ : ℝ) (n : Fin 3 → ℤ) : ℝ³ := ℓ⁻¹ • Work.BoseB4.vec n

/-- The **box-Fourier coefficient** of `ψ` against the corpus's localised plane wave
`qVec ℓ k = e^{ik·}χ_Λ − χ̂(ℓk)1_Λ`.  (This is the quantity in the target's left-hand side.) -/
def qCoeff (ℓ : ℝ) (k : ℝ³) (ψ : ℝ³ → ℝ) : ℂ :=
  ∫ z, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k z) * (ψ z : ℂ)

/-- The free `√−Δ` kinetic form of the windowed mean-free state: `bsOneBody` at the symbol
`r ↦ r`.  (The `F = fsKinCoeff c` cases are the target's right-hand side.) -/
def sqrtKinWord (ℓ : ℝ) (ψ : ℝ³ → ℝ) : ℝ := Work.BSKinetic.bsOneBody ℓ (fun r => r) 0 ψ

/-- The **full-lattice first moment** of the model's truncated kinetic row, i.e.
`Σ_k ‖k‖·ℓ⁻³·|⟨qVec k, ψ⟩|²` over the whole lattice `(2π/ℓ)ℤ³`. -/
def firstMomentSum (ℓ : ℝ) (ψ : ℝ³ → ℝ) : ℝ :=
  ∑' n : Fin 3 → ℤ, ‖kmomInt ℓ n‖ * ((ℓ ^ 3)⁻¹ * ‖qCoeff ℓ (kmomInt ℓ n) ψ‖ ^ 2)

end Work.BoseBoxFock
