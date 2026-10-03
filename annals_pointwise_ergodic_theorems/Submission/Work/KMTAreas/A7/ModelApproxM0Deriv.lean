/-
# The differentiated symbol difference `M₀` of Proposition `mod-approx`

The paper's proof of Proposition `mod-approx` bounds the *derivatives*
`∂^{j₁}_{ξ₁}∂^{j₂}_{ξ₂} M₀` for `0 ≤ j₁,j₂ ≤ 2` and then converts the symbol bound into the
`ℓ^p` operator bound through Lemma `crude-mult`(ii) (with `r₁ = N⁻¹`, `r₂ = N^{-d}`), i.e. -- in
the kernel language used here -- through the decay `|K(a,b)| ≲ r₁⟨r₁a⟩^{-2}r₂⟨r₂b⟩^{-2}` of the
coefficient kernel and `Work.KMTAreas.A7.BilinOpLp`.  This module fixes the differentiated
objects: the `ξ`-derivatives bring down the factors `2πi n`, `2πiP(n)` in the discrete average and
`2πiNt`, `2πiP(Nt)` in the oscillatory integral.  The estimate proved for them is the *sharp* one
(no factor `2^{O(s)}`, `s` = continuous scale), cf. `NOTES_A7_ModelApproxCore.md` §2.1.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- The `j`-th `(ξ₁,ξ₂)`-derivative of a summand of the discrete average, i.e. the summand of
`∂^{j₁}_{ξ₁}∂^{j₂}_{ξ₂} E_{n∈[N]}e(α₁n+α₂P(n))e(ξ₁n+ξ₂P(n))`. -/
noncomputable def momPhaseDeriv (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) (n : ℤ) (j₁ j₂ : ℕ) : ℂ :=
  momPhase P N α₁ α₂ ξ₁ ξ₂ n
    * (2 * Real.pi * Complex.I * (n : ℂ)) ^ j₁
    * (2 * Real.pi * Complex.I * ((PevalR P (n : ℝ) : ℝ) : ℂ)) ^ j₂

/-- The `j`-th `(ξ₁,ξ₂)`-derivative of the oscillatory integral `m̃_{N,ℝ}`. -/
noncomputable def mTildeDeriv (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) : ℂ :=
  ∫ t in (1 / 2 : ℝ)..1,
    ee (ξ₁ * (N : ℝ) * t + ξ₂ * PevalR P ((N : ℝ) * t))
      * (2 * Real.pi * Complex.I * (((N : ℝ) * t : ℝ) : ℂ)) ^ j₁
      * (2 * Real.pi * Complex.I * ((PevalR P ((N : ℝ) * t) : ℝ) : ℂ)) ^ j₂

/-- The `j`-th `(ξ₁,ξ₂)`-derivative of the symbol difference `M₀`. -/
noncomputable def M0deriv (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ ξ₁ ξ₂ (n : ℤ) j₁ j₂
    - mZ P q α₁ α₂ * mTildeDeriv P N ξ₁ ξ₂ j₁ j₂

end

end Work.KMTAreas.A7
