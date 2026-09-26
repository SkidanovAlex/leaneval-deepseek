import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Kernels.Theorem31

/-!
# Sample values of the generating functions `F = Fgen K` and `F̃ = Ftgen K̂`

CKMRV (*Universal optimality of the E8 and Leech lattices and interpolation formulas*,
Ann. of Math. 196 (2022), Section 5) attach to a kernel `K` on `ℍ × ℍ` the generating
function (5.2)

  `F(τ, r) = e^{π i τ r²} + 4 sin²(π r² / 2) ∫_0^∞ K(τ, it) e^{-π r² t} dt`,

and to the "hatted" kernel `K̂` the companion function

  `F̃(τ, r) = 4 sin²(π r² / 2) ∫_0^∞ K̂(τ, it) e^{-π r² t} dt`,

see `Work.Kernels.Fgen`, `Work.Kernels.Ftgen` and `Work.Kernels.kernelTransform`.

At a sample radius `r_m = √(2m)` with `m ∈ ℕ` the sine factor vanishes,
because `π r_m² / 2 = π m`, so the integral term drops out.  Consequently

  `F(τ, √(2m)) = e^{π i τ (2m)} = e^{2 π i m τ} = dirichletTerm m τ`,
  `F̃(τ, √(2m)) = 0`,

which are the normalisation conditions `value_F`, `value_Ftilde` of
`Work.FE.InterpolationSolution` for the constructed pair `(Fgen K, Ftgen K̂)`.

Nothing here depends on the particular kernel: the vanishing comes from the sine factor
in front of the integral.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

/-- The sample radius `rate m = √(2m)` squares to `2m`, as a complex number. -/
lemma rate_sq_cast (m : ℕ) : (rate m : ℂ) ^ 2 = 2 * (m : ℂ) := by
  have hrR : (rate m) ^ 2 = (2 * (m : ℝ)) := by
    rw [rate]; exact Real.sq_sqrt (by positivity)
  rw [← Complex.ofReal_pow, hrR]
  push_cast
  ring

/-- The sine factor in `kernelTransform` vanishes at the sample radius `rate m = √(2m)`,
since `π (rate m)² / 2 = π m`. -/
lemma sin_rate_sq_div_two (m : ℕ) :
    Complex.sin (Real.pi * (rate m : ℂ) ^ 2 / 2) = 0 := by
  rw [rate_sq_cast m,
    show Real.pi * (2 * (m : ℂ)) / 2 = (m : ℂ) * (Real.pi : ℂ) by ring]
  exact Complex.sin_nat_mul_pi m

/-- The Gaussian exponent at the sample radius: `π i τ (rate m)² = 2 π i m τ`. -/
lemma gauss_exponent_rate (τ : ℍ) (m : ℕ) :
    Real.pi * Complex.I * (τ : ℂ) * (rate m : ℂ) ^ 2
      = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ : ℂ) := by
  rw [rate_sq_cast m]; ring

/-- **Sample values of the generating functions.**  For any kernel `K` and any "hatted"
kernel `K̂`, at the sample radius `r_m = √(2m)` (`m ≥ 1`) one has
`Fgen K τ r_m = dirichletTerm m τ` and `Ftgen K̂ τ r_m = 0`: the sine factor in
`kernelTransform` vanishes, and the Gaussian term evaluates to `e^{2πimτ}`. -/
theorem KernelSampleValues (K Khat : ℍ → ℍ → ℂ) (τ : ℍ) (m : Set.Ici (1 : ℕ)) :
    Work.Kernels.Fgen K τ (rate m.1) = dirichletTerm m.1 τ ∧
    Work.Kernels.Ftgen Khat τ (rate m.1) = 0 := by
  constructor
  · unfold Work.Kernels.Fgen Work.Kernels.kernelTransform Work.Kernels.gaussTerm dirichletTerm
    rw [sin_rate_sq_div_two m.1, gauss_exponent_rate τ m.1]
    ring
  · unfold Work.Kernels.Ftgen Work.Kernels.kernelTransform
    rw [sin_rate_sq_div_two m.1]
    simp

end

end Work.FunctionalEquations
