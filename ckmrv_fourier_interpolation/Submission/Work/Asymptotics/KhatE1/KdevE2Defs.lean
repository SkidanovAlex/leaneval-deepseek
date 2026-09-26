import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Residues.KMinusCuspDefs

/-!
# The explicit `E(z)²`-coefficient of the funnel deviation `K̂^{(8)} - 𝒢̂^{(8)}`

Write `E(z) = Ept z = e^{πiz}` (`‖E(z)‖ = e^{-π z.im}`).  The deviation

  `Kdev ℓ 8 τ z = K̂^{(8)}(τ,z) - (𝒢₊^{(8)}(τ,z) - 𝒢₋^{(8)}(τ,z))/2`

is, as a function of `z` on the funnel, a series `Σ_{k ≥ 1} a_k(τ,z) E(z)^k` whose
coefficients `a_k` are polynomials in `z` (of degree at most two) with coefficients built from
the `τ`-atoms.

The two exact decompositions of the workspace give the coefficients explicitly:

* `K₊^{(8)} - 𝒢₊^{(8)} = tailC⁻¹ (Φ₁ + Φ₂ + Φ₃)` (`Compact.KPlus8_sub_Gplus8_decomp`), whose
  expansion in powers of `E(z)` has only **even** powers (all three `Φᵢ` are functions of
  `q(z) = E(z)²`): the `E(z)¹`-coefficient vanishes, and the `E(z)²`-coefficient is
  `KdevE2plus` below (using only the *exact* first coefficients
  `[E₂(z)-1]_{E²} = -24`, `[E₄]_{E²} = 240`, `[E₆]_{E²} = -504`, `[Δ]_{E²} = 1`);
* `-(K₋^{(8)} - 𝒢₋^{(8)})/2 = (6912π)⁻¹ (Sh)⁻¹(br + Sh·br0)`
  (`Compact.tail_identity`), whose `E(z)^k`-coefficient is `[R8]_{k-1}`
  (`Compact.Tref8_eq : Tref8 = E(z)·R8`, plus the deviation `Dev8Sum = O(E³)`), so the
  `E(z)²`-coefficient is `KdevE2minus` below.

The `E(z)¹`-coefficient of the total deviation is therefore `E1combo8/(288π)`
(`R8_p0_eq_e1combo8` together with the vanishing of the `K₊`-part), and the content of the
sharp funnel remainder statement is that the `E(z)²`-coefficient is `O(‖q(τ)‖ (scale τ)^N)`
and that the remaining terms are dominated.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- The `E(z)²`-coefficient of `(K₊^{(8)} - 𝒢₊^{(8)})/2`, i.e. of the `K₊`-part of the
deviation `K̂ - 𝒢̂`. -/
noncomputable def KdevE2plus (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (1 / (2 * Work.Asymptotics.Compact.tailC)) *
    ( -24 * ((τ : ℂ) * Work.Kernels.E6Fun τ *
          (-2 * (z : ℂ) ^ 2 + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
        + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)
      - Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 / Work.Kernels.DeltaFun τ
      - ((τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
            * (Work.Kernels.jInvariantFun τ - 240)
          - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ *
              ((z : ℂ) ^ 2 - 6 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
              * (Work.Kernels.jInvariantFun τ - 984)) )

/-- The `E(z)²`-coefficient of `-(K₋^{(8)} - 𝒢₋^{(8)})/2`, i.e. of the `K₋`-part of the
deviation. -/
noncomputable def KdevE2minus (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (1 / (6912 * (Real.pi : ℂ))) *
    ( Work.Asymptotics.Compact.Xc ℓ z *
        (3400704 * Work.Kernels.E4Fun τ
          - 3456 * (Work.Kernels.jInvariantFun τ * Work.Kernels.E4Fun τ))
      + (-41472 * Work.Kernels.E4Fun τ
          - 373248 * Work.Kernels.psi4 ℓ τ
          + 1152 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
          + 576 * (Work.Kernels.jInvariantFun τ * Work.Kernels.psi4 ℓ τ)) )

/-- The total `E(z)²`-coefficient of the deviation. -/
noncomputable def KdevE2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  KdevE2plus ℓ τ z + KdevE2minus ℓ τ z

/-- The `E(z)¹`-coefficient of the deviation: `E1combo8/(288π)`. -/
noncomputable def KdevE1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Asymptotics.E1combo8 ℓ τ / (288 * (Real.pi : ℂ))

end

end Work.Asymptotics.KhatE1
