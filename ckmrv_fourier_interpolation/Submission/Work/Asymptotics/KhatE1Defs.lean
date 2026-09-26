import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs

/-!
# The `E¹`-coefficient combinations of the funnel tail of `K̂`

The sharp funnel bound `Work.Asymptotics.Khat_funnel_tail_sharp_core` asks for one power of
`q(τ) = qParamFun τ` beyond the sharp individual estimates.  Expanding the two exact
decompositions

* `K₊^{(8)} - 𝒢₊^{(8)} = tailC⁻¹(Φ₁+Φ₂+Φ₃)` (`Compact.KPlus8_sub_Gplus8_decomp`),
* `3456π(K₋^{(d)} - 𝒢₋^{(d)}) = -(Sh)⁻¹(br + Sh·br0)` (`Compact.tail_identity`),

in powers of `E(z) = Ept z`, the coefficient of `E(z)^1` of the relevant bracket is (up to an
explicit constant) `E1combo8` resp. `E1combo24`, and the target is implied by the statement
that these coefficients are `O(‖q(τ)‖ (scale τ)^N)` (plus the matching of the even
coefficients).  The two bound lemmas are delegated from
`Submission/Work/Asymptotics/Khat_funnel_tail_sharp_core.lean`.
-/

namespace Work.Asymptotics

open UpperHalfPlane

/-- **(d = 8) the `E¹`-coefficient combination.** It is `(1/24)` times the coefficient
`Compact.R8_p0` of `Ept z` in the reference bracket `br8ref + Sh·br0`:
`j(ψ₄ - ψ₂E₆/E₄) + 576(2E₄ - ψ₄)`. -/
noncomputable def E1combo8 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ *
      (Work.Kernels.psi4 ℓ τ
        - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
    + 576 * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ)

/-- **(d = 24) the `E¹`-coefficient combination.** It is `KMFDDefs.kmfd_c1`, the coefficient of
`Ept z` in the reference bracket `kmfd_BR` of the `d = 24` funnel analysis. -/
noncomputable def E1combo24 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  27648 * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
    - 24 * (Work.Kernels.jInvariantFun τ * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))
    + 24 * (Work.Kernels.jInvariantFun τ * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ))
    - 20570112 * Work.Kernels.DeltaFun τ
    + 15744 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
    - 29568 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)

/-- The deviation of `K̂` from its cusp model `Ĝ = (𝒢₊ - 𝒢₋)/2`. -/
noncomputable def Kdev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  Work.Kernels.Khat ℓ d τ z
    - (Work.Asymptotics.Compact.Gplus d τ z - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2

/-- The part of the deviation invariant under the translation `z ↦ z + 1` (equivalently: the
part whose expansion in `E(z) = Ept z` has only even powers). -/
noncomputable def KdevEven (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (Kdev ℓ d τ z + Kdev ℓ d τ ((1 : ℝ) +ᵥ z)) / 2

/-- The part of the deviation anti-invariant under `z ↦ z + 1`; its expansion in `E(z)` has
only odd powers, the first being the `E¹`-coefficient combination `E1combo8`/`E1combo24`. -/
noncomputable def KdevOdd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (Kdev ℓ d τ z - Kdev ℓ d τ ((1 : ℝ) +ᵥ z)) / 2

end Work.Asymptotics
