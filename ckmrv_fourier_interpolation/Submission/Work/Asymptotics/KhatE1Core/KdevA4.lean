import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Br8refExpand

/-!
# The `E(z)⁴`-coefficient `KdevA4` of the sharp funnel residual

Writing `e = Ept z`, the residual `Wres = Kdev8Bracket - 2·KdevE2·e²` has an expansion
`Wres = Σ_{k≥3} a_k e^k`, and its `e⁴`-coefficient is

  `a₄ = tailC⁻¹·Phi4 + (3456π)⁻¹·( b₃ + [Tref8]_{e⁴} + [Dev8Sum]_{e⁴} )`,

where

* `Phi4` is the `e⁴`-coefficient of the `K₊`-correction `Φ₁+Φ₂+Φ₃` (transcribed from the cusp
  expansions of the `z`-atoms; `ClearedCombos`/`PhiCleared` supply the cleared identity);
* `b₃ = Xc·R8_q3 + R8_p3` is the `e⁴`-coefficient of `e(R8 - R8_p0)`;
* `[Tref8]_{e⁴} = β₄ + (j(τ)-720)·β₂` where the `βᵢ` are the explicit coefficients of
  `br8ref` (`br8ref_expand`);
* `[Dev8Sum]_{e⁴} = ((j(τ)-720)² - 179280 - 24j(τ))·β₀ + Dev4`, `Dev4 = [Dev8Raw]_{e⁴}`;

and `-2·KdevE2·e²` contributes nothing at order `e⁴` (`KdevE2` is a `z`-polynomial, independent
of `q_z`), while `a₂ = 0` is the proved `Kdev8BracketE2_eq_two_KdevE2`.

This is the `k = 4` analogue of `KhatE1.KdevA3`; the bound required of `KdevA4` is
`‖KdevA4‖ ≤ C·(scale τ)^N(1+t)^M`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- The `E(z)⁴`-coefficient of the `K₊`-correction `Φ₁+Φ₂+Φ₃`, in the form in which it comes out
of the cusp expansions (`C = 6i/π`, `τ` = `(τ : ℂ)`, `E2(τ)`, `E4(τ)`, `E6(τ)`, `j(τ)` and
`E₁₄(τ)/Δ(τ)`). -/
noncomputable def Phi4 (τ z : ℍ) : ℂ :=
    - (67392 : ℂ) * ((z : ℂ) * (z : ℂ) * E6Fun τ * (τ : ℂ))
    - (417312 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)))
    - (744 : ℂ) * ((z : ℂ) * (z : ℂ) * (E14Fun τ / DeltaFun τ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)
    - (787536 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    - (1 : ℂ) * ((z : ℂ) * (z : ℂ) * jInvariantFun τ * (E14Fun τ / DeltaFun τ) * (τ : ℂ) * E2Fun τ * E2Fun τ)
    - (2016 : ℂ) * ((z : ℂ) * E6Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (984 : ℂ) * (E6Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (3504 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * (τ : ℂ) * E2Fun τ)
    - (1728 : ℂ) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1 : ℂ) * ((z : ℂ) * (z : ℂ) * E6Fun τ * jInvariantFun τ * jInvariantFun τ * (τ : ℂ))
    - (2 : ℂ) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    - (1 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)))
    + (122256 : ℂ) * ((z : ℂ) * E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (834624 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (τ : ℂ) * E2Fun τ)
    + (744 : ℂ) * ((z : ℂ) * (z : ℂ) * (E14Fun τ / DeltaFun τ) * (τ : ℂ) * E2Fun τ * E2Fun τ)
    - (55440 : ℂ) * (E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (393768 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    + (1 : ℂ) * ((z : ℂ) * (z : ℂ) * jInvariantFun τ * (E14Fun τ / DeltaFun τ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)
    + (1032 : ℂ) * ((z : ℂ) * (z : ℂ) * E6Fun τ * jInvariantFun τ * (τ : ℂ))
    + (3456 : ℂ) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (1752 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)))
    + (2 : ℂ) * ((z : ℂ) * E6Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (1 : ℂ) * (E6Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (2 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (τ : ℂ) * E2Fun τ)
    + (1 : ℂ) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))

/-- The `e⁴`-coefficient of `Dev8Raw` (the seven raw `z`-atom deviations of `brMinus 8`). -/
noncomputable def Dev4 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  - 20736 * E4Fun τ
  + 468052992 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ
  + 107039232 * psi4 ℓ τ
  + 79488 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
  - 79488 * (jInvariantFun τ * psi4 ℓ τ)

/-- **The `E(z)⁴`-coefficient of the sharp funnel residual, as an unscaled numerator.**

This is `3456π · KdevA4`; keeping the factor `3456π` outside avoids a scalar cancellation in the
algebra of `KdevA4_eq`.  It equals

  `b₃ + [Tref8]_{e⁴} + [Dev8Sum]_{e⁴}`  with  `b₃ = [E(z)·R8]_{e⁴} = Xc·R8_q3 + R8_p3`,

written in the expansion of `br8ref` (`β₄ + (j-720)·β₂ = b₃`). -/
noncomputable def KdevA4num (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ)) * Work.Asymptotics.Compact.tailC⁻¹ * Phi4 τ z
    + ((10948608 * E4Fun τ + 19906560 * psi4 ℓ τ
                + 61056 * (jInvariantFun τ * psi4 ℓ τ)
                - 61056 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
              + (jInvariantFun τ - 720)
                * (-41472 * E4Fun τ + 912384 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ
                  + 870912 * psi4 ℓ τ
                  + 1152 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
                  - 1152 * (jInvariantFun τ * psi4 ℓ τ)))
            + (((jInvariantFun τ - 720) ^ 2 - 179280 - 24 * jInvariantFun τ)
                * (-3456 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ + 1728 * psi4 ℓ τ))
            + Work.Asymptotics.KhatE1Core.Dev4 ℓ τ z)

/-- **The `E(z)⁴`-coefficient of the sharp funnel residual.** -/
noncomputable def KdevA4 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * KdevA4num ℓ τ z

end

end Work.Asymptotics.KhatE1Core

/-!
## State of the reduction (for the next stretch)

`3456π·KdevA4` has been reduced symbolically (own engine, `.kdevdir/readoff.py`) by iterating

* `ψ₄ → Φ + P` (with `Φ := ψ₄ - ψ₂E₆/E₄`, `P := ψ₂E₆/E₄`), and
* `j(τ)·Φ → E1combo8 - 1152E₄(τ) + 576ψ₄`

to a normal form of **37 monomials** in the basis `z, τ, C = 6i/π, E2(τ), E4(τ), E6(τ), j(τ),
Φ, P, E1combo8, Xc, E₁₄(τ)/Δ(τ)`.  Its large (i.e. `q_τ^{-1}`-or-worse) part is

  `594521856·E₄ - 211382784·Φ - 211382784·P - 516096·E1combo8
     - 1360862208·Xc·E₄ + 40808448 + 576·j·E1combo8
     + j·(5971968·Xc·E₄ - 705024·E₄ - 1327104·P) - 3456·j²·Xc·E₄ + 1728·j²·P`,

the rest being `O((1+t)² scale^2)`.  Two facts to carry forward:

1. `576·j·E1combo8` is *small* (`JmulBig.jmul_big` + `E1combo8_bound`), and `Φ` is small
   (`O(q_τ scale^N)`), so those two monomials are already in boundable shape; the `j·E₄`,
   `j·P`, `j·Xc·E₄` and the `j²` monomials are the ones that must cancel further.
2. The surviving `-3456·j²·Xc·E₄ + 1728·j²·P` is a *red flag*: `j²P` is `q_τ^{-2}`-sized, whereas
   `a₄` must be `O(scale^N(1+t)^M)` (it is `c₄/Δ(τ)` with `c₄ = O(q_τ)`).  Since `j²P·e⁴ =
   (j q_z)²P` *is* small, a genuine `j²P` can only appear bundled with a compensating multiple of
   `q_z`-powers; the earlier independent numerical fit (`_kdevdir/NOTES.md`, §"a_4") matched the
   `z²`- and `z`-parts of this extraction to 12 digits and disagreed only in the `z⁰`-constant —
   i.e. precisely in the place where a spurious `z`-free `j²P`-like term would show up.  So the
   next step is to resolve that: either the `j²`-block cancels against the `z`-free block through
   an identity not yet applied (candidate: `E₆/E₄ = 1 - 744q_τ + O(q_τ²)` or the `q_z`-expansion
   of `KdevE2`), or one of the `R8_p3`/`Dev*` coefficients is mis-transcribed.

The other prover-side facts used here: `R8_p3` contains `-1152·j²·ψ₄ + 1152·j·(ψ₂E₁₄/Δ)`, which is
`-1152·j²·Φ` (the `j²P` parts cancel) — this is why the reduction must treat `ψ₄` and `P`
together.
-/
