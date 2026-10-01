/-
# ZeroFreeTables — HBTable7_defs85

The certificate for **Heath-Brown's Lemma 8.5** (the five-term positivity of HB (6.3)/(6.4)) in the
shape in which it is consumed by the degenerate case `χ₂⁴ = χ₀` of Table 7.

## Why a second certificate

HB's Table 7 is read off the *third method* (HB (8.11), the six-term positivity
`(χ₀+χ₁)(k + Re(χ₂ n^{-iγ₂}))² ≥ 0`), which is evaluated at `Re s = β₂`.  Evaluating that
positivity at `Re s = β₂` requires knowing that the zeros of the four characters
`χ₂, χ₁χ₂, χ₂², χ₁χ₂²` inside the windows of HB Lemma 5.2 (of height `|Im s| + δ`, i.e.
`|γ₂| + δ` and `2|γ₂| + δ`) lie to the left of `s`; this is exactly HB's `λ₂ ≤ λ₀` /
`χ₂⁴ ≠ χ₀` discussion (p. 47).  For the characters with `χ₂⁴ = χ₀` HB uses instead the
*first method*, Lemma 8.5, whose constant is `3/8` when every one of the four characters
`χ₁, χ₂, χ₁χ₂, χ₁χ₂⁻¹` has order dividing `4` (so that HB Lemma 2.5 gives `φ = 1/4`, i.e.
`c = φ/2 = 1/8`, for each of them):

`0 ≤ F(-λ₂) - F(λ₁-λ₂) - F(0) + f(0)(3/8 + ε)`  (HB Lemma 8.5 with `ψ ≤ 3/8`),

and its left hand side is increasing in `λ₁` and in `λ₂`, so that its *strict failure* at the row
values `(b, c)` forces `λ₂ > c` — the same extraction as for the third method
(`HBTable7_extract`).

## The certificate

`CertRow85 b c lam ε` is the strict failure of HB Lemma 8.5's inequality at `λ₁ = b`, `λ₂ = c`,
with the test function of HB Lemma 7.1 at `θ = π/4` (so `f(0) = 2λ(π-3)`, `F(z) = tfF lam z`):

`F(-c) - F(b-c) - F(0) + 2λ(π-3)(3/8 + 4ε) < 0`.

The engine `Work.LinnikAreas.OtherCharRepel.lemma85pt` (with `c = 1/8`) concludes
`0 ≤ J₂ - J₁ - J₀ + f(0)(3·(1/8) + 4ε)`, i.e. exactly `f(0)(3/8 + 4ε)`; this is why the `ε` in
`CertRow85` enters with the coefficient `4`.

The numerical content is much softer than for `CertRow` (`HBTable7_defs`): the margins here are
`8·10⁻³ … 3·10⁻²` with rational `λ` near `1` (e.g. `λ = 1.06` for the row `(0.10, 2.76)`,
`λ = 0.93` for the row `(0.745, 0.745)`); the certificate is proved at `ε = 0` and upgraded to a
tiny `ε > 0` by monotonicity in `ε` (the left hand side is affine with slope `8λ(π-3) > 0`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- The certificate of one row `(b, c)` for **HB Lemma 8.5**: the left hand side of
`F(-λ₂) - F(λ₁-λ₂) - F(0) + f(0)(3/8 + ε)` at `(λ₁, λ₂) = (b, c)` is *strictly negative*. -/
def CertRow85 (b c lam ε : ℝ) : Prop :=
  0 < lam ∧
    tfF lam (-c) - tfF lam (b - c) - tfF lam 0
      + (2 * lam * (Real.pi - 3)) * ((3 : ℝ) / 8 + 4 * ε) < 0

end Work.ZeroFreeTables
