import Mathlib
import Submission.Work.FIArea4.S15expSumDefs

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# FI §15: the `e`-stratification arrays of the variance half

`S15pDng Pa X j d β ℓ u t` is the per-modulus §15 sum (without the coprimality filter).  FI
(15.1)–(15.2) stratify the pairs of the box by `e = (d, Re z₁) = (d, Re z₂)`: writing
`z = e ρ + i s` (only the *real* part is scaled by `e`), the modulus `d` is replaced by
`d/e` and the pair sum becomes a pair sum of the arrays `ρ ↦ β (eρ + is) · (s|e)` at the modulus
`4d/e`.  This module isolates the two ingredients that make that reindexing a *factorisation*:

* `S15zf` / `S15zfV`: the `z`-factors of the angular character `S15theta` and the phase
  `S15phase`, so that
  `S15theta ℓ z₁ z₂ * S15phase X j u t ((z₁,z₂),d)
     = S15zf u t ℓ z₁ * conj (S15zfV u t ℓ z₂) * (4X2^jd)^{-it}`
  (`S15theta_phase_factor`), the `d`-only factor being of modulus one;
* `S15strU` / `S15strV`: the stratum arrays `ρ + is ↦ β (eρ+is) (s|e) · S15zf (eρ+is)`.
-/

/-- The `z`-factor of the angular character and the phase: the part of
`S15theta ℓ z₁ z₂ · S15phase X j u t ((z₁,z₂),d)` belonging to `z₁`. -/
def S15zf (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (((z.im : ℝ) / (z.re : ℝ) : ℝ) : ℂ)))
    * ((((z.re.natAbs : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ)))
    * (Complex.exp (Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)))⁻¹

/-- The conjugate partner of `S15zf`: the part of `S15theta · S15phase` belonging to `z₂`, so that
`conj (S15zfV u t ℓ z₂)` is the `z₂`-factor. -/
def S15zfV (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (((z.im : ℝ) / (z.re : ℝ) : ℝ) : ℂ)))
    * ((((z.re.natAbs : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))))
    * (Complex.exp (Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)))⁻¹

/-- The stratum array of FI (15.2): for the stratum `e` the coefficient of `ρ + is` is
`β (eρ + is) · (s|e)`, and all `z`-dependence of the weight is carried by `S15zf` evaluated at the
*unscaled* point `eρ + is`. -/
def S15strU (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (z : GaussianInt) : ℂ :=
  let w : GaussianInt := ⟨(e : ℤ) * z.re, z.im⟩
  β w * ((jacobiSym z.im e : ℤ) : ℂ) * S15zf u t ℓ w

/-- The conjugate partner of `S15strU` (see `S15zfV`). -/
def S15strV (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (z : GaussianInt) : ℂ :=
  let w : GaussianInt := ⟨(e : ℤ) * z.re, z.im⟩
  β w * ((jacobiSym z.im e : ℤ) : ℂ) * S15zfV u t ℓ w

end

end Work.FIArea4
