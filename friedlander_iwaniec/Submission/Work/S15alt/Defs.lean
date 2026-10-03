import Mathlib
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIPlan.Interface

/-!
# `Work.S15alt.Defs`: the vocabulary of the exact Möbius removal of the pair coprimality

The per-modulus §15 sum `S15pD` carries the *pair* condition `GaussCoprime z₁ z₂` of FI (15.2).
That condition is not a condition on the classes of the class Cauchy–Schwarz, and dropping it is
not an upper bound; it has to be removed **exactly**, by Möbius inversion, before the class
Cauchy–Schwarz is applied (`Work.FIArea4.coprime_pair_sum_eq_moebius`, with the indicator supplied
by `Work.FIArea4.gaussMoebius_coprime_indicator`).

This module collects the definitions in which that removal is stated, so that statements about it
do not mention `Decidable` instances:

* `coprimeInd` — the coprimality indicator `[GaussCoprime z₁ z₂]` as a `ℂ`-valued function;
* `mobSum W μ z₁ z₂` — the Möbius divisor sum `Σ_{w ∈ W, w ∣ z₁, w ∣ z₂} μ w` (which, for the
  right `(W, μ)`, equals `coprimeInd z₁ z₂`);
* `moebiusRestricted Pa X j d β ℓ u t w` — the `w`-restricted per-modulus §15 sum, i.e. the
  per-modulus sum with the coprimality replaced by the *per-element* divisibility conditions
  `w ∣ z₁`, `w ∣ z₂`; this set of pairs is a product set, hence the class Cauchy–Schwarz
  (`Work.FIArea4.S15red.pDng_e_le_EvarG`, applied to the array `z ↦ if w ∣ z then β z else 0`)
  does apply to it.
-/

namespace Work.S15alt

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The coprimality indicator `[GaussCoprime z₁ z₂]` as a `ℂ`-valued function. -/
noncomputable def coprimeInd (z1 z2 : GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime z1 z2 then 1 else 0

/-- The Möbius divisor sum `Σ_{w ∈ W, w ∣ z₁, w ∣ z₂} μ w` of the coprimality indicator. -/
noncomputable def mobSum (W : Finset GaussianInt) (μ : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℂ :=
  ∑ w ∈ W, (if w ∣ z1 ∧ w ∣ z2 then μ w else 0)

/-- The `w`-restricted per-modulus §15 sum: the per-modulus summand of `S15pD` in which the
pair coprimality `GaussCoprime z₁ z₂` has been replaced by the per-element conditions
`w ∣ z₁`, `w ∣ z₂`. -/
noncomputable def moebiusRestricted (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (w : GaussianInt) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if w ∣ z1 ∧ w ∣ z2 ∧ X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ 0 < Work.FIPlan.absDelta z1 z2
      then Work.FIArea4.S15coef β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
        * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0)

/-- The `w`-restricted coefficient array `z ↦ (if w ∣ z then β z else 0)`.  For `w` a Gaussian
integer this is again an `IsPrimBoxCoeff` whenever `β` is (the support only shrinks), so the class
Cauchy–Schwarz of `Work.FIArea4.S15red.pDng_e_le_EvarG` applies to it verbatim. -/
noncomputable def restrArray (β : GaussianInt → ℂ) (w : GaussianInt) : GaussianInt → ℂ :=
  fun z => if w ∣ z then β z else 0

end Work.S15alt
