import Mathlib
import Submission.Work.FatouCoord.Petal.repelling_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The reflected branch of the logarithm differs from the reflection of `Λ` by at most `4π`

`Λ w = log (-w) + π i` (see `Work.FatouCoord.Petal.Lambda`) is a branch of the logarithm on the
left half-plane, and it is *not* invariant under complex conjugation: reflecting `Λ z` differs
from evaluating `Λ` at the reflection of `z` by a quantity of modulus at most `4π`.

The mechanism is the standard one: `Λ z = log (-z) + π i`, `star (Λ z) = star (log (-z)) - π i`,
`Λ (star z) = log (star (-z)) + π i`, so the difference is
`star (log (-z)) - log (star (-z)) - 2 π i`.  The first two terms have the same real part
(`log ‖·‖` is conjugation invariant) and their imaginary parts are each bounded by `π` in modulus
(`-π < (log x).im ≤ π`), so their difference has modulus at most `2π`; together with `‖2π i‖ = 2π`
this gives the bound `4π`.  The bound is sharp, attained at positive real `z`.
-/

open Complex

namespace Work.FatouCoord.Flower

/-- `|(log u).im| ≤ π`: the imaginary part of `Complex.log` lies in `(-π, π]`. -/
private lemma abs_log_im_le_pi (u : ℂ) : |(Complex.log u).im| ≤ Real.pi :=
  abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_log_im u), Complex.log_im_le_pi u⟩

/-- Reflecting `log u` differs from `log` of the reflection of `u` by at most `2π`. -/
private lemma norm_conj_log_sub_le (u : ℂ) :
    ‖(starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)‖ ≤ 2 * Real.pi := by
  have hre : ((starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)).re = 0 := by
    simp [Complex.conj_re, Complex.log_re]
  have him : |((starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)).im|
      ≤ 2 * Real.pi := by
    simp only [Complex.sub_im, Complex.conj_im]
    rw [show -(Complex.log u).im - (Complex.log ((starRingEnd ℂ) u)).im
        = -((Complex.log u).im + (Complex.log ((starRingEnd ℂ) u)).im) by ring, abs_neg]
    calc |(Complex.log u).im + (Complex.log ((starRingEnd ℂ) u)).im|
        ≤ |(Complex.log u).im| + |(Complex.log ((starRingEnd ℂ) u)).im| := abs_add_le _ _
      _ ≤ Real.pi + Real.pi :=
          add_le_add (abs_log_im_le_pi u) (abs_log_im_le_pi ((starRingEnd ℂ) u))
      _ = 2 * Real.pi := by ring
  calc ‖(starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)‖
      ≤ |((starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)).re|
          + |((starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |((starRingEnd ℂ) (Complex.log u) - Complex.log ((starRingEnd ℂ) u)).im| := by
        rw [hre]; simp
    _ ≤ 2 * Real.pi := him

theorem star_Lambda_sub_le (z : ℂ) :
    ‖star (Work.FatouCoord.Petal.Lambda z) - Work.FatouCoord.Petal.Lambda (star z)‖
      ≤ 4 * Real.pi := by
  have h1 : star (Work.FatouCoord.Petal.Lambda z)
      = star (Complex.log (-z)) - (Real.pi : ℂ) * Complex.I := by
    simp only [Work.FatouCoord.Petal.Lambda]
    simp
    ring
  have h2 : Work.FatouCoord.Petal.Lambda (star z)
      = Complex.log (star (-z)) + (Real.pi : ℂ) * Complex.I := by
    simp only [Work.FatouCoord.Petal.Lambda]
    rw [show -(star z) = star (-z) by simp]
  have hkey : star (Work.FatouCoord.Petal.Lambda z) - Work.FatouCoord.Petal.Lambda (star z)
      = (star (Complex.log (-z)) - Complex.log (star (-z))) - (2 * (Real.pi : ℂ)) * Complex.I := by
    rw [h1, h2]; ring
  rw [hkey]
  simp only [Complex.star_def]
  calc ‖((starRingEnd ℂ) (Complex.log (-z)) - Complex.log ((starRingEnd ℂ) (-z)))
          - (2 * (Real.pi : ℂ)) * Complex.I‖
      ≤ ‖(starRingEnd ℂ) (Complex.log (-z)) - Complex.log ((starRingEnd ℂ) (-z))‖
          + ‖(2 * (Real.pi : ℂ)) * Complex.I‖ := norm_sub_le _ _
    _ ≤ 2 * Real.pi + 2 * Real.pi := add_le_add (norm_conj_log_sub_le (-z)) (by simp)
    _ = 4 * Real.pi := by ring

end Work.FatouCoord.Flower
