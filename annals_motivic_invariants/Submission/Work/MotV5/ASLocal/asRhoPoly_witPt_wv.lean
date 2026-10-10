import Mathlib
import Submission.Work.MotAS.AsRhoDefs
import Submission.Work.MotAS.WitPt
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotV5.ASLocal.asRhoPoly_witPt_data
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASLocal.asRhoPoly_witPt_value`

`asRhoPoly K a b g` is the `0`-th component of the inverse AS quadro-cubic map `kleinRAS` evaluated
on the ruling line `asRuleQW · 1` over the variable point `X 0, …, X 4`.  Substituting the witness
point `witPt a b` of `Work.MotAS.WitPt` (a point of the AS Klein curve modulo `X ^ 5 - X - C g`)
gives a polynomial in `K[X]`; the statement asks for its remainder modulo the monic
`X ^ 5 - X - C g` to be nonzero.

The witness point is substituted componentwise: `asWv0, …, asWv4 : Polynomial K` are the five
components of the ruling vector at the witness point (`asWv4 = 0`, the ruling lines lie in
`{z₄ = 0}`).  The value is then `kleinRAS0 a b g ![asWv0, …, asWv4]`, an explicit polynomial whose
remainder modulo `X ^ 5 - X - C g` is the explicit `PhiP` of the data module; `PhiP ≠ 0` is the
Bézout certificate `bezout`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotV5.ASLocal

open MvPolynomial Polynomial

/-- The `0`-th component of the ruling vector `asRuleQW · 1` at the witness point. -/
noncomputable def asWv0 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (4 * a ^(6:ℕ) * g + 2 * a ^(5:ℕ) * b * g + 3 * a * b ^(5:ℕ) * g + 4 * b ^(6:ℕ) * g + 2 * a ^(6:ℕ) + a ^(5:ℕ) * b + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 4 * a ^(2:ℕ) * b ^(4:ℕ) + 2 * a * b ^(5:ℕ) + 4 * b ^(6:ℕ))
  + Polynomial.C (a ^(6:ℕ) * g + 2 * a * b ^(5:ℕ) * g + 2 * a ^(6:ℕ) + a ^(5:ℕ) * b + 2 * a ^(3:ℕ) * b ^(3:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 3 * a * b ^(5:ℕ) + 3 * b ^(6:ℕ)) * Polynomial.X
  + Polynomial.C (a ^(6:ℕ) * g + 2 * a ^(5:ℕ) * b * g + 2 * a * b ^(5:ℕ) * g + 4 * b ^(6:ℕ) * g + a ^(6:ℕ) + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(3:ℕ) + 4 * a * b ^(5:ℕ) + 2 * b ^(6:ℕ)) * Polynomial.X ^(2:ℕ)
  + Polynomial.C (3 * a ^(6:ℕ) * g + a ^(5:ℕ) * b * g + a * b ^(5:ℕ) * g + 2 * b ^(6:ℕ) * g + 4 * a ^(6:ℕ) + 4 * a ^(5:ℕ) * b + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X ^(3:ℕ)
  + Polynomial.C (a ^(6:ℕ) + 3 * a ^(5:ℕ) * b + 2 * a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X ^(5:ℕ)
  + Polynomial.C (4 * a ^(6:ℕ) + 2 * a ^(5:ℕ) * b + 3 * a * b ^(5:ℕ) + 4 * b ^(6:ℕ)) * Polynomial.X ^(6:ℕ)

/-- The `1`-th component of the ruling vector `asRuleQW · 1` at the witness point. -/
noncomputable def asWv1 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (4 * a ^(6:ℕ) * g + 3 * a ^(5:ℕ) * b * g + 3 * a * b ^(5:ℕ) * g + b ^(6:ℕ) * g + 2 * a ^(6:ℕ) + 4 * a ^(4:ℕ) * b ^(2:ℕ) + 3 * a ^(3:ℕ) * b ^(3:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a * b ^(5:ℕ) + 2 * b ^(6:ℕ))
  + Polynomial.C (2 * a ^(6:ℕ) + 4 * a ^(5:ℕ) * b + a ^(4:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(4:ℕ)) * Polynomial.X
  + Polynomial.C (a ^(6:ℕ) * g + 2 * a ^(5:ℕ) * b * g + 2 * a * b ^(5:ℕ) * g + 4 * b ^(6:ℕ) * g + a ^(6:ℕ) + 4 * a ^(5:ℕ) * b + 2 * a ^(4:ℕ) * b ^(2:ℕ) + a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(2:ℕ) * b ^(4:ℕ) + a * b ^(5:ℕ)) * Polynomial.X ^(2:ℕ)
  + Polynomial.C (4 * a ^(6:ℕ) + a ^(5:ℕ) * b + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a * b ^(5:ℕ)) * Polynomial.X ^(3:ℕ)
  + Polynomial.C (3 * a ^(6:ℕ) + 4 * a ^(5:ℕ) * b + a * b ^(5:ℕ) + 3 * b ^(6:ℕ)) * Polynomial.X ^(4:ℕ)
  + Polynomial.C (3 * a ^(6:ℕ) + 3 * a ^(5:ℕ) * b + a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X ^(5:ℕ)
  + Polynomial.C (a ^(6:ℕ) + 2 * a ^(5:ℕ) * b + 2 * a * b ^(5:ℕ) + 4 * b ^(6:ℕ)) * Polynomial.X ^(6:ℕ)

/-- The `2`-th component of the ruling vector `asRuleQW · 1` at the witness point. -/
noncomputable def asWv2 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (2 * a ^(6:ℕ) * g + 4 * a ^(5:ℕ) * b * g + 4 * a * b ^(5:ℕ) * g + 3 * b ^(6:ℕ) * g + 4 * a ^(6:ℕ) + a ^(5:ℕ) * b + 4 * a ^(4:ℕ) * b ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(3:ℕ) + a ^(2:ℕ) * b ^(4:ℕ) + a * b ^(5:ℕ) + b ^(6:ℕ))
  + Polynomial.C (3 * a ^(6:ℕ) * g + a ^(5:ℕ) * b * g + a * b ^(5:ℕ) * g + 2 * b ^(6:ℕ) * g + 2 * a ^(6:ℕ) + 2 * a ^(5:ℕ) * b + 2 * a ^(4:ℕ) * b ^(2:ℕ) + a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(2:ℕ) * b ^(4:ℕ) + 3 * a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X
  + Polynomial.C (3 * a ^(6:ℕ) + 4 * a ^(5:ℕ) * b + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 2 * a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X ^(2:ℕ)
  + Polynomial.C (2 * a ^(6:ℕ) + a ^(5:ℕ) * b + 4 * a * b ^(5:ℕ) + 2 * b ^(6:ℕ)) * Polynomial.X ^(3:ℕ)
  + Polynomial.C (4 * a ^(6:ℕ) + 2 * a ^(5:ℕ) * b + 3 * a * b ^(5:ℕ) + 4 * b ^(6:ℕ)) * Polynomial.X ^(4:ℕ)
  + Polynomial.C (3 * a ^(6:ℕ) + a ^(5:ℕ) * b + a * b ^(5:ℕ) + 2 * b ^(6:ℕ)) * Polynomial.X ^(5:ℕ)
  + Polynomial.C (a ^(6:ℕ) + 2 * a ^(5:ℕ) * b + 2 * a * b ^(5:ℕ) + 4 * b ^(6:ℕ)) * Polynomial.X ^(6:ℕ)

/-- The `3`-th component of the ruling vector `asRuleQW · 1` at the witness point. -/
noncomputable def asWv3 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (2 * a ^(6:ℕ) + 3 * a ^(5:ℕ) * b + 2 * a ^(4:ℕ) * b ^(2:ℕ) + a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(2:ℕ) * b ^(4:ℕ) + 3 * a * b ^(5:ℕ) + 3 * b ^(6:ℕ))
  + Polynomial.C (3 * a ^(6:ℕ) + a ^(5:ℕ) * b + 4 * a ^(4:ℕ) * b ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(3:ℕ) + a ^(2:ℕ) * b ^(4:ℕ) + 4 * a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X
  + Polynomial.C (2 * a ^(6:ℕ) + 3 * a ^(5:ℕ) * b + 4 * a * b ^(5:ℕ) + b ^(6:ℕ)) * Polynomial.X ^(2:ℕ)
  + Polynomial.C (4 * a ^(6:ℕ) + 3 * a * b ^(5:ℕ)) * Polynomial.X ^(3:ℕ)
  + Polynomial.C (3 * a ^(6:ℕ) + a ^(5:ℕ) * b + a * b ^(5:ℕ) + 2 * b ^(6:ℕ)) * Polynomial.X ^(4:ℕ)
  + Polynomial.C (2 * a ^(6:ℕ) + 4 * a ^(5:ℕ) * b + 4 * a * b ^(5:ℕ) + 3 * b ^(6:ℕ)) * Polynomial.X ^(5:ℕ)

/-- The `4`-th component of the ruling vector `asRuleQW · 1` at the witness point. -/
noncomputable def asWv4 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  0

lemma haeval_Wv0 {K : Type} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b)
        (Work.MotAS.asRuleQW (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun j => MvPolynomial.X j) 1 0) = asWv0 a b g := by
  simp (config := { failIfUnchanged := false }) only [Work.MotAS.asRuleQW, Work.MotAS.asRuleQA, Work.MotAS.asRuleQB, Work.MotAS.asPolarP,
    Work.MotAS.asTanQ, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Work.MotAS.kleinPAS,
    Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3,
    Work.MotAS.kleinPAS4, Work.MotK.kleinE, Work.MotAS.witPt, asWv0, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat,
    Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_Wv1 {K : Type} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b)
        (Work.MotAS.asRuleQW (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun j => MvPolynomial.X j) 1 1) = asWv1 a b g := by
  simp (config := { failIfUnchanged := false }) only [Work.MotAS.asRuleQW, Work.MotAS.asRuleQA, Work.MotAS.asRuleQB, Work.MotAS.asPolarP,
    Work.MotAS.asTanQ, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Work.MotAS.kleinPAS,
    Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3,
    Work.MotAS.kleinPAS4, Work.MotK.kleinE, Work.MotAS.witPt, asWv1, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat,
    Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_Wv2 {K : Type} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b)
        (Work.MotAS.asRuleQW (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun j => MvPolynomial.X j) 1 2) = asWv2 a b g := by
  simp (config := { failIfUnchanged := false }) only [Work.MotAS.asRuleQW, Work.MotAS.asRuleQA, Work.MotAS.asRuleQB, Work.MotAS.asPolarP,
    Work.MotAS.asTanQ, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Work.MotAS.kleinPAS,
    Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3,
    Work.MotAS.kleinPAS4, Work.MotK.kleinE, Work.MotAS.witPt, asWv2, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat,
    Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_Wv3 {K : Type} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b)
        (Work.MotAS.asRuleQW (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun j => MvPolynomial.X j) 1 3) = asWv3 a b g := by
  simp (config := { failIfUnchanged := false }) only [Work.MotAS.asRuleQW, Work.MotAS.asRuleQA, Work.MotAS.asRuleQB, Work.MotAS.asPolarP,
    Work.MotAS.asTanQ, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Work.MotAS.kleinPAS,
    Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3,
    Work.MotAS.kleinPAS4, Work.MotK.kleinE, Work.MotAS.witPt, asWv3, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat,
    Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_Wv4 {K : Type} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b)
        (Work.MotAS.asRuleQW (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun j => MvPolynomial.X j) 1 4) = asWv4 a b g := by
  simp (config := { failIfUnchanged := false }) only [Work.MotAS.asRuleQW, Work.MotAS.asRuleQA, Work.MotAS.asRuleQB, Work.MotAS.asPolarP,
    Work.MotAS.asTanQ, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Work.MotAS.kleinPAS,
    Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3,
    Work.MotAS.kleinPAS4, Work.MotK.kleinE, Work.MotAS.witPt, asWv4, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat,
    Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

/-- `MvPolynomial.aeval` commutes with `kleinRAS0`: the coefficient `a ^ p * g ^ q` of the
quadro-cubic map is pushed to `C a ^ p * C g ^ q`. -/
lemma aeval_kleinRAS0 {K : Type} [Field K] [CharP K 5] (a b g : K)
    (Z : Fin 5 → MvPolynomial (Fin 5) K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b)
        (Work.MotAS.kleinRAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) Z)
      = Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun i => MvPolynomial.aeval (Work.MotAS.witPt a b) (Z i)) := by
  simp (config := { failIfUnchanged := false }) only [Work.MotAS.kleinRAS0, map_add, map_sub,
    map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try rfl


end Work.MotV5.ASLocal
