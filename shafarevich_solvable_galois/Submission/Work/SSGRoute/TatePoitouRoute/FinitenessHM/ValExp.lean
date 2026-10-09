import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The additive exponent of an adic valuation

For a Dedekind domain `R` with fraction field `K` and a height one prime `v` of `R`, Mathlib's
`v.valuation K : Valuation K ℤᵐ⁰` takes values in the multiplicative monoid
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`.  In this file we define the corresponding additive
`ℤ`-valued exponent

`adicExp v x = - log (v.valuation K x)`

so that `v.valuation K x = exp (- adicExp v x)`.  The function has junk value `0` at `x = 0`
and we only ever use it at nonzero arguments.  For `x : R` nonzero one has
`adicExp v (algebraMap R K x) = (normalizedFactors (span {x})).count v.asIdeal`, and the ordering
is reversed: `adicExp v x ≤ adicExp v y ↔ v.valuation K y ≤ v.valuation K x`.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open IsDedekindDomain

/-- The additive `ℤ`-valued exponent of the `v`-adic valuation on the fraction field `K`,
with junk value `0` at `0`. -/
noncomputable def adicExp {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (x : K) : ℤ :=
  -WithZero.log (v.valuation K x)

variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]

@[simp]
theorem adicExp_zero (v : HeightOneSpectrum R) : adicExp v (0 : K) = 0 := by
  simp [adicExp]

theorem adicExp_def (v : HeightOneSpectrum R) (x : K) :
    adicExp v x = -WithZero.log (v.valuation K x) := rfl

/-- The valuation is the exponential of minus the additive exponent. -/
theorem exp_neg_adicExp (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    WithZero.exp (-adicExp v x) = v.valuation K x := by
  have h : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [adicExp, neg_neg, WithZero.exp_log h]

/-- The additive exponent vanishes exactly at the units. -/
theorem adicExp_eq_zero_iff (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    adicExp v x = 0 ↔ v.valuation K x = 1 := by
  have h : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [adicExp, neg_eq_zero, ← WithZero.exp_inj (M := ℤ), WithZero.exp_log h,
    WithZero.exp_zero]

/-- The ordering of the additive exponent is the reverse of the ordering of the valuation. -/
theorem adicExp_le_iff (v : HeightOneSpectrum R) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    adicExp v x ≤ adicExp v y ↔ v.valuation K y ≤ v.valuation K x := by
  conv_rhs => rw [← exp_neg_adicExp v hx, ← exp_neg_adicExp v hy]
  rw [WithZero.exp_le_exp, neg_le_neg_iff]

/-- Strict version of `adicExp_le_iff`. -/
theorem adicExp_lt_iff (v : HeightOneSpectrum R) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    adicExp v x < adicExp v y ↔ v.valuation K y < v.valuation K x := by
  conv_rhs => rw [← exp_neg_adicExp v hx, ← exp_neg_adicExp v hy]
  rw [WithZero.exp_lt_exp, neg_lt_neg_iff]

/-- The additive exponent is additive. -/
theorem adicExp_mul (v : HeightOneSpectrum R) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    adicExp v (x * y) = adicExp v x + adicExp v y := by
  have hx' : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : v.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [adicExp_def, adicExp_def, adicExp_def, map_mul, WithZero.log_mul hx' hy']
  ring

/-- The additive exponent of a power. -/
theorem adicExp_pow (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) (n : ℕ) :
    adicExp v (x ^ n) = (n : ℤ) * adicExp v x := by
  rw [adicExp_def, adicExp_def, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

/-- In the strict case the additive exponent of a sum is the smaller of the two. -/
theorem adicExp_add_eq_of_lt (v : HeightOneSpectrum R) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : adicExp v x < adicExp v y) : adicExp v (x + y) = adicExp v x := by
  have hv : v.valuation K y < v.valuation K x := (adicExp_lt_iff v hx hy).mp h
  have h1 : v.valuation K (x + y) = v.valuation K x :=
    (v.valuation K).map_add_eq_of_lt_left hv
  have hxy : x + y ≠ 0 := by
    rintro h0
    rw [h0, Valuation.map_zero] at h1
    exact (Valuation.ne_zero_iff _).2 hx h1.symm
  rw [adicExp_def, adicExp_def, h1]

/-- The additive exponent is nonnegative exactly at the elements integral at `v`. -/
theorem adicExp_nonneg_iff (v : HeightOneSpectrum R) (x : K) :
    0 ≤ adicExp v x ↔ v.valuation K x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [adicExp_zero]
  · rw [← exp_neg_adicExp v hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- For an element of `R`, the additive exponent is the exponent of the principal ideal. -/
theorem adicExp_algebraMap_eq_count (v : HeightOneSpectrum R) (x : R) (hx : x ≠ 0) :
    adicExp v (algebraMap R K x) =
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).count v.asIdeal := by
  have hspan : Ideal.span {x} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hx
  rw [adicExp_def, HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg hx,
    WithZero.log_exp, neg_neg]
  exact_mod_cast Ideal.count_associates_factors_eq hspan v.isPrime v.ne_bot

section LiesOver

variable {A : Type*} {B : Type*} {L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
  [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B] [Field L] [Algebra K L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

/-- The additive exponent in an extension: `ord_w (algebraMap x) = e(w/v) · ord_v x`. -/
theorem adicExp_liesOver (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : A) :
    adicExp w (algebraMap A L x) = w.asIdeal.ramificationIdx A * adicExp v (algebraMap A K x) := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx A :=
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot
  have h1 : w.valuation L (algebraMap A L x) = w.intValuation (algebraMap A B x) := by
    rw [IsScalarTower.algebraMap_apply A B L, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : v.valuation K (algebraMap A K x) = v.intValuation x :=
    HeightOneSpectrum.valuation_of_algebraMap v x
  have h3 := HeightOneSpectrum.intValuation_liesOver v w x
  rw [adicExp_def, adicExp_def, h1, h2, ← h3, WithZero.log_pow]
  try rw [he]
  rw [nsmul_eq_mul]
  ring

end LiesOver

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
