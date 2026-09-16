import Submission.ZagierHoffmanProof.PeriodDatum
import Submission.ZagierHoffmanProof.KummerField
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup

/-!
# The Anderson–Thakur period function over the Kummer field `F((y))`

`PeriodDatum.lean` proves the functional equation `(t - θ^q)·Ω^{(1)} = Ω` for the period function
`Ω = C μ · ∏_{i≥1}(1 - t/θ^{q^i})` of Anderson–Thakur over an abstract complete valued field `K`
satisfying `μ^{q-1}·θ^q = -1`, in a *general* normalisation `v θ = exp d`.

This file performs the concrete instantiation announced there: `K := F((y)) = LaurentSeries F`,
`θ := -y^{-(q-1)}` (so `d = q - 1`), `μ := y^q`, with `q = Nat.card F`.  The relation
`μ^{q-1}·θ^q = -1` is `KummerField.kummerMu_pow_mul_theta_pow`, and `v μ = exp (-q) ≤ exp (-1)`
is `KummerField.v_kummerMu_le_one`.

The only plumbing needed is that the `ExpChar`/`CharP` type classes of the Laurent series field
are given: `Nat.card F` must be a *prime*, in which case it is the characteristic of `F` and
therefore that of `F((y))`.  (For a non-prime `Nat.card F = p^f` the twist has to be
re-parameterised by the prime `p`; see `PLAN.md`.)

## Main results

* `charP_laurentSeries`, `expChar_laurentSeries`, `nonarchimedeanAddGroup_laurentSeries` —
  the type class instances on `LaurentSeries F`.
* `periodTheta`, `periodMu`, `periodD`, `periodOmega` — the elements `θ`, `μ`, the exponent
  `d = q - 1` and the period function.
* ★ `periodDatum_twist_L` — `(t - θ^q)·Ω^{(1)} = Ω` over `F((y))`.
* ★ `isSmall_periodDatum_L` — `IsSmall Ω` (so the `L`-series converge over `F((y))`).
* ★ `isUnit_periodOmegaTate` — `Ω` is a *unit* of the Tate algebra `T` of `F((y))`.
* `periodOmega_entire`, `periodOmega_bounded` — `Ω` is entire / a Tate series.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Polynomial RatFunc
open scoped WithZero Topology
open LaurentSeries HahnSeries

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

noncomputable section

section char

/-- If the cardinality of a finite field is prime then it is its characteristic. -/
lemma ringChar_eq_card_of_prime (hp : (Nat.card F).Prime) : ringChar F = Nat.card F := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card (K := F) (p := ringChar F)
  have hdvd : ringChar F ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_trans (dvd_pow_self _ (PNat.ne_zero n)) (dvd_refl _)
  exact (Nat.prime_dvd_prime_iff_eq hprime hp).mp hdvd

/-- The characteristic of the Laurent series field is `Nat.card F`, in the prime-cardinality
case. -/
instance charP_laurentSeries [Fact (Nat.card F).Prime] :
    CharP (LaurentSeries F) (Nat.card F) := by
  haveI : CharP F (Nat.card F) :=
    ringChar_eq_card_of_prime F Fact.out ▸ (inferInstance : CharP F (ringChar F))
  exact charP_of_injective_algebraMap (algebraMap F (LaurentSeries F)).injective _

/-- The exponential characteristic of the Laurent series field. -/
instance expChar_laurentSeries [Fact (Nat.card F).Prime] :
    ExpChar (LaurentSeries F) (Nat.card F) :=
  expChar_prime _ _

/-- **`q = |F|` is a Frobenius exponent for `F((y))`, for every finite field `F`** (not only for
prime `|F|`): `|F| = p ^ f` with `p = ringChar F`, and `x ↦ x ^ (p ^ f)` is the `f`-fold iterate
of the true Frobenius.  This is the generalisation of `expChar_laurentSeries` that removes the
primality restriction from the whole `Ω`/`L`-series chapter. -/
theorem frobPow_laurentSeries (F : Type*) [Field F] [Finite F] :
    FrobPow (LaurentSeries F) (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hprime, hcard⟩ := FiniteField.card F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hprime⟩
  haveI : CharP (LaurentSeries F) (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F (LaurentSeries F)).injective _
  have hcard' : Nat.card F = ringChar F ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  rw [hcard']
  exact FrobPow.of_charP (R := LaurentSeries F) (p := ringChar F) (f : ℕ)

/-- The corresponding *instance*: `q = |F|` is a `FrobPow` exponent for `F((y))`. -/
instance instFrobPowLaurentSeries : FrobPow (LaurentSeries F) (Nat.card F) :=
  frobPow_laurentSeries F

/-- The additive group of `F((y))` is nonarchimedean for the `y`-adic valuation. -/
instance nonarchimedeanAddGroup_laurentSeries :
    NonarchimedeanAddGroup (LaurentSeries F) :=
  Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup

end char

section datum

/-- `q = Nat.card F`. -/
abbrev periodCard : ℕ := Nat.card F

/-- The exponent `d = q - 1` of the normalisation `v θ = exp d`. -/
def periodD : ℤ := ((Nat.card F : ℕ) : ℤ) - 1

/-- The element `θ = -y^{-(q-1)}` of `F((y))`. -/
abbrev periodTheta : LaurentSeries F := kummerTheta F

/-- The period constant `μ = y^q` of `F((y))`. -/
abbrev periodMu : LaurentSeries F := kummerMu F

/-- `v θ = exp d` for `d = q - 1`. -/
lemma v_periodTheta : Valued.v (periodTheta F) = WithZero.exp (periodD F) :=
  v_kummerTheta F

/-- A finite field has at least two elements. -/
lemma two_le_card_field : 2 ≤ Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

lemma one_le_periodD : 1 ≤ periodD F := by
  rw [periodD]
  have h : 2 ≤ Nat.card F := two_le_card_field F
  push_cast
  omega

lemma two_le_periodCard : 2 ≤ periodCard F := two_le_card_field F

/-- `v μ = exp (-q)`. -/
lemma v_periodMu : Valued.v (periodMu F) = WithZero.exp (-((Nat.card F : ℕ) : ℤ)) :=
  v_kummerMu F

/-- `μ` is small: `v μ ≤ exp (-1)`. -/
lemma v_periodMu_le_one : Valued.v (periodMu F) ≤ WithZero.exp (-1) :=
  v_kummerMu_le_one F

/-- The period-constant relation over `F((y))`. -/
theorem periodMu_pow_mul : periodMu F ^ (Nat.card F - 1) * periodTheta F ^ Nat.card F = -1 :=
  kummerMu_pow_mul_theta_pow F

lemma periodMu_ne_zero : periodMu F ≠ 0 :=
  HahnSeries.single_ne_zero one_ne_zero

lemma periodTheta_ne_zero : periodTheta F ≠ 0 := by
  rw [periodTheta, kummerTheta]
  exact HahnSeries.single_ne_zero (by norm_num)

end datum

section main

/-- **The Anderson–Thakur period function over `F((y))`**:
`Ω = C μ · ∏_{i≥1}(1 - t/θ^{q^i})`, with `θ = -y^{-(q-1)}`, `μ = y^q`. -/
def periodOmega : PowerSeries (LaurentSeries F) :=
  PowerSeries.C (periodMu F) * atOmega (periodCard F) (periodTheta F)

/-- **The functional equation of the Anderson–Thakur period function over `F((y))`**:
`(t - θ^q)·Ω^{(1)} = Ω`. -/
theorem periodDatum_twist_L :
    (PowerSeries.X - PowerSeries.C ((periodTheta F) ^ periodCard F))
        * frobTwist (R := LaurentSeries F) (p := periodCard F) 1 (periodOmega F)
      = periodOmega F := by
  haveI : FrobPow (LaurentSeries F) (periodCard F) := frobPow_laurentSeries F
  exact periodDatum_twist (periodCard F) (periodTheta F) (periodD F) (one_le_periodD F)
    (v_periodTheta F) (two_le_periodCard F) (periodMu_pow_mul F)

/-- `Ω` is small, i.e. lies in the maximal ideal of the Tate algebra: its coefficients have
valuation `≤ exp (-1)`.  This is the convergence hypothesis of the `L`-series over `F((y))`. -/
theorem isSmall_periodDatum_L : IsSmall (periodOmega F) := by
  haveI : FrobPow (LaurentSeries F) (periodCard F) := frobPow_laurentSeries F
  exact isSmall_periodDatum (periodCard F) (periodTheta F) (periodD F) (one_le_periodD F)
    (v_periodTheta F) (two_le_periodCard F) (v_periodMu_le_one F)

/-- `Ω` is a Tate series (bounded coefficients). -/
theorem periodOmega_bounded : SeriesBounded (periodOmega F) := by
  haveI : FrobPow (LaurentSeries F) (periodCard F) := frobPow_laurentSeries F
  exact periodDatum_bounded (periodCard F) (periodTheta F) (periodD F) (one_le_periodD F)
    (v_periodTheta F) (two_le_periodCard F)

/-- `Ω` is entire. -/
theorem periodOmega_entire : Entire (periodOmega F) := by
  haveI : FrobPow (LaurentSeries F) (periodCard F) := frobPow_laurentSeries F
  exact Entire.mul (Entire.C (periodMu F))
    (atOmega_entire_d (periodCard F) (periodTheta F) (periodD F) (one_le_periodD F)
      (v_periodTheta F) (two_le_periodCard F))

section unit

/-- The inverse of the period function: `μ⁻¹·(∑_{m≥0} c_m t^m)` where `∑ c_m t^m` is the
inverse of the pure product `∏_{i≥1}(1 - t/θ^{q^i})`. -/
def periodOmegaInv : PowerSeries (LaurentSeries F) :=
  PowerSeries.C ((periodMu F)⁻¹)
    * PowerSeries.mk (omInvCoeff (periodCard F) (periodTheta F))

lemma periodOmegaInv_bounded : SeriesBounded (periodOmegaInv F) :=
  SeriesBounded.mul (SeriesBounded.C ((periodMu F)⁻¹))
    (omInvCoeff_bounded_d (periodCard F) (periodTheta F) (periodD F) (one_le_periodD F)
      (v_periodTheta F) (two_le_periodCard F))

lemma periodOmega_mul_inv : periodOmega F * periodOmegaInv F = 1 := by
  have hC : (PowerSeries.C (periodMu F) : PowerSeries (LaurentSeries F))
      * PowerSeries.C ((periodMu F)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (periodMu_ne_zero F), map_one]
  calc periodOmega F * periodOmegaInv F
      = (PowerSeries.C (periodMu F) * PowerSeries.C ((periodMu F)⁻¹))
          * (atOmega (periodCard F) (periodTheta F)
              * PowerSeries.mk (omInvCoeff (periodCard F) (periodTheta F))) := by
        rw [periodOmega, periodOmegaInv,
          mul_mul_mul_comm (PowerSeries.C (periodMu F))
            (atOmega (periodCard F) (periodTheta F))
            (PowerSeries.C ((periodMu F)⁻¹))
            (PowerSeries.mk (omInvCoeff (periodCard F) (periodTheta F)))]
    _ = 1 * 1 := by rw [hC, atOmega_mul_omInvCoeff]
    _ = 1 := one_mul 1

/-- **`Ω` as an element of the Tate algebra of `F((y))`.** -/
def periodOmegaTate : TateAlg (LaurentSeries F) :=
  ⟨periodOmega F, periodOmega_bounded F⟩

/-- The inverse of `Ω` in the Tate algebra. -/
def periodOmegaInvTate : TateAlg (LaurentSeries F) :=
  ⟨periodOmegaInv F, periodOmegaInv_bounded F⟩

/-- **`Ω` is a unit of the Tate algebra `T` of `F((y))`**: `Ω ∈ T^×`. -/
theorem isUnit_periodOmegaTate : IsUnit (periodOmegaTate F) := by
  refine ⟨⟨periodOmegaTate F, periodOmegaInvTate F, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (periodOmega_mul_inv F)
  · refine Subtype.ext ?_
    show periodOmegaInv F * periodOmega F = 1
    rw [mul_comm]
    exact periodOmega_mul_inv F

end unit

end main

end

end ZagierHoffmanPositiveChar
