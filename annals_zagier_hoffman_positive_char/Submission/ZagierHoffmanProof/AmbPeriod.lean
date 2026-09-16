import Submission.ZagierHoffmanProof.AmbientRing
import Submission.ZagierHoffmanProof.GenPeriodDatum
import Submission.ZagierHoffmanProof.PeriodL

/-!
# The Anderson–Thakur period datum over the ambient field `L`

Every application of Dac's §3.3 (`LinearIndependence.linear_independence`) — to the MZV, the CMPL
and the ACMPL `t`-motive — uses the same period function `ω = Ω` as the small parameter of the
`L`-series.  This file instantiates the generic period datum `GenPeriodDatum.lean`
(`Ω = C μ · Ω̃`, `Ω̃ = atOmegaGen q θ`) over the ambient field

  `L = Ambient F = completion of the perfect closure of F((y))`,

with `θ = ambTheta F = -y^{-(q-1)}` and `μ = ambMu F = y^q`, and proves the five properties
required by `linear_independence`:

* `gIsSmall_ambOmega`, `gSuperEntire_ambOmega` (the coefficient bounds),
* `coeff_zero_ambOmega` (`Ω(0) ≠ 0`),
* `evalSeriesGen_ambOmega_frobenius_orbit` (`Ω(θ^{q^k}) = 0` for `k ≥ 1`),
* `ambOmega_functional` (the functional equation `(t - θ^q)·Ω^{(1)} = Ω`).

The normalising constant satisfies `μ^{q-1}·θ^q = -1` (`ambMu_pow_mul`), obtained by pushing
`periodMu_pow_mul` (over `F((y))`) through the ring hom `F((y)) → L`.

## Main results

* `ambMu_pow_mul`, `ambMu_pow_mul_theta`.
* ★★★ `ambOmega_functional`.
* ★★★ `evalSeriesGen_ambOmega_frobenius_orbit`.
* `gIsSmall_ambOmega`, `gSuperEntire_ambOmega`, `coeff_zero_ambOmega`.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-! ## §0. The small parameter `γ = exp (-1)` -/

/-- The exponent-`1` value `γ = exp (-1)`: the small parameter of the chapter. -/
noncomputable def ambGamma : ℚᵐ⁰ := WithZero.exp (-1)

lemma ambGamma_pos : 0 < ambGamma := WithZero.exp_pos

lemma ambGamma_lt_one : ambGamma < 1 := by
  rw [ambGamma, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

lemma ambGamma_nonneg : 0 ≤ ambGamma := ambGamma_pos.le

lemma ambGamma_le_one : ambGamma ≤ 1 := ambGamma_lt_one.le

/-! ## §1. The period constant `μ = y^q` -/

/-- `ambMu` is the image of `kummerMu` under the composite map `F((y)) → L`. -/
lemma ambMu_eq_lift : ambMu F = ambLiftHom F (kummerMu F) := rfl

/-- **The normalising relation** `μ^{q-1}·θ^q = -1` in `L`. -/
theorem ambMu_pow_mul :
    (ambMu F) ^ (Nat.card F - 1) * (ambTheta F) ^ Nat.card F = -1 := by
  rw [ambMu_eq_lift, ambTheta_eq_lift, ← map_pow, ← map_pow, ← map_mul]
  rw [show kummerMu F ^ (Nat.card F - 1) * kummerTheta F ^ Nat.card F = -1 from
    periodMu_pow_mul F]
  simp

/-- The relation in the "twisted" form used by the functional equation: `μ^q·θ^q = -μ`. -/
theorem ambMu_pow_mul_theta :
    (ambMu F) ^ Nat.card F * (ambTheta F) ^ Nat.card F = -(ambMu F) := by
  have hq1 : 1 ≤ Nat.card F := le_trans (by norm_num : 1 ≤ 2) (two_le_card_field F)
  have hsplit : (ambMu F) ^ Nat.card F = (ambMu F) ^ (Nat.card F - 1) * ambMu F := by
    conv_lhs => rw [← Nat.sub_add_cancel hq1]
    rw [pow_add, pow_one]
  rw [hsplit]
  calc (ambMu F) ^ (Nat.card F - 1) * ambMu F * (ambTheta F) ^ Nat.card F
      = ((ambMu F) ^ (Nat.card F - 1) * (ambTheta F) ^ Nat.card F) * ambMu F := by ring
    _ = -1 * ambMu F := by rw [ambMu_pow_mul]
    _ = -(ambMu F) := by ring

lemma ambMu_ne_zero : ambMu F ≠ 0 := by
  intro h
  have h1 := v_ambMu F
  rw [h, map_zero] at h1
  exact absurd h1.symm (WithZero.exp_ne_zero)

lemma ambTheta_ne_zero : ambTheta F ≠ 0 := by
  intro h
  have h1 := v_ambTheta F
  rw [h, map_zero] at h1
  exact absurd h1.symm (WithZero.exp_ne_zero)

/-! ## §2. The period datum `Ω = C μ · Ω̃` -/

/-- The Anderson–Thakur period function over the ambient field: `Ω = C μ · Ω̃`. -/
noncomputable def ambOmega : PowerSeries (Ambient F) :=
  PowerSeries.C (ambMu F) * atOmegaGen (Nat.card F) (ambTheta F)


lemma v_ambTheta_inv_le : (Valued.v (ambTheta F))⁻¹ ≤ ambGamma := by
  rw [v_ambTheta, ← WithZero.exp_neg, ambGamma, WithZero.exp_le_exp]
  have h : (2 : ℚ) ≤ (Nat.card F : ℚ) := by
    exact_mod_cast (two_le_card_field F : 2 ≤ Nat.card F)
  linarith

lemma v_ambMu_le : Valued.v (ambMu F) ≤ ambGamma := by
  rw [v_ambMu, ambGamma, WithZero.exp_le_exp]
  have h : (1 : ℚ) ≤ (Nat.card F : ℚ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_card_field F) : 1 ≤ Nat.card F)
  linarith

lemma two_le_ambCard : 2 ≤ Nat.card F := two_le_card_field F

/-- The period datum is small (`GIsSmall γ Ω`). -/
theorem gIsSmall_ambOmega :
    GIsSmall ambGamma (ambOmega F) :=
  gIsSmall_C_mul_atOmegaGen (K := Ambient F) (Nat.card F) (ambTheta F)
    (ambGamma_pos) (v_ambTheta_inv_le F) (ambGamma_lt_one)
    gammaArchimedean_rat (two_le_ambCard F) (v_ambMu_le F)

/-- The period datum is super-entire. -/
theorem gSuperEntire_ambOmega :
    GSuperEntire ambGamma (ambOmega F) :=
  gSuperEntire_C_mul_atOmegaGen (K := Ambient F) (Nat.card F) (ambTheta F)
    (ambGamma_pos) (v_ambTheta_inv_le F) (ambGamma_lt_one)
    gammaArchimedean_rat (two_le_ambCard F)

/-- `Ω(0) ≠ 0`. -/
theorem coeff_zero_ambOmega : (ambOmega F).coeff 0 ≠ 0 := by
  rw [ambOmega, PowerSeries.coeff_C_mul, coeff_zero_atOmegaGen, mul_one]
  exact ambMu_ne_zero F

/-- **`Ω` vanishes on the Frobenius orbit of `θ`**: `Ω(θ^{q^k}) = 0` for `k ≥ 1`. -/
theorem evalSeriesGen_ambOmega_frobenius_orbit {k : ℕ} (hk : 1 ≤ k) :
    evalSeriesGen (ambOmega F) ((ambTheta F) ^ (Nat.card F ^ k)) = 0 :=
  evalSeriesGen_C_mul_atOmegaGen_frobenius_orbit (K := Ambient F) (Nat.card F) (ambTheta F)
    (ambTheta_ne_zero F) (ambGamma_pos) (v_ambTheta_inv_le F) (ambGamma_lt_one)
    gammaArchimedean_rat (two_le_ambCard F) (ambMu F) hk

/-- **The functional equation of the period datum**: `(t - θ^q)·Ω^{(1)} = Ω`. -/
theorem ambOmega_functional :
    (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ambOmega F) = ambOmega F := by
  have htw := atOmegaGen_twist' (K := Ambient F) (Nat.card F) (ambTheta F) (ambTheta_ne_zero F)
    (ambGamma_pos) (v_ambTheta_inv_le F) (ambGamma_lt_one) gammaArchimedean_rat
    (two_le_ambCard F)
  have hC : (PowerSeries.C ((ambMu F) ^ Nat.card F) : PowerSeries (Ambient F))
      * PowerSeries.C ((ambTheta F) ^ Nat.card F) = -PowerSeries.C (ambMu F) := by
    rw [← map_mul, ambMu_pow_mul_theta, map_neg]
  calc (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ambOmega F)
      = (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
          * (PowerSeries.C ((ambMu F) ^ Nat.card F)
            * frobTwist (R := Ambient F) (p := Nat.card F) 1
                (atOmegaGen (Nat.card F) (ambTheta F))) := by
        rw [ambOmega, frobTwist_mul, frobTwist_C, pow_one]
    _ = PowerSeries.C ((ambMu F) ^ Nat.card F)
          * ((PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
            * frobTwist (R := Ambient F) (p := Nat.card F) 1
                (atOmegaGen (Nat.card F) (ambTheta F))) := by ring
    _ = PowerSeries.C ((ambMu F) ^ Nat.card F)
          * (-PowerSeries.C ((ambTheta F) ^ Nat.card F)
              * atOmegaGen (Nat.card F) (ambTheta F)) := by rw [htw]
    _ = -((PowerSeries.C ((ambMu F) ^ Nat.card F) : PowerSeries (Ambient F))
            * PowerSeries.C ((ambTheta F) ^ Nat.card F))
          * atOmegaGen (Nat.card F) (ambTheta F) := by ring
    _ = PowerSeries.C (ambMu F) * atOmegaGen (Nat.card F) (ambTheta F) := by rw [hC]; ring
    _ = ambOmega F := rfl

end ZagierHoffmanPositiveChar
