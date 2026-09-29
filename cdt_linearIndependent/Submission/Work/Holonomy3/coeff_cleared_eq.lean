import Mathlib
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.min_coeff

/-!
# The minimal-degree coefficient of the cleared pullback (STEP 3, coefficient identity)

This module assembles the purely algebraic coefficient identity that the analytic STEP 3 of the
fine holonomy bound needs.

Let `F = auxSeries f Q` be the auxiliary multivariable series over `ℚ`, `Φ = (Φ_s)_s` a `d`-tuple
of power series vanishing at `0` (the maps in the `s`-th variable), and `P i s` the pole-clearing
polynomials.  The cleared pullback is

  `uPoly P * diagComp Φ (auxSeriesC fℂ Qℂ)`,

where `fℂ`, `Qℂ` are the scalar extensions to `ℂ` and `uPoly P = ∏_s (∏_i P i s)(z_s)` is the
pole-clearing polynomial.

If `n` is a minimal total-degree exponent of `auxSeriesC fℂ Qℂ` (no coefficient of strictly smaller
degree is nonzero), then

  `coeff_n (uPoly P · diagComp Φ (auxSeriesC fℂ Qℂ))`
      `= (∏_s ∏_i P i s (0)) · (coeff_n F) · ∏_s (coeff_1 Φ_s)^{n_s}` :

by minimality of the total degree of `n` the diagonal composition `diagComp` contributes exactly
the coefficient `coeff_n` times `∏_s (coeff_1 Φ_s)^{n_s}` (`Work.Holonomy3.diagComp_coeff_eq`),
and the clearing factor contributes only its constant term `∏_s ∏_i P i s (0)`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-! ## Auxiliary lemmas: scalar extension `ℚ → ℂ` of the auxiliary series -/

/-- The lift of a univariate series to the `s`-th variable commutes with scalar extension
`ℚ → ℂ`. -/
lemma embedVarC_map {d : ℕ} (s : Fin d) (f : PowerSeries ℚ) :
    embedVarC s (PowerSeries.map (algebraMap ℚ ℂ) f)
      = MvPowerSeries.map (algebraMap ℚ ℂ) (embedVar s f) := by
  ext n
  rw [MvPowerSeries.coeff_map]
  show embedVarC s (PowerSeries.map (algebraMap ℚ ℂ) f) n
      = algebraMap ℚ ℂ (embedVar s f n)
  by_cases h : n = Finsupp.single s (n s)
  · rw [embedVarC_apply h]
    have : embedVar s f n = PowerSeries.coeff (n s) f := by rw [embedVar]; exact if_pos h
    rw [this, PowerSeries.coeff_map]
  · rw [embedVarC_apply_of_ne h]
    have : embedVar s f n = 0 := by rw [embedVar]; exact if_neg h
    rw [this, map_zero]

/-- The inclusion of multivariate polynomials into multivariate power series commutes with scalar
extension `ℚ → ℂ`. -/
lemma coe_mapToMvPowerSeries {d : ℕ} (Q : MvPolynomial (Fin d) ℚ) :
    ((MvPolynomial.map (algebraMap ℚ ℂ) Q : MvPolynomial (Fin d) ℂ) : MvPowerSeries (Fin d) ℂ)
      = MvPowerSeries.map (algebraMap ℚ ℂ) (Q : MvPowerSeries (Fin d) ℚ) := by
  ext n
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_map, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_map]

/-- The auxiliary series over `ℂ` of the scalar-extended data is the scalar extension of the
auxiliary series over `ℚ`. -/
lemma auxSeriesC_map {d m : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) :
    auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
      (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i))
      = MvPowerSeries.map (algebraMap ℚ ℂ) (auxSeries f Q) := by
  rw [auxSeriesC, auxSeries, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_prod, ← coe_mapToMvPowerSeries (Q i)]
  congr 1
  exact Finset.prod_congr rfl (fun s _ => embedVarC_map s (f (i s)))

/-! ## The constant coefficient of the pole-clearing polynomial -/

/-- The constant coefficient of the pole-clearing polynomial `uPoly P = ∏_s (∏_i P i s)(z_s)` is
`∏_s ∏_i P i s (0)`. -/
lemma uPoly_coeff_zero {d m : ℕ} (P : Fin m → Fin d → Polynomial ℂ) :
    MvPowerSeries.coeff 0 (uPoly P) = ∏ s, ∏ i, (P i s).eval 0 := by
  rw [uPoly, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (embedVarC s (∏ i, (P i s : PowerSeries ℂ))) 0 = ∏ i, (P i s).eval 0
  rw [embedVarC_coeff_zero]
  have hcoe : (∏ i, (P i s : PowerSeries ℂ))
      = ((∏ i, P i s : Polynomial ℂ) : PowerSeries ℂ) :=
    (map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) (fun i => P i s)
      Finset.univ).symm
  rw [hcoe, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]

/-! ## The coefficient identity -/

/-- **The coefficient identity of the cleared pullback (STEP 3).**  If `n` is a minimal total-degree
exponent of the scalar-extended auxiliary series `auxSeriesC fℂ Qℂ`, then the `n`-th coefficient of
the cleared pullback `uPoly P · diagComp Φ (auxSeriesC fℂ Qℂ)` is
`(∏_s ∏_i P i s (0)) · (coeff_n (auxSeries f Q)) · ∏_s (coeff_1 Φ_s)^{n_s}`. -/
theorem coeff_cleared_eq {d m : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) (Φ : Fin d → PowerSeries ℂ)
    (P : Fin m → Fin d → Polynomial ℂ) (n : Fin d →₀ ℕ)
    (hΦ0 : ∀ s, PowerSeries.coeff 0 (Φ s) = 0)
    (hmin : ∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
      MvPowerSeries.coeff n' (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
        (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i))) = 0) :
    MvPowerSeries.coeff n (uPoly P *
        diagComp Φ (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
          (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i))))
      = (∏ s, ∏ i, (P i s).eval 0) *
        (((Submission.CDTPlan.auxSeries f Q).coeff n : ℚ) : ℂ) *
        ∏ s, (PowerSeries.coeff 1 (Φ s)) ^ (n s) := by
  have hSc : MvPowerSeries.coeff n
      (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
        (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i)))
      = ((MvPowerSeries.coeff n (auxSeries f Q) : ℚ) : ℂ) := by
    rw [auxSeriesC_map f Q, MvPowerSeries.coeff_map]
    simp
  have hdiagmin : ∀ m' : Fin d →₀ ℕ, m'.degree < n.degree →
      MvPowerSeries.coeff m' (diagComp Φ (auxSeriesC
        (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
        (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i)))) = 0 :=
    fun m' hm => diagComp_coeff_eq_zero Φ _ hmin hm
  rw [coeff_mul_eq_of_min (uPoly P) _ hdiagmin rfl,
    diagComp_coeff_eq Φ _ hmin hΦ0, hSc, uPoly_coeff_zero P]
  ring

end Work.Holonomy3
