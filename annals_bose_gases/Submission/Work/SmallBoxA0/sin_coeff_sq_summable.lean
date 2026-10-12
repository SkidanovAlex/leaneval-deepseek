import Mathlib.Analysis.Fourier.AddCircle
import Submission.Work.SmallBoxA0.fourierCoeff_oddExt
import Submission.Work.SmallBoxA0.memLp_oddExt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Summability of the squared sine (Dirichlet) coefficients

For a continuous `F` on `[-ℓ/2, ℓ/2]` with `ℓ > 0`, the squared Dirichlet
(sine) coefficients

    (∫_{−ℓ/2}^{ℓ/2} F x · sin (((k:ℝ)π/ℓ)(x + ℓ/2)) dx)²

are summable in `k : ℕ`.

This is Bessel's inequality for the Dirichlet basis; concretely it follows from
the Parseval identity `sin_parseval_shifted` together with *summability* of the
Dirichlet coefficients.  We obtain the latter from the `L²`-Fourier theory of
the odd extension `oddExt F` (`hasSum_sq_fourierCoeffOn`), then transfer from the
unit interval to `[-ℓ/2, ℓ/2]` by the explicit scaling
`sin_coeff_scaling_unit`.
-/

namespace Work.SmallBoxA0

open MeasureTheory

/-- Summability of the squared sine coefficients on the *unit* interval
`[−1/2, 1/2]` (the `ℓ = 1` case).  This is just Bessel's inequality for the
Dirichlet basis, extracted from `L²`-Parseval for the odd extension `oddExt F`
(`hasSum_sq_fourierCoeffOn`). -/
lemma sin_coeff_unit_summable {F : ℝ → ℝ} (hF : Continuous F) :
    Summable (fun k : ℕ =>
      (∫ x in (-(1 / 2))..(1 / 2),
        F x * Real.sin ((k : ℝ) * Real.pi * (x + 1 / 2))) ^ 2) := by
  have h02 : (-1 : ℝ) < 1 := by norm_num
  have hmemLp := memLp_oddExt hF
  -- `L²`-Parseval for the odd extension gives summability of the *circle*
  -- Fourier coefficients of `oddExt F` (indexed by `ℤ`).
  have h0 : Summable (fun i : ℤ =>
      ‖fourierCoeffOn h02 (fun v : ℝ => ((oddExt F v : ℝ) : ℂ)) i‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn h02 hmemLp).summable
  -- Each circle coefficient is `-I` times the (cast) sine coefficient, and the
  -- squared modulus of `-I * (r : ℂ)` is `r ^ 2`.
  have hz : Summable (fun i : ℤ =>
      (∫ x in (-(1 / 2))..(1 / 2),
        F x * Real.sin ((i : ℝ) * Real.pi * (x + 1 / 2))) ^ 2) := by
    refine h0.congr (fun i => ?_)
    rw [fourierCoeff_oddExt hF i]
    rw [← cast_oddExt_sin_integral i]
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.sq_norm,
      Complex.normSq_ofReal]
    ring
  -- Restrict the `ℤ`-indexed summable family to `ℕ`.
  have hnat : Summable (fun k : ℕ =>
      (∫ x in (-(1 / 2))..(1 / 2),
        F x * Real.sin (((k : ℤ) : ℝ) * Real.pi * (x + 1 / 2))) ^ 2) :=
    hz.comp_injective (fun a b hab => Int.ofNat_injective hab)
  refine hnat.congr (fun k => ?_)
  rw [show (((k : ℤ) : ℝ)) = (k : ℝ) by push_cast; ring]

/-- Rescaling of the sine coefficients from `[−1/2, 1/2]` (for the rescaled
function `y ↦ F (ℓ y)`) to `[−ℓ/2, ℓ/2]` (for `F`).  For `ℓ > 0`,

    ∫_{−1/2}^{1/2} F(ℓ y)·sin(kπ(y+1/2)) dy
      = ℓ⁻¹ · ∫_{−ℓ/2}^{ℓ/2} F x·sin((kπ/ℓ)(x+ℓ/2)) dx . -/
lemma sin_coeff_scaling_unit {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ} (k : ℕ) :
    (∫ y in (-(1 / 2))..(1 / 2),
        F (ℓ * y) * Real.sin ((k : ℝ) * Real.pi * (y + 1 / 2)))
      = ℓ⁻¹ * ∫ x in (-(ℓ / 2))..(ℓ / 2),
          F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) := by
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  -- Identify the integrand with the composite of `y ↦ ℓ * y`.
  have hpt : (fun y : ℝ => F (ℓ * y) * Real.sin ((k : ℝ) * Real.pi * (y + 1 / 2)))
      = fun y : ℝ => (fun x : ℝ =>
          F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) (ℓ * y) := by
    funext y
    simp only
    congr 1
    have h : (ℓ * y + ℓ / 2) = ℓ * (y + 1 / 2) := by ring
    rw [h]
    field_simp
  rw [hpt]
  -- The change of variables `x = ℓ * y` on `[-1/2, 1/2]`.
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) hne
    (a := -(1 / 2)) (b := 1 / 2) (c := ℓ)
  simp only [smul_eq_mul] at h
  rw [h]
  congr 2 <;> ring

/-- **The requested lemma.**  The squared sine (Dirichlet) coefficients of a
continuous function on `[-ℓ/2, ℓ/2]` are summable. -/
lemma sin_coeff_sq_summable {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ} (hF : Continuous F) :
    Summable (fun k : ℕ =>
      (∫ x in (-(ℓ / 2))..(ℓ / 2),
        F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2) := by
  -- Apply the unit-interval result to the rescaled function `y ↦ F (ℓ * y)`.
  have hcont : Continuous (fun y : ℝ => F (ℓ * y)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hG := sin_coeff_unit_summable (F := fun y : ℝ => F (ℓ * y)) hcont
  -- Scale the summable family by `ℓ ^ 2`.
  have hmul : Summable (fun k : ℕ => ℓ ^ 2 *
      (∫ y in (-(1 / 2))..(1 / 2),
        F (ℓ * y) * Real.sin ((k : ℝ) * Real.pi * (y + 1 / 2))) ^ 2) :=
    hG.mul_left (ℓ ^ 2)
  refine hmul.congr (fun k => ?_)
  set a : ℝ := ∫ x in (-(ℓ / 2))..(ℓ / 2),
      F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) with ha
  rw [sin_coeff_scaling_unit hℓ k, mul_pow]
  rw [show ℓ ^ 2 * ((ℓ⁻¹) ^ 2 * a ^ 2) = (ℓ * ℓ⁻¹) ^ 2 * a ^ 2 by ring,
      mul_inv_cancel₀ (ne_of_gt hℓ), one_pow, one_mul]

end Work.SmallBoxA0
