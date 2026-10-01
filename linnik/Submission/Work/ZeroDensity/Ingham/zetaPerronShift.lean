import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs
import Submission.Work.ZeroDensity.Ingham.vertical_shift_patched_pole
import Submission.Work.ZeroDensity.Ingham.perronInt_integrable
import Submission.Work.ZeroDensity.Ingham.perronH_differentiable
import Submission.Work.ZeroDensity.Ingham.perronH_horizontal

/-!
# The contour shift of Montgomery's zero detector for `ζ`

For `Y > 0`, a zero `ρ` of `ζ` with `1/2 ≤ Re ρ ≤ 1` and `ρ ≠ 1`, the integral of the Perron
integrand `perronInt K Y ρ w = Γ(w) Y^w ζ(ρ+w) M_K(ρ+w)` over the vertical line `Re w = 2` equals
the integral over the critical line `Re w = 1/2 - Re ρ` plus the single residue at the pole
`w = 1 - ρ`:

`(1/2π) ∫_ℝ perronInt K Y ρ (2+it) dt
   = residueTerm K Y ρ + (1/2π) ∫_ℝ perronInt K Y ρ (1/2-β+it) dt`.

The assembly is exactly the "patched pole" contour shift `vertical_shift_patched_pole` applied to
`F = perronInt K Y ρ`, `H = perronH K Y ρ = dslope (perronM K Y ρ) (1-ρ)`, `u = 1-ρ` and
`a = residueTerm K Y ρ`: the decomposition `perronInt = residueTerm/(w-(1-ρ)) + perronH` off the two
poles `w = 0`, `w = 1-ρ` is `perronInt_eq_residueTerm_add_perronH`; `perronH` is holomorphic on the
rectangles (`perronH_differentiable`); the horizontal edges of `perronH` vanish
(`perronH_horizontal`); and `perronInt` is integrable on both vertical lines
(`perronInt_integrable`).
-/

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- The `1/2π`-normalised form of the patched contour shift: dividing
`vertical_shift_patched_pole` by `2π` turns the residue term `2π a` into `a`. -/
theorem perronShift_divided (F H : ℂ → ℂ) (p q : ℝ) (hpq : p < q) (u a : ℂ)
    (hu : p < u.re ∧ u.re < q)
    (hH : ∀ R : ℝ, DifferentiableOn ℂ H (Set.uIcc p q ×ℂ Set.uIcc (-R) R))
    (hdec : ∀ R : ℝ, 1 ≤ R → ∀ s ∈ (Set.uIcc p q ×ℂ Set.uIcc (-R) R), s ≠ u → s ≠ 0 →
      F s = a / (s - u) + H s)
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hpint : Integrable (fun t : ℝ => F ((p : ℂ) + (t : ℂ) * Complex.I)))
    (hqint : Integrable (fun t : ℝ => F ((q : ℂ) + (t : ℂ) * Complex.I))) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      = a + (1 / (2 * Real.pi)) * (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) := by
  have h := vertical_shift_patched_pole F H p q hpq u a hu hH hdec htop hbot hpint hqint
  have key : (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  rw [h, mul_add, ← mul_assoc, key, one_mul]
  exact add_comm _ _

/-- The contour shift of the zero detector with its residue, normalised by `1/2π`. -/
theorem zetaPerronShift (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (hβ0 : (1 : ℝ) / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I))
      = residueTerm K Y ρ
        + (1 / (2 * Real.pi)) *
            (∫ t : ℝ, perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)) := by
  have hreu : (1 - ρ).re = 1 - ρ.re := by simp
  have hp2 : ((1 / 2 : ℝ) - ρ.re) < 2 := by linarith
  have hu : ((1 / 2 : ℝ) - ρ.re) < (1 - ρ).re ∧ (1 - ρ).re < 2 := by
    rw [hreu]; exact ⟨by linarith, by linarith⟩
  have hH : ∀ R : ℝ, DifferentiableOn ℂ (perronH K Y ρ)
      (Set.uIcc ((1 / 2 : ℝ) - ρ.re) 2 ×ℂ Set.uIcc (-R) R) := fun R =>
    perronH_differentiable K Y hY ρ (p := (1 / 2 : ℝ) - ρ.re) (q := 2) (R := R)
      (by linarith) (by norm_num) (by linarith)
  have hdec : ∀ R : ℝ, 1 ≤ R →
      ∀ s ∈ (Set.uIcc ((1 / 2 : ℝ) - ρ.re) 2 ×ℂ Set.uIcc (-R) R), s ≠ 1 - ρ → s ≠ 0 →
      perronInt K Y ρ s = residueTerm K Y ρ / (s - (1 - ρ)) + perronH K Y ρ s :=
    fun _R _hR s _hs hsu hs0 => perronInt_eq_residueTerm_add_perronH K Y ρ hζ hρ1 hs0 hsu
  have hhor := perronH_horizontal K Y hY ρ (p := (1 / 2 : ℝ) - ρ.re) (q := 2)
      (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)
  have hpint : Integrable (fun t : ℝ =>
      perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)) :=
    perronInt_integrable K Y hY ρ hζ hρ1 (c := (1 / 2 : ℝ) - ρ.re)
      (by linarith) (by linarith) (by rw [hreu]; linarith) (by linarith) (by linarith)
  have hqint : Integrable (fun t : ℝ => perronInt K Y ρ (2 + (t : ℂ) * Complex.I)) := by
    simpa using (perronInt_integrable K Y hY ρ hζ hρ1 (c := (2 : ℝ))
      (by linarith) (by linarith) (by rw [hreu]; linarith) (by norm_num) (by norm_num)
        : Integrable (fun t : ℝ => perronInt K Y ρ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
  exact perronShift_divided (perronInt K Y ρ) (perronH K Y ρ) ((1 / 2 : ℝ) - ρ.re) 2 hp2
    (1 - ρ) (residueTerm K Y ρ) hu hH hdec hhor.1 hhor.2 hpint hqint

end Work.ZeroDensity.Ingham
