import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs

/-!
# The patched Perron integrand of the zero detector, and the decomposition at `w = 1 - ρ`

The Perron integrand `perronInt K Y ρ w = Γ(w) Y^w ζ(ρ+w) M_K(ρ+w)` has two singularities in the
strip `1/2 - Re ρ ≤ Re w ≤ 2`: the pole of `Γ` at `w = 0` and the pole of `ζ(ρ+·)` at `w = 1 - ρ`.

At a zero `ρ` of `ζ` the first of these is **removable**: writing `Γ(w) = Γ(w+1)/w` and
`ζ(ρ+w) = ζ₁(ρ+w)/(ρ+w-1)` with `ζ₁ = riemannZeta₁` the entire function determined by
`ζ(s)(s-1) = ζ₁(s)` and `ζ₁(1) = 1`, and using `ζ₁(ρ) = (ρ-1)ζ(ρ) = 0`, we get

`perronInt K Y ρ w = M w / (w - (1-ρ))`,  `M w = Γ(w+1)·dslope (ζ₁(ρ+·)) 0 w ·Y^w·M_K(ρ+w)`,

**off** the two points `w = 0` and `w = 1 - ρ`.  `M` is entire (`perronM`), the value `M (1-ρ)` is
the residue `residueTerm K Y ρ` of the pole at `w = 1-ρ`, and the patched integrand
`perronH K Y ρ = dslope (perronM K Y ρ) (1-ρ)` is therefore entire, with

`perronInt K Y ρ w = residueTerm K Y ρ / (w - (1-ρ)) + perronH K Y ρ w`

for `w ∉ {0, 1-ρ}`.
-/

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- The entire factor `M` of the patched Perron integrand:
`M w = Γ(w+1) · dslope (fun t => ζ₁ (ρ+t)) 0 w · Y^w · M_K(ρ+w)`, where `ζ₁ = riemannZeta₁`
satisfies `ζ(s) = ζ₁(s)/(s-1)` for `s ≠ 1` and `ζ₁(1) = 1`. -/
noncomputable def perronM (K : ℕ) (Y : ℝ) (ρ w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 w
    * (Y : ℂ) ^ w * MK K (ρ + w)

/-- The patched (entire) Perron integrand `dslope (perronM K Y ρ) (1-ρ)`. -/
noncomputable def perronH (K : ℕ) (Y : ℝ) (ρ w : ℂ) : ℂ :=
  dslope (perronM K Y ρ) (1 - ρ) w

/-- At a zero `ρ ≠ 1` of `ζ`, one has `ζ₁(ρ) = (ρ-1)ζ(ρ) = 0`. -/
lemma riemannZeta₁_eq_zero_of_riemannZeta_eq_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) : riemannZeta₁ ρ = 0 := by
  have h := riemannZeta_eq_inv_sub_mul (s := ρ) hρ1
  rw [hζ] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr hρ1))

/-- **The patched decomposition of the Perron integrand.**  Off the two poles `w = 0` and
`w = 1 - ρ`,

`Γ(w) Y^w ζ(ρ+w) M_K(ρ+w) = M w / (w - (1-ρ))`.

(At a zero `ρ ≠ 1` of `ζ` the singularity of `Γ(w)ζ(ρ+w)` at `w = 0` is removable; the identity
fails only at the single point `w = 0`, where `perronInt` is given the value `Γ(0)·0 = 0` whereas
the right-hand side has the removable-singularity value `ζ'(ρ)M_K(ρ)`.) -/
theorem perronInt_eq_perronM_div (K : ℕ) (Y : ℝ) (ρ : ℂ) (hζ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) {w : ℂ} (hw0 : w ≠ 0) (hwu : w ≠ 1 - ρ) :
    perronInt K Y ρ w = perronM K Y ρ w / (w - (1 - ρ)) := by
  have hz : riemannZeta₁ ρ = 0 := riemannZeta₁_eq_zero_of_riemannZeta_eq_zero hζ hρ1
  have hkey : riemannZeta₁ (ρ + w) = w * dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 w := by
    have hb := sub_smul_dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 w
    simp only [sub_zero, smul_eq_mul, add_zero, hz, sub_zero] at hb
    exact hb.symm
  have hwne : ρ + w ≠ 1 := by
    intro h
    exact hwu (by linear_combination h)
  have hζw : riemannZeta (ρ + w) = (ρ + w - 1)⁻¹ * riemannZeta₁ (ρ + w) :=
    riemannZeta_eq_inv_sub_mul hwne
  have hΓ : Complex.Gamma w = Complex.Gamma (w + 1) / w := by
    rw [Complex.Gamma_add_one w hw0]
    field_simp
  have harg : ρ + w - 1 = w - (1 - ρ) := by ring
  rw [perronInt, perronM, hΓ, hζw, hkey, harg]
  have hwne' : w - (1 - ρ) ≠ 0 := sub_ne_zero.mpr hwu
  field_simp

/-- **The value of `M` at the pole**: `M (1-ρ) = Γ(1-ρ) Y^{1-ρ} M_K(1) = residueTerm K Y ρ`.
Indeed `dslope (ζ₁(ρ+·)) 0 (1-ρ) = (ζ₁(1) - ζ₁(ρ))/(1-ρ) = 1/(1-ρ)` and
`Γ(2-ρ) = (1-ρ)Γ(1-ρ)`. -/
theorem perronM_pole (K : ℕ) (Y : ℝ) (ρ : ℂ) (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    perronM K Y ρ (1 - ρ) = residueTerm K Y ρ := by
  have hz : riemannZeta₁ ρ = 0 := riemannZeta₁_eq_zero_of_riemannZeta_eq_zero hζ hρ1
  have hu : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have h1 : ρ + (1 - ρ) = 1 := by ring
  have h0 : ρ + (0 : ℂ) = ρ := by ring
  have hds : dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 (1 - ρ) = (1 - ρ)⁻¹ := by
    rw [dslope_of_ne _ hu, slope_def_field, h1, h0, riemannZeta₁_one, hz]
    norm_num
  have hΓ : Complex.Gamma ((1 - ρ) + 1) = (1 - ρ) * Complex.Gamma (1 - ρ) :=
    Complex.Gamma_add_one (1 - ρ) hu
  rw [perronM, residueTerm, hds, hΓ, h1]
  field_simp

/-- The patched integrand is the Perron integrand minus the single residue kernel: for
`w ∉ {0, 1-ρ}`,

`perronInt K Y ρ w = residueTerm K Y ρ / (w - (1-ρ)) + perronH K Y ρ w`. -/
theorem perronInt_eq_residueTerm_add_perronH (K : ℕ) (Y : ℝ) (ρ : ℂ) (hζ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) {w : ℂ} (hw0 : w ≠ 0) (hwu : w ≠ 1 - ρ) :
    perronInt K Y ρ w = residueTerm K Y ρ / (w - (1 - ρ)) + perronH K Y ρ w := by
  rw [perronInt_eq_perronM_div K Y ρ hζ hρ1 hw0 hwu, perronH,
    ← perronM_pole K Y ρ hζ hρ1]
  have hsm : perronM K Y ρ w
      = perronM K Y ρ (1 - ρ) + (w - (1 - ρ)) * dslope (perronM K Y ρ) (1 - ρ) w := by
    have hb : (w - (1 - ρ)) * dslope (perronM K Y ρ) (1 - ρ) w
        = perronM K Y ρ w - perronM K Y ρ (1 - ρ) := by
      simpa [smul_eq_mul] using (sub_smul_dslope (perronM K Y ρ) (1 - ρ) w)
    rw [hb]
    ring
  have hsune : w - (1 - ρ) ≠ 0 := sub_ne_zero.mpr hwu
  rw [hsm]
  field_simp

end Work.ZeroDensity.Ingham
