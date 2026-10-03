/-
# The kernel of the modulated Ionescu–Wainger bump `φ_{N,k₁,t}`

This file identifies the inverse Fourier transform of the modulated bump
`varphiNt N k₁ t ξ = φ_N(ξ) e(N t ξ)` of Krause–Mirek–Tao with the *shifted
Calderón–Zygmund kernel* of `Work.Analysis.CzShift`:

  `𝓕⁻ (φ_{N,k₁,t}) (x) = (lacσ N k₁)⁻¹ Ψ((x + N t) / lacσ N k₁)`
                       `= shiftKernel Ψ (lacσ N k₁) (-(N t)/lacσ N k₁) x`,

where `Ψ = 𝓕⁻ lacψ`, `lacψ (ξ) = η(ξ) - η(2ξ)` is the fixed mean-zero bump and
`lacσ N k₁ = 2 ^ (Log N - k₁)` is its frequency scale.  This is the identity that
puts the family `ξ ↦ φ_{N,t}(ξ)` into the Appendix-B shape
`ξ ↦ ψ(σ ξ) e(λ σ ξ)` with `λ σ = N t`, so that the shifted Calderón–Zygmund
theorem `cz_shift_lp` (Appendix B, `cz-shift`) applies to it.

The proof is the two elementary Fourier facts, both of which are already in the
workspace:

* modulation — multiplying a symbol by `ee (a ·)` translates the inverse
  transform by `a` (`fourierInv_mul_ee`, proved here by the integral formula,
  using that `ee` is `Real.fourierChar` and that `Real.fourierChar` is an
  additive character);
* dilation — `𝓕⁻ (fun ξ => η (c ξ)) x = c⁻¹ 𝓕⁻ η (x / c)` for `c > 0`
  (`fourierInv_comp_mul`, a repackaging of `fourierInv_comp_div` of
  `fourierInv_comp_div.lean` / `EtaMult.lean`).

The scale identification `varphiNt N k₁ t = fun ξ => lacψ (lacσ N k₁ * ξ) * ee (N t ξ)`
is `varphiNt_shiftForm` (`lacunaryBumpScaleIdentity.lean`), together with the two
elementary facts `lacσ N k₁ = 2 ^ (Log N - k₁)` (real exponent form) and
`lacψ = bumpF`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacBumpDefs
import Submission.Work.KMTAreas.A7.lacunaryBumpScaleIdentity

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-! ## The scale `lacσ` and the bump `lacψ` -/

/-- The fixed bump of `lacunaryBumpScaleIdentity` is the mean-zero bump `lacψ`. -/
lemma bumpF_eq_lacψ : bumpF = lacψ := rfl

/-- `lacσ N k₁ = 2 ^ (Log N - k₁)` written with a real exponent, as in `varphiN`. -/
lemma lacσ_eq (N k₁ : ℕ) :
    lacσ N k₁ = (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) := by
  rw [lacσ, ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/-- The frequency scale `lacσ` is positive. -/
lemma lacσ_pos (N k₁ : ℕ) : 0 < lacσ N k₁ := by
  rw [lacσ]
  exact zpow_pos (by norm_num) _

/-- The frequency scale `lacσ` is nonzero. -/
lemma lacσ_ne_zero (N k₁ : ℕ) : lacσ N k₁ ≠ 0 := (lacσ_pos N k₁).ne'

/-- `ee` is the complex-valued exponential character `Real.fourierChar`. -/
lemma ee_eq_fourierChar (z : ℝ) : ee z = (Real.fourierChar z : ℂ) := by
  rw [ee, Real.fourierChar_apply]
  push_cast
  ring

/-! ## Modulation and dilation of the inverse Fourier transform -/

/-- The exponential `ee` is an additive character: `ee (x + y) = ee x * ee y`. -/
lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Modulation.**  Multiplying a symbol by `ee (a ·)` translates its inverse
Fourier transform by `a`. -/
lemma fourierInv_mul_ee (g : ℝ → ℂ) (a y : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => g ξ * ee (a * ξ)) y
      = FourierTransformInv.fourierInv g (y + a) := by
  rw [fourierInv_eq_real, fourierInv_eq_real]
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def, Circle.smul_def, ← ee_eq_fourierChar (v * y),
    ← ee_eq_fourierChar (v * (y + a))]
  have hcirc : ee (v * y) * ee (a * v) = ee (v * (y + a)) := by
    rw [← ee_add]
    congr 1
    ring
  calc ee (v * y) * (g v * ee (a * v))
      = (ee (v * y) * ee (a * v)) * g v := by ring
    _ = ee (v * (y + a)) * g v := by rw [hcirc]

/-- **Dilation.**  Replacing the symbol `η` by `ξ ↦ η (c ξ)` (with `c > 0`) dilates the
inverse Fourier transform by `c`: `𝓕⁻ (η (c ·)) x = c⁻¹ 𝓕⁻ η (x / c)`. -/
lemma fourierInv_comp_mul (η : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => FourierTransformInv.fourierInv (fun ξ : ℝ => η (c * ξ)) x)
      = fun x : ℝ => (c : ℂ)⁻¹ * FourierTransformInv.fourierInv η (x / c) := by
  have h := fourierInv_comp_div η (c := c⁻¹) (inv_pos.mpr hc)
  have hsym : (fun θ : ℝ => η (θ / c⁻¹)) = fun θ : ℝ => η (c * θ) := by
    funext θ
    rw [div_inv_eq_mul, mul_comm]
  funext x
  rw [← hsym, congrFun h x, Complex.ofReal_inv, inv_mul_eq_div]
  rfl

/-! ## The inverse Fourier transform of the bump -/

/-- **The kernel of the bump.**  For `σ > 0` and `a : ℝ`, the inverse Fourier transform of
`ξ ↦ lacψ (σ ξ) · ee (a ξ)` is the dilated seed `x ↦ σ⁻¹ Ψ((x + a)/σ)`, where `Ψ = 𝓕⁻ lacψ`. -/
lemma fourierInv_lacψ_shift (Ψ : ℝ → ℝ)
    (hΨ : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv lacψ u)
    {σ a : ℝ} (hσ : 0 < σ) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => lacψ (σ * ξ) * ee (a * ξ)) x
      = (σ : ℂ)⁻¹ * (Ψ ((x + a) / σ) : ℂ) := by
  rw [fourierInv_mul_ee (g := fun ξ : ℝ => lacψ (σ * ξ)) a x]
  rw [congrFun (fourierInv_comp_mul lacψ hσ) (x + a)]
  rw [← hΨ]

/-- The modulated bump is the fixed bump `lacψ` at the frequency scale `lacσ N k₁`,
modulated at the shift `N t`. -/
lemma varphiNt_lacψ_form (N k₁ : ℕ) (hk₁ : 1 ≤ k₁) (t : ℝ) :
    varphiNt N k₁ t = fun ξ : ℝ => lacψ (lacσ N k₁ * ξ) * ee (((N : ℝ) * t) * ξ) := by
  have h := varphiNt_shiftForm k₁ hk₁ N t
  have h2 : (fun ξ : ℝ =>
        bumpF ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * ξ)
          * ee (((N : ℝ) * t) * ξ))
      = fun ξ : ℝ => lacψ (lacσ N k₁ * ξ) * ee (((N : ℝ) * t) * ξ) := by
    funext ξ
    rw [lacσ_eq N k₁, bumpF_eq_lacψ]
  exact h.trans h2

/-! ## The main identity -/

/-- **The kernel of the modulated bump.**  The inverse Fourier transform of `varphiNt N k₁ t` is
the shifted Calderón–Zygmund kernel attached to the seed `Ψ = 𝓕⁻ lacψ`, the scale
`lacσ N k₁ = 2 ^ (Log N - k₁)` and the shift `-(N t)/lacσ N k₁`. -/
theorem lacBumpKernel (Ψ : ℝ → ℝ)
    (hΨ : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv Work.KMTAreas.A7.lacψ u)
    (N k₁ : ℕ) (hk₁ : 1 ≤ k₁) (t : ℝ) :
    (fun x : ℝ => FourierTransformInv.fourierInv (Work.KMTAreas.A7.varphiNt N k₁ t) x)
      = fun x : ℝ => Work.Analysis.CzShift.shiftKernel Ψ (Work.KMTAreas.A7.lacσ N k₁)
          (-((N : ℝ) * t) / Work.KMTAreas.A7.lacσ N k₁) x := by
  funext x
  rw [varphiNt_lacψ_form N k₁ hk₁ t]
  rw [fourierInv_lacψ_shift Ψ hΨ (lacσ_pos N k₁) x]
  rw [Work.Analysis.CzShift.shiftKernel]
  rw [Complex.ofReal_mul, Complex.ofReal_inv]
  congr 1
  have hσnz : lacσ N k₁ ≠ 0 := lacσ_ne_zero N k₁
  have harg : (-((N : ℝ) * t) / lacσ N k₁) * lacσ N k₁ = -((N : ℝ) * t) := by
    field_simp
  rw [show (x + (N : ℝ) * t) / lacσ N k₁
        = (x - (-((N : ℝ) * t) / lacσ N k₁) * lacσ N k₁) / lacσ N k₁ from by
      rw [harg]
      ring]

end

end Work.KMTAreas.A7
