import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.lowMult_eq_kernel_integral
import Submission.Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff
import Submission.Work.OneBodyKin.kinFT_sub_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.lowMult_add_of_pos`

Linearity of FS's low-momentum multiplier in the one-body state, for `κ > 0`:

  `lowMult fc κ ℓ (ψ + φ) x = lowMult fc κ ℓ ψ x + lowMult fc κ ℓ φ x`.

## Route

Write the momentum-space coefficient of the multiplier as

  `lowMultCoeff fc κ ℓ G p = f(‖p‖/κ) · (θ_ΛG)^(p)`,

so that (purely by making the phase explicit, no analysis) the multiplier is the *inverse*
Fourier transform of the coefficient:

  `lowMult fc κ ℓ G x = (2π)⁻³ · (kinFT (lowMultCoeff fc κ ℓ G) (−x)).re`

(identical to `lowMult_eq_kinFT_lowCoeff` of the sibling
`integrable_ind_mul_lowMult_int`).  Linearity is then a formal consequence of two
additivities:

* the coefficient is additive, `lowMultCoeff (ψ+φ) = lowMultCoeff ψ + lowMultCoeff φ`,
  because the box extension `θ_Λ` is additive and `kinFT` is additive on the two
  integrable extensions (`1_{Λ}ψ`, `1_{Λ}φ ∈ L¹`);
* `kinFT` is additive on the two integrable coefficients `lowMultCoeff ψ`, `lowMultCoeff φ`
  (`HighMassAux.integrable_lowMultCoeff`, using the compact support of `f(·/κ)` for `κ > 0`).

The integrability of the extensions is `IntegrableOn ψ (acube ℓ)` for the continuous `ψ`,
which holds for every `ℓ` since `acube ℓ` is compact (whence finite measure).
-/

namespace Work.BoseFixB3.CS.Pieces

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The momentum-space coefficient of the low-momentum multiplier applied to (the box
extension of) `G`: `p ↦ f(‖p‖/κ) · kinFT (1_Λ · G) p`.  Its `L¹`-integrability is
`Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff`. -/
private def lowMultCoeff (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (G : E3 → ℝ) (p : E3) : ℂ :=
  ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
    Submission.BoseGases.kinFT
      (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator G z : ℝ) : ℂ)) p

/-- **`lowMult` is the inverse Fourier transform of the coefficient.**  The `p`-integral of
the definition is the `kinFT` of `lowMultCoeff` at the momentum `−x`. -/
private lemma lowMult_eq_kinFT_lowMultCoeff (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (G : E3 → ℝ) (x : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ G x
      = ((2 * Real.pi) ^ 3)⁻¹
          * (Submission.BoseGases.kinFT (lowMultCoeff fc κ ℓ G) (-x)).re := by
  unfold Work.BoseBoxFix.lowMult lowMultCoeff Submission.BoseGases.kinFT
  rw [Complex.re_ofReal_mul]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  have he : Complex.exp (Complex.I * (inner ℝ p x : ℂ))
      = Complex.exp (-(Complex.I * (inner ℝ (-x) p : ℂ))) := by
    rw [inner_neg_left, Complex.ofReal_neg, mul_neg, neg_neg, real_inner_comm]
  rw [he, mul_assoc]

/-- `kinFT` is additive on integrable states. -/
private lemma kinFT_add {g h : E3 → ℂ} (hg : Integrable g) (hh : Integrable h) (p : E3) :
    Submission.BoseGases.kinFT (g + h) p
      = Submission.BoseGases.kinFT g p + Submission.BoseGases.kinFT h p := by
  have hfun : (g + h : E3 → ℂ) = g - (-1 : ℂ) • h := by
    funext z
    simp
  rw [hfun]
  simpa using Work.OneBodyKin.kinFT_sub_smul hg hh (-1 : ℂ) p

/-- The box extension `θ_Λ` is additive. -/
private lemma indicator_add_acube (ℓ : ℝ) (ψ φ : E3 → ℝ) :
    (Submission.BoseGases.acube ℓ).indicator (ψ + φ)
      = (Submission.BoseGases.acube ℓ).indicator ψ
        + (Submission.BoseGases.acube ℓ).indicator φ := by
  funext z
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

/-- The (complexified) box extension is additive. -/
private lemma ofReal_indicator_add_acube (ℓ : ℝ) (ψ φ : E3 → ℝ) :
    (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator (ψ + φ) z : ℝ) : ℂ))
      = (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ))
        + (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator φ z : ℝ) : ℂ)) := by
  funext z
  have h := congrFun (indicator_add_acube ℓ ψ φ) z
  simp only [Pi.add_apply] at h
  simp only [Pi.add_apply, h, Complex.ofReal_add]

/-- The coefficient is additive in the state. -/
private lemma lowMultCoeff_add (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) {ψ φ : E3 → ℝ}
    (hψ : Integrable (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)))
    (hφ : Integrable (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator φ z : ℝ) : ℂ))) :
    lowMultCoeff fc κ ℓ (ψ + φ) = lowMultCoeff fc κ ℓ ψ + lowMultCoeff fc κ ℓ φ := by
  funext p
  rw [Pi.add_apply]
  simp only [lowMultCoeff]
  rw [ofReal_indicator_add_acube ℓ ψ φ, kinFT_add hψ hφ p]
  ring

theorem lowMult_add_of_pos (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    {ψ φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) (hφ : Continuous φ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFix.lowMult fc κ ℓ (ψ + φ) x
      = Work.BoseBoxFix.lowMult fc κ ℓ ψ x + Work.BoseBoxFix.lowMult fc κ ℓ φ x := by
  classical
  have hcs : HasCompactSupport (fun p : E3 => fc.f (‖p‖ / κ)) :=
    Work.BoseFixB3.HighMass.lowcut_symbol_hasCompactSupport (fc := fc) (κ := κ) hκ
  have hmeas : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  -- the box extensions of the continuous states are `L¹`
  have hψon : IntegrableOn ψ (Submission.BoseGases.acube ℓ) :=
    ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ) hψ.continuousOn
  have hφon : IntegrableOn φ (Submission.BoseGases.acube ℓ) :=
    ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ) hφ.continuousOn
  have hIψ : Integrable
      (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) :=
    (MeasureTheory.IntegrableOn.integrable_indicator hψon hmeas).ofReal
  have hIφ : Integrable
      (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator φ z : ℝ) : ℂ)) :=
    (MeasureTheory.IntegrableOn.integrable_indicator hφon hmeas).ofReal
  -- the coefficients are `L¹`
  have hcψ : Integrable (lowMultCoeff fc κ ℓ ψ) :=
    Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff (fc := fc) (κ := κ) (ℓ := ℓ) hψon hcs
  have hcφ : Integrable (lowMultCoeff fc κ ℓ φ) :=
    Work.BoseFixB3.HighMassAux.integrable_lowMultCoeff (fc := fc) (κ := κ) (ℓ := ℓ) hφon hcs
  rw [lowMult_eq_kinFT_lowMultCoeff fc κ ℓ (ψ + φ) x,
    lowMult_eq_kinFT_lowMultCoeff fc κ ℓ ψ x,
    lowMult_eq_kinFT_lowMultCoeff fc κ ℓ φ x,
    lowMultCoeff_add fc κ ℓ hIψ hIφ, kinFT_add hcψ hcφ (-x), Complex.add_re,
    mul_add]

end

end Work.BoseFixB3.CS.Pieces
