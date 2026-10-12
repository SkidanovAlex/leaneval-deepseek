import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Work.BoseRowsFS.CoulShift

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Mathlib's normalised Fourier transform turns a right translation into a phase factor:
`𝓕 (g(·+a)) p = e^{2πi⟪a,p⟫} · 𝓕 g p`.  This is
`VectorFourier.fourierIntegral_comp_add_right` with `L = innerₗ` and `𝐞 = Real.fourierChar`,
spelled out in the complex exponential.  Only the *norm* of the phase is used below, so no sign
convention is at stake. -/
lemma fourier_comp_add_right_phase (g : ℝ³ → ℂ) (a p : ℝ³) :
    𝓕 (fun z : ℝ³ => g (z + a)) p
      = Complex.exp (((2 * Real.pi * inner ℝ a p : ℝ) : ℂ) * Complex.I) * 𝓕 g p := by
  have h := VectorFourier.fourierIntegral_comp_add_right (e := Real.fourierChar) (μ := volume)
    (L := innerₗ ℝ³) g a
  have hw := congrFun h p
  rw [Circle.smul_def, Real.fourierChar_apply] at hw
  exact hw

/-- Pointwise additivity of the Fourier transform of integrable functions on `ℝ³`. -/
lemma fourier_add_of_integrable {f g : ℝ³ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (fun x => f x + g x) = 𝓕 f + 𝓕 g := by
  have h := VectorFourier.fourierIntegral_add (e := Real.fourierChar) (μ := volume)
    (L := innerₗ ℝ³) Real.continuous_fourierChar continuous_inner hf hg
  exact h

/-- The Fourier transform of `F + F(·+a)` at `q` is `𝓕 F q + e^{2πi⟪a,q⟫} 𝓕 F q`; the phase has
modulus one, so the norm is at most `2 ‖𝓕 F q‖`. -/
theorem fourier_sum_shift_norm_le {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hF : MeasureTheory.Integrable F) (a q : EuclideanSpace ℝ (Fin 3)) :
    ‖FourierTransform.fourier (fun x => F x + F (x + a)) q‖ ≤ 2 * ‖FourierTransform.fourier F q‖ := by
  have hFa : Integrable (fun x : ℝ³ => F (x + a)) := hF.comp_add_right a
  have hadd : 𝓕 (fun x : ℝ³ => F x + F (x + a)) q
      = 𝓕 F q + 𝓕 (fun x : ℝ³ => F (x + a)) q :=
    congrFun (fourier_add_of_integrable hF hFa) q
  rw [hadd, fourier_comp_add_right_phase F a q]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, two_mul]

end Work.BoseRowsFS.CoulShift
