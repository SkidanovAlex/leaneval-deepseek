import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound

namespace Commons.Analysis.Complex

open Filter MeasureTheory intervalIntegral
open scoped Topology

private lemma rectInt_strip_eq_gen (A B T : ℝ) (F : ℂ → ℂ) :
    Commons.NumberTheory.Zeta.rectInt ((A : ℂ) - (T : ℂ) * _root_.Complex.I)
        ((B : ℂ) + (T : ℂ) * _root_.Complex.I) F =
      (∫ x : ℝ in A..B, F ((x : ℂ) - (T : ℂ) * _root_.Complex.I)) -
      (∫ x : ℝ in A..B, F ((x : ℂ) + (T : ℂ) * _root_.Complex.I)) +
      _root_.Complex.I * (∫ y : ℝ in (-T)..T, F ((B : ℂ) + (y : ℂ) * _root_.Complex.I)) -
      _root_.Complex.I * (∫ y : ℝ in (-T)..T, F ((A : ℂ) + (y : ℂ) * _root_.Complex.I)) := by
  have hzre : (((A : ℂ) - (T : ℂ) * _root_.Complex.I)).re = A := by
    simp [Complex.sub_re, Complex.mul_re]
  have hzim : (((A : ℂ) - (T : ℂ) * _root_.Complex.I)).im = -T := by
    simp [Complex.sub_im, Complex.mul_im]
  have hwre : (((B : ℂ) + (T : ℂ) * _root_.Complex.I)).re = B := by
    simp [Complex.add_re, Complex.mul_re]
  have hwim : (((B : ℂ) + (T : ℂ) * _root_.Complex.I)).im = T := by
    simp [Complex.add_im, Complex.mul_im]
  unfold Commons.NumberTheory.Zeta.rectInt
  rw [hzre, hwre, hzim, hwim]
  simp only [Complex.ofReal_neg, smul_eq_mul, neg_mul, sub_eq_add_neg]

theorem rectInt_tendsto_vertical_gen {F : ℂ → ℂ} {A B : ℝ} (hAB : A < B)
    (hBint : MeasureTheory.Integrable (fun t : ℝ => F ((B : ℂ) + (t : ℂ) * Complex.I)))
    (hAint : MeasureTheory.Integrable (fun t : ℝ => F ((A : ℂ) + (t : ℂ) * Complex.I)))
    (hu : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B, F ((x : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hd : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B, F ((x : ℂ) - (T : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun T : ℝ => Commons.NumberTheory.Zeta.rectInt ((A : ℂ) - (T : ℂ) * Complex.I)
        ((B : ℂ) + (T : ℂ) * Complex.I) F) Filter.atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I))))) := by
  have hABle : A ≤ B := le_of_lt hAB
  have hu' := hu
  have hnegtop : Tendsto (fun T : ℝ => -T) atTop atBot := by
    rw [Filter.tendsto_atBot]
    intro a
    filter_upwards [Filter.eventually_ge_atTop (-a)] with T hT
    linarith
  have hC : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F ((B : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds (∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hBint hnegtop tendsto_id
  have hD : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F ((A : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hAint hnegtop tendsto_id
  have hcomb := ((hd.sub hu').add (hC.const_mul Complex.I)).sub (hD.const_mul Complex.I)
  simp only [sub_zero, zero_add] at hcomb
  have hlim : Complex.I * ((∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I)))
      = Complex.I * (∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I * (∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * Complex.I)) := by ring
  rw [hlim]
  refine hcomb.congr' ?_
  filter_upwards with T
  exact (rectInt_strip_eq_gen A B T F).symm

end Commons.Analysis.Complex
