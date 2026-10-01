import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral Set Filter
open scoped Interval Topology

/-- Cauchy's theorem for the rectangle with vertical sides on `Re = a`, `Re = b` and horizontal
sides on `Im = -T`, `Im = T`, stated for a function `F` differentiable on the closed rectangle. -/
private lemma rect_vert_identity_F {a b T : ℝ} {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F (Set.uIcc a b ×ℂ Set.uIcc (-T) T)) :
    (∫ y : ℝ in (-T)..T, F ((b : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y : ℝ in (-T)..T, F ((a : ℂ) + (y : ℂ) * Complex.I))
      = -Complex.I * ((∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I))
        - ∫ x : ℝ in a..b, F ((x : ℂ) - (T : ℂ) * Complex.I)) := by
  set z : ℂ := (a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I with hzdef
  set w : ℂ := (b : ℂ) + (T : ℂ) * Complex.I with hwdef
  have hzre : z.re = a := by simp [z]
  have hzim : z.im = -T := by simp [z]
  have hwre : w.re = b := by simp [w]
  have hwim : w.im = T := by simp [w]
  have hd' : DifferentiableOn ℂ F ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    rw [hzre, hwre, hzim, hwim]; exact hd
  have hraw := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hd'
  rw [hzre, hwre, hzim, hwim] at hraw
  simp only [smul_eq_mul] at hraw
  have hPI : (∫ x : ℝ in a..b, F ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = ∫ x : ℝ in a..b, F ((x : ℂ) - (T : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg F
    push_cast
    ring
  rw [hPI] at hraw
  have key : Complex.I * ((∫ y : ℝ in (-T)..T, F ((b : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y : ℝ in (-T)..T, F ((a : ℂ) + (y : ℂ) * Complex.I)))
      = (∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I))
        - ∫ x : ℝ in a..b, F ((x : ℂ) - (T : ℂ) * Complex.I) := by
    linear_combination hraw
  have h1 : -((Complex.I : ℂ) * Complex.I) = 1 := by rw [Complex.I_mul_I]; norm_num
  calc (∫ y : ℝ in (-T)..T, F ((b : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, F ((a : ℂ) + (y : ℂ) * Complex.I))
      = (-((Complex.I : ℂ) * Complex.I)) *
          ((∫ y : ℝ in (-T)..T, F ((b : ℂ) + (y : ℂ) * Complex.I))
            - (∫ y : ℝ in (-T)..T, F ((a : ℂ) + (y : ℂ) * Complex.I))) := by
        rw [h1, one_mul]
    _ = -(Complex.I * (Complex.I * ((∫ y : ℝ in (-T)..T, F ((b : ℂ) + (y : ℂ) * Complex.I))
            - (∫ y : ℝ in (-T)..T, F ((a : ℂ) + (y : ℂ) * Complex.I))))) := by ring
    _ = -(Complex.I * ((∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I))
            - ∫ x : ℝ in a..b, F ((x : ℂ) - (T : ℂ) * Complex.I))) := by rw [key]
    _ = -Complex.I * ((∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I))
            - ∫ x : ℝ in a..b, F ((x : ℂ) - (T : ℂ) * Complex.I)) := by ring

theorem vertical_contour_shift
    (F : ℂ → ℂ) (p q : ℝ) (hpq : p ≤ q)
    (hF : ∀ R : ℝ, DifferentiableOn ℂ F (Set.uIcc p q ×ℂ Set.uIcc (-R) R))
    (hIp : MeasureTheory.Integrable (fun t : ℝ => F ((p : ℂ) + (t : ℂ) * Complex.I)))
    (hIq : MeasureTheory.Integrable (fun t : ℝ => F ((q : ℂ) + (t : ℂ) * Complex.I)))
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, F ((x : ℂ) + (R : ℂ) * Complex.I))
        Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, F ((x : ℂ) - (R : ℂ) * Complex.I))
        Filter.atTop (nhds 0)) :
    (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      = ∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I) := by
  rcases eq_or_lt_of_le hpq with hpq' | hpq'
  · subst hpq'
    rfl
  · have hVb := intervalIntegral_tendsto_integral hIq tendsto_neg_atTop_atBot tendsto_id
    have hVa := intervalIntegral_tendsto_integral hIp tendsto_neg_atTop_atBot tendsto_id
    have hLHS : Filter.Tendsto
        (fun T : ℝ => (∫ y : ℝ in (-T)..T, F ((q : ℂ) + (y : ℂ) * Complex.I))
          - (∫ y : ℝ in (-T)..T, F ((p : ℂ) + (y : ℂ) * Complex.I)))
        Filter.atTop (nhds ((∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
          - ∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I))) := hVb.sub hVa
    have hRHS : Filter.Tendsto
        (fun T : ℝ => -Complex.I * ((∫ x : ℝ in p..q, F ((x : ℂ) + (T : ℂ) * Complex.I))
          - ∫ x : ℝ in p..q, F ((x : ℂ) - (T : ℂ) * Complex.I)))
        Filter.atTop (nhds 0) := by
      have h := (htop.sub hbot).const_mul (-Complex.I)
      simpa using h
    have heq : (fun T : ℝ => (∫ y : ℝ in (-T)..T, F ((q : ℂ) + (y : ℂ) * Complex.I))
          - (∫ y : ℝ in (-T)..T, F ((p : ℂ) + (y : ℂ) * Complex.I)))
        =ᶠ[Filter.atTop] (fun T : ℝ => -Complex.I *
          ((∫ x : ℝ in p..q, F ((x : ℂ) + (T : ℂ) * Complex.I))
            - ∫ x : ℝ in p..q, F ((x : ℂ) - (T : ℂ) * Complex.I))) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact rect_vert_identity_F (hF T)
    have hzero : (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
        - ∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I) = 0 :=
      tendsto_nhds_unique (hLHS.congr' heq) hRHS
    exact sub_eq_zero.mp hzero

end Commons.Analysis.Complex