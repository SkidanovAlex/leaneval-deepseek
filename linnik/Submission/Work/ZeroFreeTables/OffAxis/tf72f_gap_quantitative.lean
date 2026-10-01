import Mathlib
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.ZeroFreeTables.tf72fK_t_moment_nonneg
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.tf72Tzero
import Submission.Work.OffAxis.MomentStep103GapQuant

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.ZeroFreeTables.OffAxis

/-! ## `F` of the test function `tf72T (6/7)` as an integral over `[0, 7/3]`

The test function `T = tf72T (6/7)` has support `[0, 2/(6/7)] = [0, 7/3]` and
`T.f = tf72f (6/7)`, so its Laplace transform on the real axis is the explicit integral
`T.F z = ∫_0^{7/3} e^{-zt} tf72f (6/7) t dt`. -/

private lemma tf72T67_F_eq_int (z : ℝ) :
    (tf72T ((6:ℝ)/7) (by norm_num)).F z
      = ∫ t in (0:ℝ)..(7/3), Real.exp (-(z * t)) * tf72f ((6:ℝ)/7) t := by
  set T : TestFn := tf72T ((6:ℝ)/7) (by norm_num) with hT
  have hx0 : T.x₀ = 7/3 := by
    rw [hT]
    show (2:ℝ) / ((6:ℝ)/7) = 7/3
    norm_num
  have hf : T.f = tf72f ((6:ℝ)/7) := by
    rw [hT]
    rfl
  have h := TestFn_F_eq_integral T z
  rw [hx0, hf] at h
  rw [hT] at h
  exact h

/-! ## The quantitative gap in the `F`-vocabulary

`F (-lam) - 2 F (6/7 - lam) = tf72fPhi lam` for every real `lam` (this is
`tf72fL_eq_Phi`, after writing `F` as the integral over `[0, 7/3]`), so the combination

  `F (-6/7) - F (-lam) - 2 (F 0 - F (6/7 - lam)) = tf72fPhi (6/7) - tf72fPhi lam`

is exactly the gap whose quantitative lower bound
`(104/66825) * (6/7 - lam) ≤ tf72fPhi (6/7) - tf72fPhi lam` is
`Work.OffAxis.MomentStep103GapQuant`. -/

theorem tf72f_gap_quantitative :
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 6/7 →
      (104/66825 : ℝ) * (6/7 - lam)
        ≤ (tf72T ((6:ℝ)/7) (by norm_num)).F (-(6/7)) - (tf72T ((6:ℝ)/7) (by norm_num)).F (-lam)
          - 2 * ((tf72T ((6:ℝ)/7) (by norm_num)).F 0
              - (tf72T ((6:ℝ)/7) (by norm_num)).F (6/7 - lam)) := by
  intro lam h0 h1
  -- the four values of `F` appearing in the statement, as integrals over `[0, 7/3]`
  have eA : (tf72T ((6:ℝ)/7) (by norm_num)).F (-(6/7))
      = ∫ t in (0:ℝ)..(7/3), Real.exp ((6/7)*t) * tf72f ((6:ℝ)/7) t := by
    rw [tf72T67_F_eq_int]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-(6/7:ℝ)) * t) = (6/7:ℝ) * t from by ring]
  have eB : (tf72T ((6:ℝ)/7) (by norm_num)).F (-lam)
      = ∫ t in (0:ℝ)..(7/3), Real.exp (lam*t) * tf72f ((6:ℝ)/7) t := by
    rw [tf72T67_F_eq_int]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-lam) * t) = lam * t from by ring]
  have eC : (tf72T ((6:ℝ)/7) (by norm_num)).F 0
      = ∫ t in (0:ℝ)..(7/3), tf72f ((6:ℝ)/7) t := by
    rw [tf72T67_F_eq_int]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -(0 * t) = 0 from by ring, Real.exp_zero, one_mul]
  have eD : (tf72T ((6:ℝ)/7) (by norm_num)).F (6/7 - lam)
      = ∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam)*t)) * tf72f ((6:ℝ)/7) t :=
    tf72T67_F_eq_int (6/7 - lam)
  -- the gap `F(-lam) - 2 F(6/7 - lam)` is `tf72fPhi lam`
  have hphiL :
      (∫ t in (0:ℝ)..(7/3), Real.exp (lam*t) * tf72f ((6:ℝ)/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3),
            Real.exp (-((6/7 - lam)*t)) * tf72f ((6:ℝ)/7) t)
      = tf72fPhi lam :=
    tf72fL_eq_Phi lam
  -- and `F(-6/7) - 2 F 0` is `tf72fPhi (6/7)`
  have hphi67 :
      (∫ t in (0:ℝ)..(7/3), Real.exp (((6:ℝ)/7)*t) * tf72f ((6:ℝ)/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), tf72f ((6:ℝ)/7) t)
      = tf72fPhi ((6:ℝ)/7) := by
    have h := tf72fL_eq_Phi ((6:ℝ)/7)
    have hzero : (∫ t in (0:ℝ)..(7/3),
          Real.exp (-((((6:ℝ)/7) - 6/7) * t)) * tf72f ((6:ℝ)/7) t)
        = ∫ t in (0:ℝ)..(7/3), tf72f ((6:ℝ)/7) t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      simp
    rw [hzero] at h
    exact h
  -- identify the `F`-combination with the `tf72fPhi` gap
  have hgoal :
      (tf72T ((6:ℝ)/7) (by norm_num)).F (-(6/7))
          - (tf72T ((6:ℝ)/7) (by norm_num)).F (-lam)
          - 2 * ((tf72T ((6:ℝ)/7) (by norm_num)).F 0
              - (tf72T ((6:ℝ)/7) (by norm_num)).F (6/7 - lam))
        = tf72fPhi (6/7) - tf72fPhi lam := by
    rw [eA, eB, eC, eD]
    linarith [hphi67, hphiL]
  rw [hgoal]
  exact Work.OffAxis.MomentStep103GapQuant lam h0 h1

end Work.ZeroFreeTables.OffAxis
