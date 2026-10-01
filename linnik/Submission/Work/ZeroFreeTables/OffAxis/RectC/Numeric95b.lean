/-
# ZeroFreeTables/OffAxis/RectC/Numeric95b

The companion of `Numeric95` for the level `λ* = λ₁ + 472/1000`:
`∫₀^{8/3} e^{(82/100)t} tf72f (3/4) ≤ 1710/1000` (the worst case of `F(-λ*)` when
`λ* = λ₁ + 472/1000`, `λ₁ ≤ 348/1000`) and `∫₀^{8/3} e^{(472/1000)t} tf72f (3/4) ≥ 1260/1000`
(the kept-zero term `F(λ₁ - λ*)` at `λ* - λ₁ = 472/1000`).  Direct numerical values:
`1.703967` (0.35% slack) and `1.263860` (0.31% slack).

The proof reuses the verified `P6`/`bc`/moment machinery of `Numeric95`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Numeric95

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

namespace Work.ZeroFreeTables.OffAxis.RectC

/-- `e^{(82/100)t} ≤ (P6 ((82/300)·t))³` on `[0, 8/3]` (the analogue of `exp_le_cube95`). -/
lemma exp_le_cube82 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 8/3) :
    Real.exp ((82:ℝ)/100 * t) ≤ (P6 ((82:ℝ)/300 * t))^3 := by
  have hy0 : 0 ≤ (82:ℝ)/300 * t := by positivity
  have hy1 : (82:ℝ)/300 * t ≤ 1 := by nlinarith [h1]
  have hey : Real.exp ((82:ℝ)/300 * t) ≤ P6 ((82:ℝ)/300 * t) := exp_le_P6 hy0 hy1
  have h3 : (82:ℝ)/100 * t = 3 * ((82:ℝ)/300 * t) := by ring
  have hexp : Real.exp ((82:ℝ)/100 * t) = (Real.exp ((82:ℝ)/300 * t))^3 := by
    rw [h3]; exact Real.exp_nat_mul _ 3
  rw [hexp]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hey 3

/-- Integration of `(P6 ((82/300)·t))³` against `hP`, via the moments. -/
lemma integral_cube_hP82 :
    ∫ t in (0:ℝ)..(8/3), (P6 ((82:ℝ)/300 * t))^3 * H4.hP t
      = ∑ n ∈ Finset.range 19, bc n * ((82:ℝ)/300)^n * H4.hM n := by
  have hint : ∀ n ∈ Finset.range 19,
      IntervalIntegrable (fun t : ℝ => bc n * ((82:ℝ)/300 * t)^n * H4.hP t)
        volume (0:ℝ) (8/3) :=
    fun n _ => int_poly_hP (by fun_prop)
  have key1 : (fun t : ℝ => (P6 ((82:ℝ)/300 * t))^3 * H4.hP t)
      = fun t : ℝ => ∑ n ∈ Finset.range 19,
          bc n * ((82:ℝ)/300 * t)^n * H4.hP t := by
    funext t; rw [cube_P6, Finset.sum_mul]
  rw [key1, intervalIntegral.integral_finsetSum hint]
  apply Finset.sum_congr rfl
  intro n _
  have key2 : (fun t : ℝ => bc n * ((82:ℝ)/300 * t)^n * H4.hP t)
      = fun t : ℝ => (bc n * ((82:ℝ)/300)^n) * (t^n * H4.hP t) := by
    funext t; rw [mul_pow]; ring
  rw [key2, intervalIntegral.integral_const_mul, H4.hP_moment]

theorem Numeric95b :
    (∫ t in (0:ℝ)..(8/3), Real.exp ((82:ℝ)/100 * t) * Work.ZeroFreeTables.tf72f (3/4) t)
        ≤ (1710:ℝ)/1000 ∧
      (1260:ℝ)/1000 ≤ ∫ t in (0:ℝ)..(8/3),
        Real.exp ((472:ℝ)/1000 * t) * Work.ZeroFreeTables.tf72f (3/4) t := by
  have hA : ∀ c : ℝ, (∫ t in (0:ℝ)..(8/3), Real.exp (c * t) * Work.ZeroFreeTables.tf72f (3/4) t)
      = ∫ t in (0:ℝ)..(8/3), Real.exp (c * t) * H4.hP t := by
    intro c
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 8/3)] at ht
    show Real.exp (c * t) * Work.ZeroFreeTables.tf72f (3/4) t = Real.exp (c * t) * H4.hP t
    rw [H4.tf72f34_eq t ht]
  constructor
  · rw [hA]
    calc ∫ t in (0:ℝ)..(8/3), Real.exp ((82:ℝ)/100 * t) * H4.hP t
        ≤ ∫ t in (0:ℝ)..(8/3), (P6 ((82:ℝ)/300 * t))^3 * H4.hP t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact int_poly_hP (by fun_prop)
          · exact int_poly_hP ((cont_P6.comp (continuous_const.mul continuous_id)).pow 3)
          · intro t ht
            exact mul_le_mul_of_nonneg_right (exp_le_cube82 ht.1 ht.2) (H4.hP_nonneg t ht.1 ht.2)
      _ = ∑ n ∈ Finset.range 19, bc n * ((82:ℝ)/300)^n * H4.hM n := integral_cube_hP82
      _ ≤ (1710:ℝ)/1000 := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, bc]
          norm_num [H4.hM]
  · rw [hA]
    calc (1260:ℝ)/1000
        ≤ ∑ j ∈ Finset.range 6, ((472:ℝ)/1000)^j * H4.hM j / (j.factorial:ℝ) := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero]
          norm_num [H4.hM]
      _ = ∫ t in (0:ℝ)..(8/3),
            (∑ j ∈ Finset.range 6, (((472:ℝ)/1000)*t)^j/(j.factorial:ℝ)) * H4.hP t :=
          (integral_taylor_mul_hP ((472:ℝ)/1000) 6).symm
      _ ≤ ∫ t in (0:ℝ)..(8/3), Real.exp (((472:ℝ)/1000) * t) * H4.hP t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact int_poly_hP (by fun_prop)
          · exact int_poly_hP (by fun_prop)
          · intro t ht
            have ht0 : 0 ≤ t := ht.1
            have hsum : (∑ j ∈ Finset.range 6, (((472:ℝ)/1000)*t)^j/(j.factorial:ℝ))
                ≤ Real.exp (((472:ℝ)/1000)*t) :=
              Real.sum_le_exp_of_nonneg (by positivity) 6
            exact mul_le_mul_of_nonneg_right hsum (H4.hP_nonneg t ht.1 ht.2)

end Work.ZeroFreeTables.OffAxis.RectC
