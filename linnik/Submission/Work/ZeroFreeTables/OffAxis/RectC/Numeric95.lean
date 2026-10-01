/-
# ZeroFreeTables — the two interval-integral estimates of HB Lemma 9.5 at λ = 3/4

See the statement below.  Route: on `[0, 8/3]` the test function `tf72f (3/4)` is the
quintic `H4.hP`, whose moments `H4.hM j = ∫_0^{8/3} t^j · hP t` are known; bound `e^x`
above by `(P6 (x/3))^3` (Taylor at scale `1/3` plus the geometric-tail remainder from
`Real.exp_bound'`, valid since `x ≤ 3`) and below by its truncated Taylor polynomial
(`Real.sum_le_exp_of_nonneg`), then integrate term by term against `hM`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.H4.Tf72FDefs
import Submission.Work.ZeroFreeTables.H4.Tf72FNegLamLe
import Submission.Work.ZeroFreeTables.testFn72_defs

open MeasureTheory intervalIntegral Finset
open scoped Interval
noncomputable section

namespace Work.ZeroFreeTables.OffAxis.RectC

/-- The Taylor upper polynomial of `exp` of order `6` (remainder from `Real.exp_bound'`):
`Σ_{j<6} y^j/j! + 7 y^6/(6!·6)`, valid for `0 ≤ y ≤ 1`. -/
def P6 (y : ℝ) : ℝ :=
  1 + y + y^2/2 + y^3/6 + y^4/24 + y^5/120 + y^6*(7/4320)

/-- Coefficients of `(P6 y)^3`, so that `(P6 y)^3 = Σ_{n<19} bc n · y^n`. -/
def bc : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | 2 => 9/2
  | 3 => 9/2
  | 4 => 27/8
  | 5 => 81/40
  | 6 => 1459/1440
  | 7 => 313/720
  | 8 => 469/2880
  | 9 => 31/576
  | 10 => 1363/86400
  | 11 => 71/17280
  | 12 => 5911/6220800
  | 13 => 1207/6220800
  | 14 => 43/1244160
  | 15 => 983/186624000
  | 16 => 497/746496000
  | 17 => 49/746496000
  | 18 => 343/80621568000
  | _ => 0

lemma cont_hP : Continuous H4.hP := by unfold H4.hP; fun_prop

lemma cont_P6 : Continuous P6 := by unfold P6; fun_prop

lemma int_poly_hP {p : ℝ → ℝ} (hp : Continuous p) :
    IntervalIntegrable (fun t : ℝ => p t * H4.hP t) volume (0:ℝ) (8/3) :=
  (hp.mul cont_hP).intervalIntegrable 0 (8/3)

lemma exp_le_P6 {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y ≤ P6 y := by
  have h := Real.exp_bound' h0 h1 (n := 6) (by norm_num)
  simp only [P6, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h ⊢
  norm_num at h ⊢
  ring_nf at h ⊢
  exact h

lemma cube_P6 (y : ℝ) : (P6 y)^3 = ∑ n ∈ Finset.range 19, bc n * y^n := by
  simp only [P6, Finset.sum_range_succ, Finset.sum_range_zero, bc]
  ring

lemma exp_le_cube95 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 8/3) :
    Real.exp ((887:ℝ)/1000 * t) ≤ (P6 ((887:ℝ)/3000 * t))^3 := by
  have hy0 : 0 ≤ (887:ℝ)/3000 * t := by positivity
  have hy1 : (887:ℝ)/3000 * t ≤ 1 := by nlinarith [h1]
  have hey : Real.exp ((887:ℝ)/3000 * t) ≤ P6 ((887:ℝ)/3000 * t) := exp_le_P6 hy0 hy1
  have h3 : (887:ℝ)/1000 * t = 3 * ((887:ℝ)/3000 * t) := by ring
  have hexp : Real.exp ((887:ℝ)/1000 * t) = (Real.exp ((887:ℝ)/3000 * t))^3 := by
    rw [h3]; exact Real.exp_nat_mul _ 3
  rw [hexp]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hey 3

/-- Term-by-term integration of a truncated Taylor polynomial of `exp` against `hP`,
using the moments `H4.hM`. -/
lemma integral_taylor_mul_hP (c : ℝ) (N : ℕ) :
    ∫ t in (0:ℝ)..(8/3), (∑ j ∈ Finset.range N, (c*t)^j/(j.factorial:ℝ)) * H4.hP t
      = ∑ j ∈ Finset.range N, c^j * H4.hM j / (j.factorial:ℝ) := by
  have hint : ∀ j ∈ Finset.range N,
      IntervalIntegrable (fun t : ℝ => (c*t)^j/(j.factorial:ℝ) * H4.hP t)
        volume (0:ℝ) (8/3) :=
    fun j _ => int_poly_hP (by fun_prop)
  have key1 : (fun t : ℝ => (∑ j ∈ Finset.range N, (c*t)^j/(j.factorial:ℝ)) * H4.hP t)
      = fun t : ℝ => ∑ j ∈ Finset.range N, (c*t)^j/(j.factorial:ℝ) * H4.hP t := by
    funext t; rw [Finset.sum_mul]
  rw [key1, intervalIntegral.integral_finsetSum hint]
  apply Finset.sum_congr rfl
  intro j _
  have key2 : (fun t : ℝ => (c*t)^j/(j.factorial:ℝ) * H4.hP t)
      = fun t : ℝ => (c^j/(j.factorial:ℝ)) * (t^j * H4.hP t) := by
    funext t; rw [mul_pow]; ring
  rw [key2, intervalIntegral.integral_const_mul, H4.hP_moment]
  ring

/-- Integration of `(P6 (887/3000 · t))^3` against `hP`, evaluated via the moments. -/
lemma integral_cube_hP :
    ∫ t in (0:ℝ)..(8/3), (P6 ((887:ℝ)/3000 * t))^3 * H4.hP t
      = ∑ n ∈ Finset.range 19, bc n * ((887:ℝ)/3000)^n * H4.hM n := by
  have hint : ∀ n ∈ Finset.range 19,
      IntervalIntegrable (fun t : ℝ => bc n * ((887:ℝ)/3000 * t)^n * H4.hP t)
        volume (0:ℝ) (8/3) :=
    fun n _ => int_poly_hP (by fun_prop)
  have key1 : (fun t : ℝ => (P6 ((887:ℝ)/3000 * t))^3 * H4.hP t)
      = fun t : ℝ => ∑ n ∈ Finset.range 19,
          bc n * ((887:ℝ)/3000 * t)^n * H4.hP t := by
    funext t; rw [cube_P6, Finset.sum_mul]
  rw [key1, intervalIntegral.integral_finsetSum hint]
  apply Finset.sum_congr rfl
  intro n _
  have key2 : (fun t : ℝ => bc n * ((887:ℝ)/3000 * t)^n * H4.hP t)
      = fun t : ℝ => (bc n * ((887:ℝ)/3000)^n) * (t^n * H4.hP t) := by
    funext t; rw [mul_pow]; ring
  rw [key2, intervalIntegral.integral_const_mul, H4.hP_moment]

/-- **The two interval-integral estimates for HB Lemma 9.5 at `λ = 3/4`, `λ* = 887/1000`.**
For HB Lemma 7.2's test function `f = tf72f (3/4)` (supported on `[0, 8/3]`, `F(0) = 8/9`,
`f 0 = 4/5`):
`F(-λ*) = ∫₀^{8/3} e^{(887/1000)t} f ≤ 1820/1000` and, for every `a ∈ [539/1000, 887/1000]`,
`∫₀^{8/3} e^{a t} f ≥ 1330/1000` — the second in the form used by the Lemma-9.5 assembly
(`a = λ* - λ₁` with `λ₁ ≤ 348/1000`, so `a ≥ 539/1000`, and the integral is increasing in `a`).

Route: on `[0,8/3]` the function `tf72f (3/4)` is the quintic `Work.ZeroFreeTables.H4.hP`
(`H4/Tf72FDefs.lean`, lemma `tf72f34_eq`), whose moments `hM j = ∫₀^{8/3} t^j · hP t` are computed
there; bound `e^{x}` above by a Taylor polynomial plus remainder (as in
`Submission/Work/ZeroFreeTables/H4/Tf72FNegLamLe.lean`, here for `x ≤ 887·8/(1000·3) ≤ 3`) and below
by its Taylor polynomial (positive remainder), then integrate term by term against `hM`.
Direct numerical integration gives `1.81231` (upper) and `1.33506` (lower), so both hold. -/
theorem Numeric95 :
    (∫ t in (0:ℝ)..(8/3), Real.exp ((887:ℝ)/1000 * t) * Work.ZeroFreeTables.tf72f (3/4) t)
        ≤ (1820:ℝ)/1000 ∧
      ∀ a : ℝ, (539:ℝ)/1000 ≤ a → a ≤ (887:ℝ)/1000 →
        (1330:ℝ)/1000 ≤ ∫ t in (0:ℝ)..(8/3), Real.exp (a * t) * Work.ZeroFreeTables.tf72f (3/4) t := by
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
    calc ∫ t in (0:ℝ)..(8/3), Real.exp ((887:ℝ)/1000 * t) * H4.hP t
        ≤ ∫ t in (0:ℝ)..(8/3), (P6 ((887:ℝ)/3000 * t))^3 * H4.hP t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact int_poly_hP (by fun_prop)
          · exact int_poly_hP ((cont_P6.comp (continuous_const.mul continuous_id)).pow 3)
          · intro t ht
            exact mul_le_mul_of_nonneg_right (exp_le_cube95 ht.1 ht.2) (H4.hP_nonneg t ht.1 ht.2)
      _ = ∑ n ∈ Finset.range 19, bc n * ((887:ℝ)/3000)^n * H4.hM n := integral_cube_hP
      _ ≤ (1820:ℝ)/1000 := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, bc]
          norm_num [H4.hM]
  · intro a ha1 ha2
    rw [hA]
    calc (1330:ℝ)/1000
        ≤ ∑ j ∈ Finset.range 6, ((539:ℝ)/1000)^j * H4.hM j / (j.factorial:ℝ) := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero]
          norm_num [H4.hM]
      _ = ∫ t in (0:ℝ)..(8/3),
            (∑ j ∈ Finset.range 6, (((539:ℝ)/1000)*t)^j/(j.factorial:ℝ)) * H4.hP t :=
          (integral_taylor_mul_hP ((539:ℝ)/1000) 6).symm
      _ ≤ ∫ t in (0:ℝ)..(8/3), Real.exp (a * t) * H4.hP t := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact int_poly_hP (by fun_prop)
          · exact int_poly_hP (by fun_prop)
          · intro t ht
            have ht0 : 0 ≤ t := ht.1
            have hsum : (∑ j ∈ Finset.range 6, (((539:ℝ)/1000)*t)^j/(j.factorial:ℝ))
                ≤ Real.exp (((539:ℝ)/1000)*t) :=
              Real.sum_le_exp_of_nonneg (by positivity) 6
            have hle : Real.exp (((539:ℝ)/1000)*t) ≤ Real.exp (a*t) :=
              Real.exp_le_exp.mpr (by nlinarith [ha1, ht0])
            exact mul_le_mul_of_nonneg_right (hsum.trans hle) (H4.hP_nonneg t ht.1 ht.2)

end Work.ZeroFreeTables.OffAxis.RectC
