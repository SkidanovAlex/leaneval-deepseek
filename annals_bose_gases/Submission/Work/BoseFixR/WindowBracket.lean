import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.paramsAt_facts
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.WindowBracket`

The D1 log/quartic/interior bracket of `Work.BlockBound4.d4Bracket` at the box
data of `Work.BoseBoxFix.Adm`, in the dilute window `N ≤ 9 μ ℓ³`:

    d4Bracket Ct (N−1) ℓ (2 d s ℓ)⁻¹ v ≤ 291 μ² a ℓ³ .

Everything here is scalar: the bracket is

    d1C Ct · ( T₁ + T₂ + T₃ ),
    T₁ = a² c₀ log((c₀a)⁻¹) · N²/ℓ³,
    T₂ = a⁴ (c₀³)⁻¹ (N/ℓ³)⁴ ℓ³,
    T₃ = a c₀³ (N/ℓ³) ℓ³,

with `ℓ = sideAt μ a = a t^{-163/323}`, `c₀ = (2 d s ℓ)⁻¹ = t^{156/323}/(2a)`
and `t = μa³` (`sideAt_eq_rpow` plus `paramsAt = fsParams (μa³)`).  Since
`N ≤ 9μℓ³` and `ℓ = a t^{-163/323}`, `μ = t/a³`, all three terms are monomials in
`t` and `a`:

    T₁ ≤ 81·√2 · t^{78/323} · μ²aℓ³,   T₂ ≤ 52488 t^{178/323} μ²aℓ³,
    T₃ ≤ (9/8) t^{145/323} μ²aℓ³,

each of the last two being an *equality* at `N = 9μℓ³`.  The log term is
controlled by `log y ≤ 2√y` (`Real.log_le_rpow_div`).  With `t ≤ 1` the sum is at
most `53000 t^{78/323} μ²aℓ³`, and choosing
`ε₀ = min 1 (291/(53000·d1C Ct))^{323/78}` makes `d1C·53000·t^{78/323} ≤ 291`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixR

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 0. Elementary scalar tools -/

/-- `log y ≤ 2√y` (from `Real.log_le_rpow_div` at `ε = 1/2`). -/
lemma log_le_two_mul_rpow_half {y : ℝ} (hy : 0 ≤ y) :
    Real.log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
  have h := Real.log_le_rpow_div hy (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 : y ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * y ^ (1 / 2 : ℝ) := by ring
  rwa [h2] at h

/-- `√2 ≤ 1.42`. -/
lemma sqrt_two_le_142 : Real.sqrt 2 ≤ 142 / 100 := by
  have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (142 / 100) ^ 2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 142 / 100)] at h

/-- D1's constant is positive (it dominates `6(2π)³`). -/
lemma d1C_pos (Ct : ℝ) : 0 < Work.SmallBoxA0.d1C Ct := by
  rw [Work.SmallBoxA0.d1C, Submission.BoseGases.d1TargetC]
  exact lt_of_lt_of_le (by positivity) (le_max_left _ _)

/-! ## 1. The three term bounds of the D1 bracket -/

/-- **The log term** `T₁ = a²c₀log((c₀a)⁻¹)·N²/ℓ³` of the D1 bracket, bounded by
`81√2 t^{78/323} μ²aℓ³ ≤ 120 t^{78/323} μ²aℓ³` in the dilute window `N ≤ 9μℓ³`,
`t = μa³ ≤ 1`. -/
lemma t1_bound {a μ s c₀ N : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hs : 0 < s) (hN : 0 ≤ N)
    (hc₀ : c₀ = (μ * a ^ 3) ^ (156 / 323 : ℝ) / (2 * a))
    (ht1 : μ * a ^ 3 ≤ 1)
    (hNmax : N ≤ 9 * μ * s ^ 3) :
    a ^ 2 * c₀ * Real.log ((c₀ * a)⁻¹) * (N * N / s ^ 3)
      ≤ 120 * (μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hc0a : c₀ * a = (μ * a ^ 3) ^ (156 / 323 : ℝ) / 2 := by
    rw [hc₀, div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt ha)]
  have hc0apos : 0 < c₀ * a := by rw [hc0a]; positivity
  have hc0pos : 0 < c₀ := by nlinarith [hc0apos, ha]
  have hle1 : c₀ * a ≤ 1 := by
    rw [hc0a]
    have h := Real.rpow_le_one ht.le ht1 (by norm_num : (0 : ℝ) ≤ 156 / 323)
    linarith
  have hlogarg : (c₀ * a)⁻¹ = 2 * (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) := by
    rw [hc0a, inv_div, Real.rpow_neg ht.le, div_eq_mul_inv]
  have hlog1 : 1 ≤ (c₀ * a)⁻¹ := by
    rw [hlogarg]
    have h : (1 : ℝ) ≤ (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
    linarith
  have hlog0 : 0 ≤ Real.log ((c₀ * a)⁻¹) := Real.log_nonneg hlog1
  have hlogbound : Real.log ((c₀ * a)⁻¹) ≤ 2 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (μ * a ^ 3) ^ (-(78 / 323 : ℝ)) := by
    rw [hlogarg]
    have h1 := log_le_two_mul_rpow_half
      (show (0 : ℝ) ≤ 2 * (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) by positivity)
    have h2 : (2 * (μ * a ^ 3) ^ (-(156 / 323 : ℝ))) ^ (1 / 2 : ℝ)
        = (2 : ℝ) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul ht.le]
      norm_num
    rw [h2] at h1
    calc Real.log (2 * (μ * a ^ 3) ^ (-(156 / 323 : ℝ)))
        ≤ 2 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ))) := h1
      _ = 2 * (2 : ℝ) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ)) := by ring
  have hNsq : N * N / s ^ 3 ≤ 81 * μ ^ 2 * s ^ 3 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 3)]
    have hsq : N * N ≤ (9 * μ * s ^ 3) * (9 * μ * s ^ 3) :=
      mul_le_mul hNmax hNmax hN (by positivity)
    nlinarith [hsq]
  have hcoef1 : 0 ≤ a ^ 2 * c₀ * Real.log ((c₀ * a)⁻¹) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt hc0pos)) hlog0
  have hA : a ^ 2 * c₀ * Real.log ((c₀ * a)⁻¹) * (N * N / s ^ 3)
      ≤ a ^ 2 * c₀ * Real.log ((c₀ * a)⁻¹) * (81 * μ ^ 2 * s ^ 3) :=
    mul_le_mul_of_nonneg_left hNsq hcoef1
  have hB : a ^ 2 * c₀ * Real.log ((c₀ * a)⁻¹) * (81 * μ ^ 2 * s ^ 3)
      ≤ a ^ 2 * c₀ * (2 * (2 : ℝ) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ)))
          * (81 * μ ^ 2 * s ^ 3) := by
    have h1 : 0 ≤ a ^ 2 * c₀ := mul_nonneg (by positivity) (le_of_lt hc0pos)
    have h2 : 0 ≤ 81 * μ ^ 2 * s ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogbound h1) h2
  have hEq : a ^ 2 * c₀ * (2 * (2 : ℝ) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ)))
        * (81 * μ ^ 2 * s ^ 3)
      = 81 * (2 : ℝ) ^ (1 / 2 : ℝ) *
          ((μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3)) := by
    have hkey : (μ * a ^ 3) ^ (156 / 323 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ))
        = (μ * a ^ 3) ^ (78 / 323 : ℝ) := by
      rw [← Real.rpow_add ht]; norm_num
    have h1 : a ^ 2 * c₀ = a * (c₀ * a) := by ring
    rw [h1, hc0a]
    calc a * ((μ * a ^ 3) ^ (156 / 323 : ℝ) / 2)
            * (2 * (2 : ℝ) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ)))
            * (81 * μ ^ 2 * s ^ 3)
        = 81 * (2 : ℝ) ^ (1 / 2 : ℝ) *
            (((μ * a ^ 3) ^ (156 / 323 : ℝ) * (μ * a ^ 3) ^ (-(78 / 323 : ℝ)))
              * (μ ^ 2 * a * s ^ 3)) := by ring
      _ = 81 * (2 : ℝ) ^ (1 / 2 : ℝ) *
            ((μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3)) := by rw [hkey]
  have hC : 81 * (2 : ℝ) ^ (1 / 2 : ℝ) *
        ((μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3))
      ≤ 120 * (μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by
    have hP : 0 ≤ (μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by positivity
    have hs2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 142 / 100 := by
      rw [← Real.sqrt_eq_rpow]; exact sqrt_two_le_142
    have hc : 81 * (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 120 := by linarith
    calc 81 * (2 : ℝ) ^ (1 / 2 : ℝ) *
            ((μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3))
        ≤ 120 * ((μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3)) :=
          mul_le_mul_of_nonneg_right hc hP
      _ = 120 * (μ * a ^ 3) ^ (78 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by ring
  exact le_trans (le_trans (le_trans hA hB) (le_of_eq hEq)) hC

/-- **The quartic term** `T₂ = a⁴(c₀³)⁻¹(N/ℓ³)⁴ℓ³` of the D1 bracket:
`≤ 52488 t^{178/323} μ²aℓ³` (equality at `N = 9μℓ³`). -/
lemma t2_bound {a μ s c₀ N : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hs : 0 < s) (hN : 0 ≤ N)
    (hc₀ : c₀ = (μ * a ^ 3) ^ (156 / 323 : ℝ) / (2 * a))
    (hNmax : N ≤ 9 * μ * s ^ 3) :
    a ^ 4 * (c₀ ^ 3)⁻¹ * ((N / s ^ 3) ^ 3) * (N / s ^ 3) * s ^ 3
      ≤ 52488 * (μ * a ^ 3) ^ (178 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hc0pos : 0 < c₀ := by rw [hc₀]; positivity
  have hc0i3 : (c₀ ^ 3)⁻¹ = 8 * a ^ 3 * (μ * a ^ 3) ^ (-(468 / 323 : ℝ)) := by
    have hc0inv : c₀⁻¹ = 2 * a * (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) := by
      rw [hc₀, inv_div, Real.rpow_neg ht.le, div_eq_mul_inv]
    rw [← inv_pow, hc0inv, mul_pow, mul_pow]
    have hcube : ((μ * a ^ 3) ^ (-(156 / 323 : ℝ))) ^ 3
        = (μ * a ^ 3) ^ (-(468 / 323 : ℝ)) := by
      rw [← Real.rpow_natCast ((μ * a ^ 3) ^ (-(156 / 323 : ℝ))) 3, ← Real.rpow_mul ht.le]
      norm_num
    rw [hcube]
    norm_num
  have hNle : N / s ^ 3 ≤ 9 * μ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 3)]
    linarith [hNmax]
  have hpow : ((N / s ^ 3) ^ 3) * (N / s ^ 3) ≤ (9 * μ) ^ 4 := by
    rw [← pow_succ]
    exact pow_le_pow_left₀ (by positivity) hNle 4
  have hcoef : 0 ≤ a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3 := by
    have h1 : 0 < a ^ 4 := by positivity
    have h2 : 0 < (c₀ ^ 3)⁻¹ := by positivity
    have h3 : 0 < s ^ 3 := by positivity
    exact le_of_lt (mul_pos (mul_pos h1 h2) h3)
  have hmain : a ^ 4 * (c₀ ^ 3)⁻¹ * ((N / s ^ 3) ^ 3) * (N / s ^ 3) * s ^ 3
      ≤ a ^ 4 * (c₀ ^ 3)⁻¹ * (9 * μ) ^ 4 * s ^ 3 := by
    rw [show a ^ 4 * (c₀ ^ 3)⁻¹ * ((N / s ^ 3) ^ 3) * (N / s ^ 3) * s ^ 3
          = (a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3) * (((N / s ^ 3) ^ 3) * (N / s ^ 3)) by ring]
    calc (a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3) * (((N / s ^ 3) ^ 3) * (N / s ^ 3))
        ≤ (a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3) * (9 * μ) ^ 4 := mul_le_mul_of_nonneg_left hpow hcoef
      _ = a ^ 4 * (c₀ ^ 3)⁻¹ * (9 * μ) ^ 4 * s ^ 3 := by ring
  refine le_trans hmain ?_
  rw [hc0i3]
  have hkey : 8 * 9 ^ 4 * (a ^ 6 * μ ^ 2 * (μ * a ^ 3) ^ (-(468 / 323 : ℝ)))
      = 52488 * (μ * a ^ 3) ^ (178 / 323 : ℝ) := by
    have h2 : a ^ 6 * μ ^ 2 = (μ * a ^ 3) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; ring
    have hk : (μ * a ^ 3) ^ (2 : ℝ) * (μ * a ^ 3) ^ (-(468 / 323 : ℝ))
        = (μ * a ^ 3) ^ (178 / 323 : ℝ) := by
      rw [← Real.rpow_add ht]; norm_num
    rw [h2, hk]
    norm_num
  have hEq : a ^ 4 * (8 * a ^ 3 * (μ * a ^ 3) ^ (-(468 / 323 : ℝ))) * (9 * μ) ^ 4 * s ^ 3
      = 52488 * (μ * a ^ 3) ^ (178 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by
    rw [← hkey]
    ring
  exact le_of_eq hEq

/-- **The interior term** `T₃ = a c₀³ (N/ℓ³) ℓ³` of the D1 bracket:
`≤ (9/8) t^{145/323} μ²aℓ³` (equality at `N = 9μℓ³`). -/
lemma t3_bound {a μ s c₀ N : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hs : 0 < s) (hN : 0 ≤ N)
    (hc₀ : c₀ = (μ * a ^ 3) ^ (156 / 323 : ℝ) / (2 * a))
    (hNmax : N ≤ 9 * μ * s ^ 3) :
    a * c₀ ^ 3 * (N / s ^ 3) * s ^ 3
      ≤ (9 / 8) * (μ * a ^ 3) ^ (145 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hc0pos : 0 < c₀ := by rw [hc₀]; positivity
  have hc03 : c₀ ^ 3 = (μ * a ^ 3) ^ (468 / 323 : ℝ) / (8 * a ^ 3) := by
    rw [hc₀, div_pow, mul_pow]
    have hcube : ((μ * a ^ 3) ^ (156 / 323 : ℝ)) ^ 3
        = (μ * a ^ 3) ^ (468 / 323 : ℝ) := by
      rw [← Real.rpow_natCast ((μ * a ^ 3) ^ (156 / 323 : ℝ)) 3, ← Real.rpow_mul ht.le]
      norm_num
    rw [hcube]
    norm_num
  have hNle : N / s ^ 3 ≤ 9 * μ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 3)]
    linarith [hNmax]
  have hcoef : 0 ≤ a * c₀ ^ 3 * s ^ 3 := by
    have h1 : 0 < a * c₀ ^ 3 := mul_pos ha (by positivity)
    exact le_of_lt (mul_pos h1 (by positivity))
  have hmain : a * c₀ ^ 3 * (N / s ^ 3) * s ^ 3 ≤ a * c₀ ^ 3 * (9 * μ) * s ^ 3 := by
    rw [show a * c₀ ^ 3 * (N / s ^ 3) * s ^ 3 = (a * c₀ ^ 3 * s ^ 3) * (N / s ^ 3) by ring]
    calc (a * c₀ ^ 3 * s ^ 3) * (N / s ^ 3) ≤ (a * c₀ ^ 3 * s ^ 3) * (9 * μ) :=
          mul_le_mul_of_nonneg_left hNle hcoef
      _ = a * c₀ ^ 3 * (9 * μ) * s ^ 3 := by ring
  refine le_trans hmain ?_
  rw [hc03]
  have hkey : (μ * a ^ 3) ^ (145 / 323 : ℝ) * (μ * a ^ 3) ^ (1 : ℝ)
      = (μ * a ^ 3) ^ (468 / 323 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  have hEq : a * ((μ * a ^ 3) ^ (468 / 323 : ℝ) / (8 * a ^ 3)) * (9 * μ) * s ^ 3
      = (9 / 8) * (μ * a ^ 3) ^ (145 / 323 : ℝ) * (μ ^ 2 * a * s ^ 3) := by
    rw [← hkey, Real.rpow_one]
    have hA : a ≠ 0 := ne_of_gt ha
    field_simp
  exact le_of_eq hEq

/-! ## 2. Unfolding the bracket, and the constants -/

/-- The D1 bracket at particle count `N−1` is `d1C` times the sum of the three
terms `T₁, T₂, T₃` above. -/
lemma d4Bracket_eq_terms {v : EuclideanSpace ℝ (Fin 3) → ℝ} {Ct μ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) :
    Work.BlockBound4.d4Bracket Ct (N - 1)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) v
      = Work.SmallBoxA0.d1C Ct *
        (((_root_.BoseGases.a v) ^ 2
            * ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹)
            * Real.log ((((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) * (_root_.BoseGases.a v))⁻¹)
            * ((N : ℝ) * (N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
          + (_root_.BoseGases.a v) ^ 4
              * ((((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 3)⁻¹)
              * ((((N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) ^ 3))
              * ((N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
          + (_root_.BoseGases.a v)
              * (((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 3)
              * ((N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) := by
  have hcast : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    rw [Nat.cast_sub hN]
    norm_num
  rw [Work.BlockBound4.d4Bracket, Work.SmallBoxA0.kinPBracket, hcast]

/-- The box data of `Adm` fix `c₀`: `(2 d s ℓ)⁻¹ = t^{156/323}/(2a)` with
`t = μa³`. -/
lemma d4c0_eq {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) :
    (2 * (Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
        * Work.BoseBox.sideAt μ a)⁻¹
      = (μ * a ^ 3) ^ (156 / 323 : ℝ) / (2 * a) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hside : Work.BoseBox.sideAt μ a = a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) :=
    Work.BoseBox.sideAt_eq_rpow ha hμ
  have hd : (Work.BoseBox.paramsAt μ a).d = (μ * a ^ 3) ^ (6 / 323 : ℝ) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have hs : (Work.BoseBox.paramsAt μ a).s = (μ * a ^ 3) ^ (1 / 323 : ℝ) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have h6 : (μ * a ^ 3) ^ (6 / 323 : ℝ) * (μ * a ^ 3) ^ (1 / 323 : ℝ)
      = (μ * a ^ 3) ^ (7 / 323 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  have h7 : (μ * a ^ 3) ^ (7 / 323 : ℝ) * (μ * a ^ 3) ^ (-(163 / 323 : ℝ))
      = (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) := by
    rw [← Real.rpow_add ht]; norm_num
  have hprod : 2 * (Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
        * Work.BoseBox.sideAt μ a = 2 * a * (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) := by
    rw [hd, hs, hside]
    calc 2 * (μ * a ^ 3) ^ (6 / 323 : ℝ) * (μ * a ^ 3) ^ (1 / 323 : ℝ)
            * (a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)))
        = 2 * a * ((μ * a ^ 3) ^ (6 / 323 : ℝ) * (μ * a ^ 3) ^ (1 / 323 : ℝ)
            * (μ * a ^ 3) ^ (-(163 / 323 : ℝ))) := by ring
      _ = 2 * a * ((μ * a ^ 3) ^ (7 / 323 : ℝ) * (μ * a ^ 3) ^ (-(163 / 323 : ℝ))) := by
            rw [h6]
      _ = 2 * a * (μ * a ^ 3) ^ (-(156 / 323 : ℝ)) := by rw [h7]
  rw [hprod, mul_inv, Real.rpow_neg ht.le, inv_inv, div_eq_mul_inv]
  ring

/-- **The constant absorption**: for `t ≤ ε₀ ≤ (291/(53000·D))^{323/78}`,
`D·53000·t^{78/323} ≤ 291`. -/
lemma d1C_absorb {D t ε₀ : ℝ} (hD : 0 < D) (ht : 0 < t) (hε0 : 0 ≤ ε₀)
    (hε : ε₀ ≤ (291 / (53000 * D)) ^ (323 / 78 : ℝ))
    (htε : t ≤ ε₀) :
    D * 53000 * t ^ (78 / 323 : ℝ) ≤ 291 := by
  have hbase : 0 ≤ 291 / (53000 * D) := by positivity
  have h1 : t ^ (78 / 323 : ℝ) ≤ ε₀ ^ (78 / 323 : ℝ) :=
    Real.rpow_le_rpow ht.le htε (by norm_num)
  have h2 : ε₀ ^ (78 / 323 : ℝ)
      ≤ ((291 / (53000 * D)) ^ (323 / 78 : ℝ)) ^ (78 / 323 : ℝ) :=
    Real.rpow_le_rpow hε0 hε (by norm_num)
  have h3 : ((291 / (53000 * D)) ^ (323 / 78 : ℝ)) ^ (78 / 323 : ℝ)
      = 291 / (53000 * D) := by
    rw [← Real.rpow_mul hbase]
    norm_num
  have h4 : t ^ (78 / 323 : ℝ) ≤ 291 / (53000 * D) := by
    rw [h3] at h2
    exact le_trans h1 h2
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ D * 53000)
  calc D * 53000 * t ^ (78 / 323 : ℝ) = (D * 53000) * t ^ (78 / 323 : ℝ) := by ring
    _ ≤ (D * 53000) * (291 / (53000 * D)) := h5
    _ = 291 := by field_simp

/-! ## 3. The window bracket -/

theorem WindowBracket {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (Ct : ℝ) (hCt : 0 ≤ Ct) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ 9 * μ →
      Work.BlockBound4.d4Bracket Ct (N - 1)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) v
        ≤ 291 * μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
  have hd1C : 0 < Work.SmallBoxA0.d1C Ct := d1C_pos Ct
  refine ⟨min 1 ((291 / (53000 * Work.SmallBoxA0.d1C Ct)) ^ (323 / 78 : ℝ)), ?_, ?_⟩
  · exact lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  · intro μ hAdm N hN2 hNle
    obtain ⟨hμ, hμα, -⟩ := hAdm
    have hε1 : min 1 ((291 / (53000 * Work.SmallBoxA0.d1C Ct)) ^ (323 / 78 : ℝ)) ≤ 1 :=
      min_le_left _ _
    have hεX : min 1 ((291 / (53000 * Work.SmallBoxA0.d1C Ct)) ^ (323 / 78 : ℝ))
        ≤ (291 / (53000 * Work.SmallBoxA0.d1C Ct)) ^ (323 / 78 : ℝ) := min_le_right _ _
    have ht_pos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    have ht_le1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hμα hε1
    have hε0nn : 0 ≤ min 1 ((291 / (53000 * Work.SmallBoxA0.d1C Ct)) ^ (323 / 78 : ℝ)) :=
      le_of_lt (lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _))
    have hA : Work.SmallBoxA0.d1C Ct * 53000
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ) ≤ 291 :=
      d1C_absorb hd1C ht_pos hε0nn hεX hμα
    have hs_pos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
      rw [Work.BoseBox.sideAt_eq_rpow hav hμ]; positivity
    have hNmax : (N : ℝ) ≤ 9 * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
      rw [div_le_iff₀ (pow_pos hs_pos 3)] at hNle
      linarith [hNle]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hc₀ : (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ (156 / 323 : ℝ) / (2 * (_root_.BoseGases.a v)) :=
      d4c0_eq hav hμ
    rw [d4Bracket_eq_terms (v := v) (Ct := Ct) (μ := μ) (N := N) (by omega)]
    set T1 : ℝ := (_root_.BoseGases.a v) ^ 2
            * ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹)
            * Real.log ((((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) * (_root_.BoseGases.a v))⁻¹)
            * ((N : ℝ) * (N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
        with hT1
    set T2 : ℝ := (_root_.BoseGases.a v) ^ 4
              * ((((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 3)⁻¹)
              * ((((N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) ^ 3))
              * ((N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        with hT2
    set T3 : ℝ := (_root_.BoseGases.a v)
              * (((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 3)
              * ((N : ℝ) / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        with hT3
    have h1 : T1 ≤ 120 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
        * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
      rw [hT1]
      exact t1_bound hav hμ hs_pos hN0 hc₀ ht_le1 hNmax
    have h2 : T2 ≤ 52488 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (178 / 323 : ℝ)
        * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
      rw [hT2]
      exact t2_bound hav hμ hs_pos hN0 hc₀ hNmax
    have h3 : T3 ≤ (9 / 8) * (μ * (_root_.BoseGases.a v) ^ 3) ^ (145 / 323 : ℝ)
        * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
      rw [hT3]
      exact t3_bound hav hμ hs_pos hN0 hc₀ hNmax
    have hPnn : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by positivity
    let M : ℝ := (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
        * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
    have hMnn : 0 ≤ M := by dsimp only [M]; positivity
    have h1' : T1 ≤ 120 * M := by
      calc T1 ≤ 120 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := h1
        _ = 120 * M := by dsimp only [M]; ring
    have h2' : T2 ≤ 52488 * M := by
      have h178 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (178 / 323 : ℝ)
          ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ht_pos ht_le1 (by norm_num)
      have hmid : (μ * (_root_.BoseGases.a v) ^ 3) ^ (178 / 323 : ℝ)
            * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
          ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
            * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
        mul_le_mul_of_nonneg_right h178 hPnn
      calc T2 ≤ 52488 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (178 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := h2
        _ = 52488 * ((μ * (_root_.BoseGases.a v) ^ 3) ^ (178 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) := by ring
        _ ≤ 52488 * ((μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) :=
            mul_le_mul_of_nonneg_left hmid (by norm_num)
        _ = 52488 * M := by dsimp only [M]
    have h3' : T3 ≤ (9 / 8) * M := by
      have h145 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (145 / 323 : ℝ)
          ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ht_pos ht_le1 (by norm_num)
      have hmid : (μ * (_root_.BoseGases.a v) ^ 3) ^ (145 / 323 : ℝ)
            * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
          ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
            * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
        mul_le_mul_of_nonneg_right h145 hPnn
      calc T3 ≤ (9 / 8) * (μ * (_root_.BoseGases.a v) ^ 3) ^ (145 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := h3
        _ = (9 / 8) * ((μ * (_root_.BoseGases.a v) ^ 3) ^ (145 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) := by ring
        _ ≤ (9 / 8) * ((μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ)
              * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) :=
            mul_le_mul_of_nonneg_left hmid (by norm_num)
        _ = (9 / 8) * M := by dsimp only [M]
    have hsum : T1 + T2 + T3 ≤ 53000 * M := by
      have hs1 : T1 + T2 + T3 ≤ (120 * M + 52488 * M) + 9 / 8 * M :=
        add_le_add (add_le_add h1' h2') h3'
      have hcoef : (120 * M + 52488 * M) + 9 / 8 * M ≤ 53000 * M := by
        have h1 : (120 * M + 52488 * M) + 9 / 8 * M = (120 + 52488 + 9 / 8 : ℝ) * M := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          (by norm_num : (120 + 52488 + 9 / 8 : ℝ) ≤ 53000) hMnn
      exact le_trans hs1 hcoef
    have hfin : Work.SmallBoxA0.d1C Ct * (53000 * M)
        ≤ 291 * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
      have hrew : Work.SmallBoxA0.d1C Ct * (53000 * M)
          = (Work.SmallBoxA0.d1C Ct * 53000
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (78 / 323 : ℝ))
            * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
        dsimp only [M]; ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hA hPnn
    calc Work.SmallBoxA0.d1C Ct * (T1 + T2 + T3)
        ≤ Work.SmallBoxA0.d1C Ct * (53000 * M) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hd1C)
      _ ≤ 291 * (μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := hfin
      _ = 291 * μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by ring

end Work.BoseFixR
