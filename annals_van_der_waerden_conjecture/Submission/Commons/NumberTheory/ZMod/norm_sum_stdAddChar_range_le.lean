import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Finset

namespace Commons.NumberTheory.ZMod

/-- Partial-period (Gauss sum over an interval) bound for the standard additive
character of `ZMod p`: for `1 ≤ d ≤ p/2` the sum of `stdAddChar (k * d)` over
`k < L` is bounded by both `L` and `p / (2d)` — the latter being the
`O(1/d)` cancellation coming from `‖1 - stdAddChar d‖ ≥ 4d/p`. -/
theorem norm_sum_stdAddChar_range_le (p : ℕ) [Fact p.Prime] (d : ℕ) (hd1 : 1 ≤ d)
    (hd2 : 2 * d ≤ p) (L : ℕ) :
    ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * (d : ZMod p))‖
      ≤ min (L : ℝ) ((p : ℝ) / (2 * (d : ℝ))) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
  have h2dR : (2 : ℝ) * d ≤ p := by exact_mod_cast hd2
  -- the point of evaluation
  set x : ℝ := 2 * Real.pi * d / p with hx
  have hxhalf : x / 2 = Real.pi * d / p := by rw [hx]; ring
  have hcast : ((d : ℤ) : ZMod p) = (d : ZMod p) := by push_cast; rfl
  have hexpz : ZMod.stdAddChar (d : ZMod p) = Complex.exp (Complex.I * (x : ℂ)) := by
    rw [← hcast, ZMod.stdAddChar_coe]
    congr 1
    rw [hx]; push_cast; ring
  set z : ℂ := ZMod.stdAddChar (d : ZMod p) with hz
  -- auxiliary real algebra
  have hdp : 4 * (d : ℝ) / p = 2 * (2 / Real.pi * (x / 2)) := by
    rw [hxhalf]; field_simp; ring
  have hxhalf_nonneg : 0 ≤ x / 2 := by rw [hxhalf]; positivity
  have hxhalf_le : x / 2 ≤ Real.pi / 2 := by
    rw [hxhalf, div_le_div_iff₀ hp_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [h2dR, Real.pi_pos]
  have hsin_nonneg : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hxhalf_nonneg
      (by linarith [hxhalf_le, Real.pi_pos])
  have hsin_ge : 2 / Real.pi * (x / 2) ≤ Real.sin (x / 2) :=
    Real.mul_le_sin hxhalf_nonneg hxhalf_le
  -- norm of `z` and of `1 - z`
  have hznorm : ‖z‖ = 1 := by
    rw [hexpz, Complex.norm_exp_I_mul_ofReal]
  have hnorm1sub : ‖(1 : ℂ) - z‖ = 2 * Real.sin (x / 2) := by
    rw [hexpz, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show ‖2 * Real.sin (x / 2)‖ = |2 * Real.sin (x / 2)| by simp]
    rw [abs_of_nonneg (by linarith)]
  have hzsub_ge : 4 * (d : ℝ) / p ≤ ‖(1 : ℂ) - z‖ := by
    rw [hnorm1sub, hdp]
    linarith [hsin_ge]
  have hzsub_pos : 0 < ‖(1 : ℂ) - z‖ :=
    lt_of_lt_of_le (by positivity) hzsub_ge
  -- geometric bound
  have hS : (∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * (d : ZMod p)))
      = ∑ k ∈ Finset.range L, z ^ k := by
    rw [hz]
    apply Finset.sum_congr rfl
    intro k _
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  have hgeom : (∑ k ∈ Finset.range L, z ^ k) * (1 - z) = 1 - z ^ L :=
    geom_sum_mul_neg z L
  have hzL : ‖z ^ L‖ = 1 := by rw [norm_pow, hznorm, one_pow]
  have hle2 : ‖(1 : ℂ) - z ^ L‖ ≤ 2 := by
    calc ‖(1 : ℂ) - z ^ L‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ L‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, hzL]; norm_num
  have hmul : ‖(∑ k ∈ Finset.range L, z ^ k)‖ * ‖(1 : ℂ) - z‖ ≤ 2 := by
    rw [← norm_mul, hgeom]; exact hle2
  have hS_le : ‖(∑ k ∈ Finset.range L, z ^ k)‖ ≤ 2 / ‖(1 : ℂ) - z‖ :=
    (le_div_iff₀ hzsub_pos).mpr hmul
  have hstep : 2 / ‖(1 : ℂ) - z‖ ≤ (p : ℝ) / (2 * (d : ℝ)) := by
    have h4 : (0 : ℝ) < 4 * (d : ℝ) / p := by positivity
    calc 2 / ‖(1 : ℂ) - z‖ ≤ 2 / (4 * (d : ℝ) / p) :=
          div_le_div_of_nonneg_left (by norm_num) h4 hzsub_ge
      _ = (p : ℝ) / (2 * (d : ℝ)) := by field_simp; ring
  have hLbound : ‖(∑ k ∈ Finset.range L, z ^ k)‖ ≤ (L : ℝ) := by
    calc ‖(∑ k ∈ Finset.range L, z ^ k)‖ ≤ ∑ k ∈ Finset.range L, ‖z ^ k‖ :=
          norm_sum_le _ _
      _ = ∑ _k ∈ Finset.range L, (1 : ℝ) := by
          apply Finset.sum_congr rfl; intro k _
          rw [norm_pow, hznorm, one_pow]
      _ = (L : ℝ) := by simp
  rw [hS]
  exact le_min hLbound (le_trans hS_le hstep)

end Commons.NumberTheory.ZMod