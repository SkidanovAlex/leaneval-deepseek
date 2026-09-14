import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Commons.NumberTheory.ZMod

/-- Distance-to-zero lower bound for the distance of `stdAddChar x` to `1`:
writing `d = min x.val (M - x.val)`, one has `4d/M ≤ ‖stdAddChar x - 1‖`. -/
private lemma norm_stdAddChar_sub_one_ge (M : ℕ) [NeZero M] (x : ZMod M) :
    4 * ((min x.val (M - x.val) : ℕ) : ℝ) / (M : ℝ) ≤ ‖ZMod.stdAddChar x - 1‖ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast NeZero.pos M
  have hxM : x.val < M := ZMod.val_lt x
  have hcast : (((M - x.val : ℕ)) : ℝ) = (M : ℝ) - (x.val : ℝ) := by
    rw [Nat.cast_sub hxM.le]
  have hnorm : ‖ZMod.stdAddChar x - 1‖
      = 2 * |Real.sin (Real.pi * (x.val : ℝ) / (M : ℝ))| := by
    have hxy : x = ((x.val : ℤ) : ZMod M) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hexp : ZMod.stdAddChar x
        = Complex.exp (Complex.I * ((2 * Real.pi * (x.val : ℝ) / (M : ℝ) : ℝ) : ℂ)) := by
      conv_lhs => rw [hxy, ZMod.stdAddChar_coe]
      congr 1
      push_cast
      ring
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show ‖(2 * Real.sin ((2 * Real.pi * (x.val : ℝ) / (M : ℝ)) / 2) : ℝ)‖
          = |2 * Real.sin ((2 * Real.pi * (x.val : ℝ) / (M : ℝ)) / 2)| by
        rw [Real.norm_eq_abs]]
    rw [show (2 * Real.pi * (x.val : ℝ) / (M : ℝ)) / 2
          = Real.pi * (x.val : ℝ) / (M : ℝ) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rcases le_total x.val (M - x.val) with h | h
  · have hmin : (min x.val (M - x.val) : ℕ) = x.val := min_eq_left h
    rw [hmin, hnorm]
    have h2 : 2 * (x.val : ℝ) ≤ (M : ℝ) := by
      have hcast' : (x.val : ℝ) ≤ (((M - x.val : ℕ)) : ℝ) := by exact_mod_cast h
      rw [hcast] at hcast'
      linarith
    have hnn : 0 ≤ Real.pi * (x.val : ℝ) / (M : ℝ) := by positivity
    have hle : Real.pi * (x.val : ℝ) / (M : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hM_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h2, Real.pi_pos]
    have hsin_ge : 2 / Real.pi * (Real.pi * (x.val : ℝ) / (M : ℝ))
        ≤ Real.sin (Real.pi * (x.val : ℝ) / (M : ℝ)) := Real.mul_le_sin hnn hle
    have hsin_nn : 0 ≤ Real.sin (Real.pi * (x.val : ℝ) / (M : ℝ)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hnn (by linarith [hle, Real.pi_pos])
    rw [abs_of_nonneg hsin_nn]
    have heq : 2 / Real.pi * (Real.pi * (x.val : ℝ) / (M : ℝ))
        = 2 * (x.val : ℝ) / (M : ℝ) := by
      field_simp
    rw [heq] at hsin_ge
    rw [show (4 : ℝ) * (x.val : ℝ) / (M : ℝ) = 2 * (2 * (x.val : ℝ) / (M : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hsin_ge (by norm_num)
  · have hmin : (min x.val (M - x.val) : ℕ) = M - x.val := min_eq_right h
    rw [hmin, hnorm]
    have h2 : 2 * (((M - x.val : ℕ)) : ℝ) ≤ (M : ℝ) := by
      have hcast' : (((M - x.val : ℕ)) : ℝ) ≤ (x.val : ℝ) := by exact_mod_cast h
      rw [hcast] at hcast'
      linarith
    have hnn : 0 ≤ Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ) := by positivity
    have hle : Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hM_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h2, Real.pi_pos]
    have hsin_ge : 2 / Real.pi * (Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ))
        ≤ Real.sin (Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ)) := Real.mul_le_sin hnn hle
    have hsin_nn : 0 ≤ Real.sin (Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hnn (by linarith [hle, Real.pi_pos])
    have hsin_eq : Real.sin (Real.pi * (x.val : ℝ) / (M : ℝ))
        = Real.sin (Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ)) := by
      rw [hcast]
      rw [show Real.pi * (x.val : ℝ) / (M : ℝ)
            = Real.pi - Real.pi * ((M : ℝ) - (x.val : ℝ)) / (M : ℝ) by
        field_simp
        ring]
      rw [Real.sin_pi_sub]
    rw [hsin_eq, abs_of_nonneg hsin_nn]
    have heq : 2 / Real.pi * (Real.pi * (((M - x.val : ℕ)) : ℝ) / (M : ℝ))
        = 2 * (((M - x.val : ℕ)) : ℝ) / (M : ℝ) := by
      field_simp
    rw [heq] at hsin_ge
    rw [show (4 : ℝ) * (((M - x.val : ℕ)) : ℝ) / (M : ℝ)
          = 2 * (2 * (((M - x.val : ℕ)) : ℝ) / (M : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hsin_ge (by norm_num)

theorem norm_sum_stdAddChar_range_le_zmod (M : ℕ) [NeZero M] (c : ZMod M) (hc : c ≠ 0)
    (L : ℕ) :
    ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod M) * c)‖
      ≤ min (L : ℝ) ((M : ℝ) / (2 * ((min c.val (M - c.val) : ℕ) : ℝ))) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast NeZero.pos M
  set d : ℕ := min c.val (M - c.val) with hd
  have hd_pos_nat : 1 ≤ d := by
    have h1 : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).mp h)
    have h2 : c.val < M := ZMod.val_lt c
    rw [hd]
    omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  set z : ℂ := ZMod.stdAddChar c with hz
  have hS : (∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod M) * c))
      = ∑ k ∈ Finset.range L, z ^ k := by
    rw [hz]
    apply Finset.sum_congr rfl
    intro k _
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [hS]
  have hzc : ZMod.stdAddChar c
      = Complex.exp (Complex.I * ((2 * Real.pi * (c.val : ℝ) / (M : ℝ) : ℝ) : ℂ)) := by
    have hxy : c = ((c.val : ℤ) : ZMod M) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_lhs => rw [hxy, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hznorm : ‖z‖ = 1 := by
    rw [hz, hzc, Complex.norm_exp_I_mul_ofReal]
  have hzsub_ge : 4 * (d : ℝ) / (M : ℝ) ≤ ‖(1 : ℂ) - z‖ := by
    rw [hz, norm_sub_rev]
    simpa only [hd] using norm_stdAddChar_sub_one_ge M c
  have hgeom : (∑ k ∈ Finset.range L, z ^ k) * (1 - z) = 1 - z ^ L := geom_sum_mul_neg z L
  have hzL : ‖z ^ L‖ = 1 := by rw [norm_pow, hznorm, one_pow]
  have hle2 : ‖(1 : ℂ) - z ^ L‖ ≤ 2 := by
    calc ‖(1 : ℂ) - z ^ L‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ L‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, hzL]; norm_num
  have hmul : ‖∑ k ∈ Finset.range L, z ^ k‖ * ‖(1 : ℂ) - z‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact hle2
  have hzsub_pos : 0 < ‖(1 : ℂ) - z‖ := lt_of_lt_of_le (by positivity) hzsub_ge
  have hS_le : ‖∑ k ∈ Finset.range L, z ^ k‖ ≤ 2 / ‖(1 : ℂ) - z‖ :=
    (le_div_iff₀ hzsub_pos).mpr hmul
  have hstep : 2 / ‖(1 : ℂ) - z‖ ≤ (M : ℝ) / (2 * (d : ℝ)) := by
    have h4 : (0 : ℝ) < 4 * (d : ℝ) / (M : ℝ) := by positivity
    calc 2 / ‖(1 : ℂ) - z‖ ≤ 2 / (4 * (d : ℝ) / (M : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) h4 hzsub_ge
      _ = (M : ℝ) / (2 * (d : ℝ)) := by field_simp; ring
  have hLbound : ‖∑ k ∈ Finset.range L, z ^ k‖ ≤ (L : ℝ) := by
    calc ‖∑ k ∈ Finset.range L, z ^ k‖ ≤ ∑ k ∈ Finset.range L, ‖z ^ k‖ := norm_sum_le _ _
      _ = ∑ _k ∈ Finset.range L, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [norm_pow, hznorm, one_pow]
      _ = (L : ℝ) := by simp
  exact le_min hLbound (le_trans hS_le hstep)

end Commons.NumberTheory.ZMod