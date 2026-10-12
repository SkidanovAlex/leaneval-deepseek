import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

theorem neumann_heat_one_dim_sub_le {s t u v : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |(∑' k : ℕ, Real.cos (Real.pi * k * (u + s / 2) / s) * Real.cos (Real.pi * k * (v + s / 2) / s)
        * Real.exp (-(t * (Real.pi * k / s) ^ 2)) * (if k = 0 then s else s / 2)⁻¹) - s⁻¹|
      ≤ 2 * s⁻¹ * (Real.exp (-(t * (Real.pi / s) ^ 2)) / (1 - Real.exp (-(t * (Real.pi / s) ^ 2)))) := by
  set q : ℝ := Real.exp (-(t * (Real.pi / s) ^ 2)) with hqdef
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    rw [hqdef, ← Real.exp_zero, Real.exp_lt_exp]
    have : 0 < t * (Real.pi / s) ^ 2 := by positivity
    linarith
  set f : ℕ → ℝ := fun k : ℕ =>
      Real.cos (Real.pi * k * (u + s / 2) / s) * Real.cos (Real.pi * k * (v + s / 2) / s)
        * Real.exp (-(t * (Real.pi * k / s) ^ 2)) * (if k = 0 then s else s / 2)⁻¹ with hfdef
  have hfac : ∀ k : ℕ, |(if k = 0 then s else s / 2 : ℝ)⁻¹| ≤ 2 * s⁻¹ := by
    intro k
    split_ifs with hk
    · rw [abs_of_pos (inv_pos.mpr hs)]
      nlinarith [inv_nonneg.mpr hs.le]
    · have h : (s / 2 : ℝ)⁻¹ = 2 * s⁻¹ := by field_simp
      rw [h, abs_of_nonneg (by positivity)]
  have hexp : ∀ k : ℕ, Real.exp (-(t * (Real.pi * k / s) ^ 2)) ≤ q ^ k := by
    intro k
    rw [hqdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hsne : s ≠ 0 := ne_of_gt hs
    have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
        nlinarith
    have hkey : (Real.pi * (k : ℝ) / s) ^ 2 = (Real.pi / s) ^ 2 * (k : ℝ) ^ 2 := by
      rw [div_pow, div_pow]; ring
    rw [hkey]
    have hstep : t * ((Real.pi / s) ^ 2 * (k : ℝ)) ≤ t * ((Real.pi / s) ^ 2 * (k : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      exact mul_le_mul_of_nonneg_left hkk (sq_nonneg _)
    nlinarith [hstep]
  have hbound : ∀ k : ℕ, ‖f k‖ ≤ 2 * s⁻¹ * q ^ k := by
    intro k
    have h1 := Real.abs_cos_le_one (Real.pi * (k : ℝ) * (u + s / 2) / s)
    have h2 := Real.abs_cos_le_one (Real.pi * (k : ℝ) * (v + s / 2) / s)
    have h3 := hexp k
    have h4 := hfac k
    rw [hfdef, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |Real.cos (Real.pi * (k : ℝ) * (u + s / 2) / s)|
            * |Real.cos (Real.pi * (k : ℝ) * (v + s / 2) / s)|
            * Real.exp (-(t * (Real.pi * (k : ℝ) / s) ^ 2))
            * |(if k = 0 then s else s / 2 : ℝ)⁻¹|
        ≤ 1 * 1 * q ^ k * (2 * s⁻¹) := by gcongr
      _ = 2 * s⁻¹ * q ^ k := by ring
  have hsum_geom : Summable (fun k : ℕ => 2 * s⁻¹ * q ^ k) :=
    (summable_geometric_of_lt_one hqpos.le hqlt).mul_left (2 * s⁻¹)
  have hf : Summable f := Summable.of_norm_bounded hsum_geom hbound
  have hf0 : f 0 = s⁻¹ := by
    rw [hfdef]; simp
  have hgeom_tail : (∑' k : ℕ, q ^ (k + 1)) = q / (1 - q) := by
    rw [show (∑' k : ℕ, q ^ (k + 1)) = q * ∑' k : ℕ, q ^ k from by
          rw [← tsum_mul_left]; exact tsum_congr (fun k => pow_succ' q k)]
    rw [tsum_geometric_of_lt_one hqpos.le hqlt, div_eq_mul_inv]
  have hsplit : (∑' k : ℕ, f k) = s⁻¹ + ∑' k : ℕ, f (k + 1) := by
    rw [hf.tsum_eq_zero_add, hf0]
  rw [hsplit]
  have hsimp : s⁻¹ + (∑' k : ℕ, f (k + 1)) - s⁻¹ = ∑' k : ℕ, f (k + 1) := by ring
  rw [hsimp]
  have hgeom_shift : Summable (fun k : ℕ => 2 * s⁻¹ * q ^ (k + 1)) :=
    (summable_nat_add_iff (f := fun k : ℕ => 2 * s⁻¹ * q ^ k) 1).mpr hsum_geom
  have hnorm_summ : Summable (fun k : ℕ => ‖f (k + 1)‖) := by
    refine Summable.of_norm_bounded hgeom_shift (fun k => ?_)
    rw [norm_norm]; exact hbound (k + 1)
  calc |∑' k : ℕ, f (k + 1)|
      ≤ ∑' k : ℕ, ‖f (k + 1)‖ := norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' k : ℕ, 2 * s⁻¹ * q ^ (k + 1) :=
        Summable.tsum_le_tsum (fun k => hbound (k + 1)) hnorm_summ hgeom_shift
    _ = 2 * s⁻¹ * (q / (1 - q)) := by rw [tsum_mul_left, hgeom_tail]

end Commons.Analysis.Fourier