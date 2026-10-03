import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star

namespace Commons.Analysis.Real

theorem strictMono_floor_mul_geom (s : ℕ) (hs : 1 ≤ s) :
    StrictMono fun n : ℕ => Nat.floor ((s : ℝ) * (1 + (s : ℝ)⁻¹) ^ n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  set α : ℝ := 1 + (s : ℝ)⁻¹ with hαdef
  have hsR : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hs)
  have hαpos : 0 < α := by
    rw [hαdef]
    have : 0 < (s : ℝ)⁻¹ := inv_pos.mpr hsR
    linarith
  have hα1 : 1 ≤ α := by
    rw [hαdef]
    have : 0 < (s : ℝ)⁻¹ := inv_pos.mpr hsR
    linarith
  have hpow1 : 1 ≤ α ^ n := one_le_pow₀ hα1
  have ha_nonneg : 0 ≤ (s : ℝ) * α ^ n := by positivity
  have hsα : (s : ℝ) * α = (s : ℝ) + 1 := by
    rw [hαdef]
    field_simp
  have hstep : (s : ℝ) * α ^ (n + 1) = (s : ℝ) * α ^ n + α ^ n := by
    rw [pow_succ]
    calc (s : ℝ) * (α ^ n * α) = ((s : ℝ) * α) * α ^ n := by ring
      _ = ((s : ℝ) + 1) * α ^ n := by rw [hsα]
      _ = (s : ℝ) * α ^ n + α ^ n := by ring
  rw [hstep]
  have hle : Nat.floor ((s : ℝ) * α ^ n + 1) ≤ Nat.floor ((s : ℝ) * α ^ n + α ^ n) :=
    Nat.floor_le_floor (by linarith)
  rw [Nat.floor_add_one ha_nonneg] at hle
  omega

end Commons.Analysis.Real