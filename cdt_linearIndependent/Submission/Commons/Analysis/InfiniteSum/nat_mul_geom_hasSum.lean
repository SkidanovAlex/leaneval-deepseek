import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open scoped BigOperators

namespace Commons.Analysis.InfiniteSum

/-- `Σₙ n·Xⁿ = X/(1−X)²` for real `‖X‖ < 1` (first moment of the geometric series). -/
lemma nat_mul_geom_hasSum {X : ℝ} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * X ^ n) (X / (1 - X) ^ 2) := by
  -- Σₙ (n+1 choose 1)·Xⁿ = 1/(1−X)², and Σₙ Xⁿ = 1/(1−X)
  have h1 : HasSum (fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * X ^ n)
      (1 / (1 - X) ^ (1 + 1)) := by
    simpa using (hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := X) hX)
  have hgeom : HasSum (fun n : ℕ => X ^ n) ((1 - X)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hX
  have hch : ∀ n : ℕ, (((n + 1).choose 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    intro n
    norm_num [Nat.choose_one_right]
  -- subtract the two series: (n+1)·Xⁿ − Xⁿ = n·Xⁿ
  have hsub := h1.sub hgeom
  have hsub' : HasSum (fun n : ℕ => (n : ℝ) * X ^ n)
      (1 / (1 - X) ^ (1 + 1) - (1 - X)⁻¹) := by
    apply HasSum.congr_fun hsub
    intro n
    rw [hch n]
    ring
  -- the closed form value: 1/(1−X)² − 1/(1−X) = X/(1−X)²
  have hXne : X ≠ 1 := by
    intro hXeq
    have : ‖X‖ = (1 : ℝ) := by simp [hXeq]
    linarith
  have hval : 1 / (1 - X) ^ (1 + 1) - (1 - X)⁻¹ = X / (1 - X) ^ 2 := by
    have hden : (1 - X : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hXne.symm)
    field_simp [hden]
    ring
  rw [hval] at hsub'
  exact hsub'

end Commons.Analysis.InfiniteSum