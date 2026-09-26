import Submission.Work.CoreTopology.Disk

/-!
# The meridian and longitude circles are simple

`IsSimple` (in `Submission.Work.CoreTopology.Disk`) says that a closed curve on the torus is
injective on a fundamental period `[0, 2π)` — an embedded (simple) closed curve.  Here we
check this for the meridian and the longitude circles, which is what allows them to be used
in Pardon's invariant `I(F, β)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The meridian circle of a parametrised torus is simple. -/
theorem meridianCurve_simple (P : ParamTorus) (θ : ℝ) : IsSimple P (meridianCurve P θ) := by
  intro φ hφ φ' hφ' h
  rw [Set.mem_Ico] at hφ hφ'
  obtain ⟨-, ⟨k, hk⟩⟩ := (P.inj_mod θ φ θ φ').mp h
  have hk' : φ - φ' = (k : ℝ) * (2 * Real.pi) := by linarith
  have hlt : |φ - φ'| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hφ.1, hφ.2, hφ'.1, hφ'.2]
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(k : ℝ)| * (2 * Real.pi) = |φ - φ'| := by
    rw [← abs_of_pos hpos, ← abs_mul, ← hk']
  have hk1 : |(k : ℝ)| < 1 := by
    rcases lt_or_ge 0 (|(k : ℝ)|) with h0 | h0
    · nlinarith [Real.pi_pos, hlt]
    · have hz : |(k : ℝ)| = 0 := le_antisymm h0 (abs_nonneg _)
      rw [hz, zero_mul] at habs
      linarith [abs_nonneg (φ - φ'), habs]
  have hk0 : k = 0 := by
    have h2 : -(1 : ℝ) < (k : ℝ) := (abs_lt.mp hk1).1
    have h3 : (k : ℝ) < 1 := (abs_lt.mp hk1).2
    have h2' : (-1 : ℤ) < k := by exact_mod_cast h2
    have h3' : k < (1 : ℤ) := by exact_mod_cast h3
    omega
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- The longitude circle of a parametrised torus is simple. -/
theorem longitudeCurve_simple (P : ParamTorus) (φ : ℝ) : IsSimple P (longitudeCurve P φ) := by
  intro θ hθ θ' hθ' h
  rw [Set.mem_Ico] at hθ hθ'
  obtain ⟨⟨k, hk⟩, -⟩ := (P.inj_mod θ φ θ' φ).mp h
  have hk' : θ - θ' = (k : ℝ) * (2 * Real.pi) := by linarith
  have hlt : |θ - θ'| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(k : ℝ)| * (2 * Real.pi) = |θ - θ'| := by
    rw [← abs_of_pos hpos, ← abs_mul, ← hk']
  have hk1 : |(k : ℝ)| < 1 := by
    rcases lt_or_ge 0 (|(k : ℝ)|) with h0 | h0
    · nlinarith [Real.pi_pos, hlt]
    · have hz : |(k : ℝ)| = 0 := le_antisymm h0 (abs_nonneg _)
      rw [hz, zero_mul] at habs
      linarith [abs_nonneg (θ - θ'), habs]
  have hk0 : k = 0 := by
    have h2 : -(1 : ℝ) < (k : ℝ) := (abs_lt.mp hk1).1
    have h3 : (k : ℝ) < 1 := (abs_lt.mp hk1).2
    have h2' : (-1 : ℤ) < k := by exact_mod_cast h2
    have h3' : k < (1 : ℤ) := by exact_mod_cast h3
    omega
  rw [hk0] at hk
  push_cast at hk
  linarith

end

end Work.CoreTopology
