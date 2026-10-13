import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ENNReal NNReal

namespace Work.Stability

/-- A bounded Lipschitz function is `α`-Hölder for every `α ≤ 1`: with `d = dist x y` one has
`dist (f x) (f y) ≤ min (K d) (2M)`, and `min (K d) (2M) ≤ max K (2M) * d ^ α` because `d ≤ d ^ α`
for `0 ≤ d ≤ 1` and `1 ≤ d ^ α` for `1 ≤ d`. -/
theorem HolderOfBoundedLipschitz {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] {α : NNReal} (hα : α ≤ 1) {K : NNReal} {f : X → E}
    (hb : IsBoundedFun f) (hl : LipschitzWith K f) : Holder α f := by
  -- The uniform bound supplied by boundedness, as an `ℝ≥0` diameter.
  have hbdd : Metric.ediam (f '' Set.univ) ≠ ⊤ := Metric.isBounded_iff_ediam_ne_top.mp hb
  let D : NNReal := (Metric.ediam (f '' Set.univ)).toNNReal
  have hD : (D : ℝ≥0∞) = Metric.ediam (f '' Set.univ) := ENNReal.coe_toNNReal hbdd
  have hedge : ∀ x y : X, edist (f x) (f y) ≤ (D : ℝ≥0∞) := by
    intro x y
    rw [hD]
    exact Metric.edist_le_ediam_of_mem (Set.mem_image_of_mem f (Set.mem_univ x))
      (Set.mem_image_of_mem f (Set.mem_univ y))
  refine ⟨K + D, fun x y => ?_⟩
  have hsplit : ((K + D : NNReal) : ℝ≥0∞) * edist x y ^ (α : ℝ)
      = (K : ℝ≥0∞) * edist x y ^ (α : ℝ) + (D : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
    rw [ENNReal.coe_add, add_mul]
  rw [hsplit]
  have hl' : edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y := hl x y
  rcases eq_or_ne α 0 with hα0 | hα0
  · -- `d ^ 0 = 1`: only boundedness is used.
    have hpow : edist x y ^ (α : ℝ) = 1 := by rw [hα0]; simp
    calc edist (f x) (f y) ≤ (D : ℝ≥0∞) := hedge x y
      _ = (D : ℝ≥0∞) * 1 := (mul_one _).symm
      _ = (D : ℝ≥0∞) * edist x y ^ (α : ℝ) := by rw [hpow]
      _ ≤ (K : ℝ≥0∞) * edist x y ^ (α : ℝ) + (D : ℝ≥0∞) * edist x y ^ (α : ℝ) :=
          le_add_left le_rfl
  · have hαpos : (0 : ℝ) < (α : ℝ) := by
      have h : (0 : NNReal) < α := lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ α) (Ne.symm hα0)
      exact_mod_cast h
    by_cases hle : edist x y ≤ 1
    · -- Small distances: `d ≤ d ^ α` and the Lipschitz bound dominate.
      have hpow : edist x y ≤ edist x y ^ (α : ℝ) := by
        have h := ENNReal.rpow_le_rpow_of_exponent_ge hle
          (show (α : ℝ) ≤ 1 by exact_mod_cast hα)
        rwa [ENNReal.rpow_one] at h
      calc edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y := hl'
        _ ≤ (K : ℝ≥0∞) * edist x y ^ (α : ℝ) := mul_le_mul_right hpow _
        _ ≤ (K : ℝ≥0∞) * edist x y ^ (α : ℝ) + (D : ℝ≥0∞) * edist x y ^ (α : ℝ) :=
            le_add_right le_rfl
    · -- Large distances: `1 ≤ d ^ α` and the uniform bound dominate.
      have hgt : (1 : ℝ≥0∞) < edist x y := not_le.mp hle
      have hone : (1 : ℝ≥0∞) ≤ edist x y ^ (α : ℝ) :=
        ENNReal.one_le_rpow (le_of_lt hgt) hαpos
      calc edist (f x) (f y) ≤ (D : ℝ≥0∞) := hedge x y
        _ = (D : ℝ≥0∞) * 1 := (mul_one _).symm
        _ ≤ (D : ℝ≥0∞) * edist x y ^ (α : ℝ) := mul_le_mul_right hone _
        _ ≤ (K : ℝ≥0∞) * edist x y ^ (α : ℝ) + (D : ℝ≥0∞) * edist x y ^ (α : ℝ) :=
            le_add_left le_rfl

end Work.Stability
