import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6Est

/-- Auxiliary arithmetic fact: if `0 ≤ x`, `x ≤ a` and `x ≤ b`, then
`x ≤ √(a * b)`. -/
lemma le_sqrt_mul {x a b : ℝ} (hx : 0 ≤ x) (ha : x ≤ a) (hb : x ≤ b) : x ≤ Real.sqrt (a * b) := by
  have ha0 : 0 ≤ a := le_trans hx ha
  have hb0 : 0 ≤ b := le_trans hx hb
  have hsq : x ^ 2 ≤ a * b := by
    have h := mul_le_mul ha hb hx ha0
    simpa [pow_two] using h
  exact (Real.le_sqrt hx (mul_nonneg ha0 hb0)).2 hsq

theorem beta_close_bounds {K : FsKernel} {r : ℝ} (hηT : K.η * K.T ≤ 1) (hr0 : 0 ≤ r) (hrT : r ≤ K.T) :
    |K.β r - 8 * Real.pi| ≤ Real.sqrt (K.η * r * (K.B + 8 * Real.pi)) ∧
    |K.β r - 8 * Real.pi| ≤ K.η * r ∧ K.β r ≤ 8 * Real.pi + 1 ∧ 8 * Real.pi - 1 ≤ K.β r := by
  have hclose := K.close r hr0 hrT
  have hηr0 : 0 ≤ K.η * r := mul_nonneg K.ηnn hr0
  have hηr1 : K.η * r ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hrT K.ηnn) hηT
  have hB0 : 0 ≤ K.B + 8 * Real.pi := by linarith [K.Bnn, Real.pi_pos]
  -- `|β r - 8π| ≤ B + 8π` from `0 ≤ β r ≤ B`
  have hbound : |K.β r - 8 * Real.pi| ≤ K.B + 8 * Real.pi := by
    rw [abs_le]
    exact ⟨by linarith [K.nonneg r, K.Bnn, Real.pi_pos], by linarith [K.bound r, Real.pi_pos]⟩
  have hcl := abs_le.mp hclose
  refine ⟨le_sqrt_mul (abs_nonneg _) hclose hbound, hclose, ?_, ?_⟩
  · linarith [hcl.2, hηr1]
  · linarith [hcl.1, hηr1]

end Work.BoseB6Est
