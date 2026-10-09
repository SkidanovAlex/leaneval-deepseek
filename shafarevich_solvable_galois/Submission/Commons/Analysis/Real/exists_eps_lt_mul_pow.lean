import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Real

/-- Quantitative "small denominator" estimate: for positive `A`, `δ` and nonnegative `C`,
one can choose `ε > 0` so small that every `b ≤ ε * C` is dominated by `a' * δ ^ d`
whenever `a'` is within `ε` below `A`. -/
lemma exists_eps_lt_mul_pow {A δ C : ℝ} (hA : 0 < A) (hδ : 0 < δ) (hC : 0 ≤ C) (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, A - ε ≤ a' → b ≤ ε * C → b < a' * δ ^ d := by
  set D : ℝ := δ ^ d with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact pow_pos hδ d
  set E : ℝ := C + D with hEdef
  have hEpos : 0 < E := by
    rw [hEdef]
    linarith
  refine ⟨A * D / (2 * E + 1), ?_, ?_⟩
  · positivity
  · intro a' b ha' hb
    have hden : 0 < 2 * E + 1 := by linarith
    have hεpos : 0 < A * D / (2 * E + 1) := by positivity
    have hεE : (A * D / (2 * E + 1)) * E < A * D / 2 := by
      rw [div_mul_eq_mul_div]
      rw [div_lt_div_iff₀]
      · nlinarith
      · linarith
      · norm_num
    have hεC : (A * D / (2 * E + 1)) * C < A * D / 2 := by
      have hC_le_E : C ≤ E := by
        rw [hEdef]
        linarith
      calc
        (A * D / (2 * E + 1)) * C ≤ (A * D / (2 * E + 1)) * E := by
          exact mul_le_mul_of_nonneg_left hC_le_E hεpos.le
        _ < A * D / 2 := hεE
    have hε_le_half : A * D / (2 * E + 1) ≤ A / 2 := by
      rw [div_le_iff₀ hden]
      have hD_le_E : D ≤ E := by
        rw [hEdef]
        linarith
      nlinarith
    have ha'_lower : A - A * D / (2 * E + 1) ≥ A / 2 := by linarith
    have hpow : A * D / 2 ≤ a' * D := by
      calc
        A * D / 2 = (A / 2) * D := by ring
        _ ≤ (A - A * D / (2 * E + 1)) * D := by
          exact mul_le_mul_of_nonneg_right ha'_lower hDpos.le
        _ ≤ a' * D := by
          exact mul_le_mul_of_nonneg_right ha' hDpos.le
    have hb_lt : b < A * D / 2 := lt_of_le_of_lt hb hεC
    calc
      b < A * D / 2 := hb_lt
      _ ≤ a' * D := hpow
      _ = a' * δ ^ d := by rw [hDdef]

end Commons.Analysis.Real