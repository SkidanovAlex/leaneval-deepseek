import Mathlib

namespace Work.Parab.inversion

/-- For every `c > 0` and every pair of constants `a b`, the affine-logarithmic
expression `a * log (2x) + b` is eventually strictly below `c * x`.
This is the elementary `log = o(x)` fact, in a form convenient for the
parabolic inversion estimates. -/
lemma exists_mul_log_lt_aux {a b c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ x → a * Real.log (2 * x) + b < c * x := by
  have hlog2 : (fun x : ℝ => Real.log (2 * x)) =o[Filter.atTop] id := by
    have h1 : (fun x : ℝ => Real.log (2 * x)) =o[Filter.atTop] (fun x : ℝ => 2 * x) :=
      Real.isLittleO_log_id_atTop.comp_tendsto
        (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) Filter.tendsto_id)
    have h2 : (fun x : ℝ => 2 * x) =O[Filter.atTop] (id : ℝ → ℝ) := by
      simpa using Asymptotics.IsBigO.const_mul_left
        (Asymptotics.isBigO_refl (id : ℝ → ℝ) Filter.atTop) (2:ℝ)
    exact h1.trans_isBigO h2
  have hf : (fun x : ℝ => a * Real.log (2 * x)) =o[Filter.atTop] id := hlog2.const_mul_left a
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖a * Real.log (2 * x)‖ ≤ (c / 2) * ‖x‖ :=
    Asymptotics.isLittleO_iff.mp hf (c := c / 2) (by linarith)
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, b < (c / 2) * x := by
    filter_upwards [Filter.eventually_ge_atTop (2 * b / c + 1)] with x hx
    have hx2 : 2 * b / c < x := by linarith
    have hpos : 0 < c / 2 := by linarith
    calc b = (c / 2) * (2 * b / c) := by field_simp
      _ < (c / 2) * x := mul_lt_mul_of_pos_left hx2 hpos
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, (0:ℝ) ≤ x := Filter.eventually_ge_atTop 0
  have hall : ∀ᶠ x : ℝ in Filter.atTop, a * Real.log (2 * x) + b < c * x := by
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx3] at hx1
    have hle : a * Real.log (2 * x) ≤ c / 2 * x := le_trans (le_abs_self _) hx1
    linarith
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.mp hall
  exact ⟨max R0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx =>
    hR0 x (le_trans (le_max_left _ _) hx)⟩

theorem exists_mul_log_lt {A K ε : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ x →
      2 * A * (A * Real.log (2 * x) + K) < (ε / 2) * x ∧
      A * Real.log (2 * x) + K < x / 16 := by
  obtain ⟨R1, -, hR1⟩ := exists_mul_log_lt_aux (a := 2 * A * A) (b := 2 * A * K) (c := ε / 2)
    (by linarith)
  obtain ⟨R2, -, hR2⟩ := exists_mul_log_lt_aux (a := A) (b := K) (c := 1 / 16)
    (by norm_num)
  refine ⟨max (max R1 R2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  have hxR1 : R1 ≤ x := le_trans (le_trans (le_max_left R1 R2) (le_max_left (max R1 R2) 1)) hx
  have hxR2 : R2 ≤ x := le_trans (le_trans (le_max_right R1 R2) (le_max_left (max R1 R2) 1)) hx
  constructor
  · have h := hR1 x hxR1
    have heq : 2 * A * (A * Real.log (2 * x) + K) = 2 * A * A * Real.log (2 * x) + 2 * A * K := by
      ring
    rw [heq]; exact h
  · have h := hR2 x hxR2
    linarith

end Work.Parab.inversion
