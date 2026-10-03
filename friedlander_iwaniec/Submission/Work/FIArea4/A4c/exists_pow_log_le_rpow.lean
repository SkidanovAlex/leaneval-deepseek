import Mathlib

namespace Work.FIArea4.A4c

/-- For any `C ≥ 1` and `ε > 0`, eventually `(log x)^C ≤ x^ε`.
This is the usual statement that `log` grows slower than any positive power:
`log =o[atTop] x^(ε/C)`, then raise both sides to the `C`-th power. -/
theorem exists_pow_log_le_rpow (C : ℕ) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → (Real.log x) ^ C ≤ x ^ ε := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hδ : 0 < ε / C := div_pos hε hCpos
  -- `log x = o(x^(ε/C))` at `+∞`.
  have hlittle : Real.log =o[Filter.atTop] fun x : ℝ => x ^ (ε / C) :=
    isLittleO_log_rpow_atTop hδ
  -- hence, eventually, `log x ≤ x^(ε/C)` (on `x ≥ 1` the norms disappear).
  have hbound : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ (ε / C) := by
    have h := Asymptotics.IsLittleO.def hlittle (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) (ε / C)), one_mul] at hx
    exact hx
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max a 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right a 1) hx
  have hxa : a ≤ x := le_trans (le_max_left a 1) hx
  have hx0 : 0 ≤ x := by linarith
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hle : Real.log x ≤ x ^ (ε / C) := ha x hxa
  calc (Real.log x) ^ C ≤ (x ^ (ε / C)) ^ C := pow_le_pow_left₀ hlogx_nonneg hle C
    _ = x ^ ((ε / C) * (C : ℝ)) := by
        rw [← Real.rpow_natCast (x ^ (ε / C)) C, ← Real.rpow_mul hx0 (ε / C) (C : ℝ)]
    _ = x ^ ε := by
        rw [div_mul_cancel₀ ε hCpos.ne']

end Work.FIArea4.A4c
