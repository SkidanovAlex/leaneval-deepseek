import Submission.Work.LT.half_le_sin_sq_pi

/-!
# `sin²(π m/p) ≥ 1/2` for the balanced representative of a residue

Let `m = |valMinAbs t|` be the absolute value of the balanced (least-absolute-value)
representative of `t : ZMod p`.  The defining property `ZMod.natAbs_valMinAbs_le` gives
`2 m ≤ p`, i.e. `m/p ≤ 1/2`, and the hypothesis `p ≤ 4 m` gives `1/4 ≤ m/p`.
On `[1/4, 1/2]` the function `x ↦ sin(π x)²` is at least `sin(π/4)² = 1/2`
(monotonicity of `sin` on `[−π/2, π/2]` together with the endpoints' values), which is
`Work.LT.half_le_sin_sq_pi`.
-/

namespace Work.LT

theorem sin_sq_natAbs_ge_half (p : ℕ) [NeZero p] (t : ZMod p)
    (h : p ≤ 4 * (ZMod.valMinAbs t).natAbs) :
    1 / 2 ≤ Real.sin (Real.pi * ((ZMod.valMinAbs t).natAbs : ℝ) / p) ^ 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    have := NeZero.pos p
    exact_mod_cast this
  set m := (ZMod.valMinAbs t).natAbs with hm
  -- `m/p ≤ 1/2` : the balanced representative has absolute value at most `p/2`.
  have h2m : 2 * m ≤ p := by
    have hb := ZMod.natAbs_valMinAbs_le (n := p) t
    rw [← hm] at hb
    omega
  -- `1/4 ≤ m/p` : the hypothesis `p ≤ 4 m`.
  have h4m : p ≤ 4 * m := by rw [hm]; exact h
  have hhalf : (m : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_iff₀ hp_pos]
    have : (2 : ℝ) * (m : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2m
    linarith
  have hquarter : (1 : ℝ) / 4 ≤ (m : ℝ) / p := by
    rw [le_div_iff₀ hp_pos]
    have : (p : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast h4m
    linarith
  have key := half_le_sin_sq_pi ((m : ℝ) / p) hquarter hhalf
  simpa only [mul_div_assoc] using key

end Work.LT
