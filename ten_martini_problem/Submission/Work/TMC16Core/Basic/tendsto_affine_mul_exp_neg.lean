import Mathlib

namespace Work.TMC16Core.Basic

/-- The exponential factor `x ↦ exp (-(c * x))` with `c > 0` tends to `0` at `+∞`. -/
private lemma tendsto_exp_neg_mul_atTop_nhds_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun x : ℝ => Real.exp (-(c * x))) Filter.atTop (nhds 0) := by
  have h' : Filter.Tendsto (fun x : ℝ => (-c) * x) Filter.atTop Filter.atBot :=
    (Filter.tendsto_id).const_mul_atTop_of_neg (show (-c) < 0 by linarith)
  exact Real.tendsto_exp_atBot.comp (by simpa [neg_mul] using h')

theorem tendsto_affine_mul_exp_neg (a c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun k : ℕ => (a + (k : ℝ)) * Real.exp (-(c * (k : ℝ)))) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (-(c * x))) Filter.atTop (nhds 0) :=
    tendsto_exp_neg_mul_atTop_nhds_zero c hc
  have hlin : Filter.Tendsto (fun x : ℝ => x * Real.exp (-(c * x))) Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    simpa using h
  have hg : Filter.Tendsto (fun x : ℝ => (a + x) * Real.exp (-(c * x))) Filter.atTop (nhds 0) := by
    have hsplit : (fun x : ℝ => (a + x) * Real.exp (-(c * x)))
        = fun x : ℝ => a * Real.exp (-(c * x)) + x * Real.exp (-(c * x)) := by
      funext x; ring
    rw [hsplit]
    simpa using ((hexp.const_mul a)).add hlin
  exact hg.comp (tendsto_natCast_atTop_atTop (R := ℝ))

end Work.TMC16Core.Basic
