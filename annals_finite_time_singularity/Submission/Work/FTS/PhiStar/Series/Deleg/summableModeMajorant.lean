import Mathlib.Analysis.PSeries

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem summableModeMajorant (K A : ℝ) :
    Summable (fun m : ℕ => (if m = 0 then K else 0) + A * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  -- The `if m = 0` term has finite support, hence is summable ...
  have h1 : Summable (fun m : ℕ => if m = 0 then K else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun b hb => by
      simp only [Finset.mem_singleton] at hb
      simp [hb])
  -- ... and the `m^{-3/2}` tail is the convergent `p`-series with `p = 3/2 > 1`.
  have h2 : Summable (fun m : ℕ => A * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr (by norm_num) |>.mul_left A
  exact h1.add h2

end Work.FTS.PhiStar.Series.Deleg
