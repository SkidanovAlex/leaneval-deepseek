import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeIbp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open Filter

/-- **The boundary-layer error of the zero-mode cut-off tends to `0`.**

`δ_n = 1/(n+1)`, and the layer contributes the factor `(1 + 1/δ_n)·(2δ_n)^{(3+η)/2}`.  Since
`(1 + 1/δ_n)·(2δ_n)^{s} = 2^s·(δ_n^s + δ_n^{s-1})`, the whole product is a constant times a sum
of two negative powers of `δ_n`, hence tends to `0` as `n → ∞` (`tendsto_delta_rpow`). -/
theorem SlotsZeroLayerTendsto {A C M : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    Filter.Tendsto (fun n : ℕ =>
      A * (1 + 1 / Work.FTS.StrongEps.EComparison.delta n)
        * (2 * C * (2 * Work.FTS.StrongEps.EComparison.delta n) ^ ((3 + Work.Spaces.eta) / 2)
            * M))
      Filter.atTop (nhds 0) := by
  set s : ℝ := (3 + Work.Spaces.eta) / 2 with hsdef
  have hs : 0 < s := by
    rw [hsdef]; have := Work.Spaces.eta_pos; linarith
  have hs1 : 0 < s - 1 := by
    rw [hsdef]; have := Work.Spaces.eta_pos; linarith
  have hfun : (fun n : ℕ =>
        A * (1 + 1 / delta n) * (2 * C * (2 * delta n) ^ s * M))
      = fun n : ℕ => (A * 2 * C * M * 2 ^ s) * ((delta n) ^ s + (delta n) ^ (s - 1)) := by
    funext n
    have hδ : 0 < delta n := by rw [delta]; positivity
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
    have hsplit : (1 + 1 / delta n) * (delta n) ^ s
        = (delta n) ^ s + (delta n) ^ (s - 1) := by
      rw [add_mul, one_mul, one_div, ← Real.rpow_neg_one (delta n), mul_comm,
        ← Real.rpow_add hδ]
      rw [show s + (-1 : ℝ) = s - 1 from by ring]
    calc A * (1 + 1 / delta n) * (2 * C * (2 ^ s * (delta n) ^ s) * M)
        = (A * 2 * C * M * 2 ^ s) * ((1 + 1 / delta n) * (delta n) ^ s) := by ring
      _ = (A * 2 * C * M * 2 ^ s) * ((delta n) ^ s + (delta n) ^ (s - 1)) := by
            rw [hsplit]
  rw [hfun]
  have h1 : Tendsto (fun n : ℕ => (delta n) ^ s + (delta n) ^ (s - 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_delta_rpow hs).add (tendsto_delta_rpow hs1)
    simpa using h
  simpa using h1.const_mul (A * 2 * C * M * 2 ^ s)

end Work.FTS.StrongEps.EComparison
