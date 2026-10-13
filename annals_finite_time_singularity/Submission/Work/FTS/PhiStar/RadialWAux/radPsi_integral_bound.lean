/-
# `radPsi_integral_bound` — the crude integral bound for the outer piece `Ψ`

For `c` a function on `(0,∞)` whose first `22` iterated derivatives are bounded by `K`,

  `radPsi α m c z = ∫_{u > 1} c (z u) u^{-p-1} du`,   `p = radP α m`,

and for every `k ≤ 22` with `k < p` the `k`-th derivative of `Ψ` at `z > 0` is

  `∫_{u > 1} c^{(k)}(z u) u^{k - p - 1} du`      (`radPsi_iteratedDeriv`).

Since `k - p - 1 < -1` the weight `u^{k-p-1}` is integrable on `(Ioi 1)` with
`∫_{u>1} u^{k-p-1} du = 1/(p - k)`, and `|c^{(k)}| ≤ K`, so the integral is bounded by
`K/(p - k)`.

The proof does not need any regularity of `c` beyond the pointwise bound: the
dominating function `K u^{k-p-1}` is integrable, so
`norm_integral_le_of_norm_le` applies a.e. on `(Ioi 1)`.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.RadialWAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

theorem radPsi_integral_bound {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 22 → (k : ℝ) < Work.FTS.PhiStar.RadialWAux.radP α m →
      ∀ z : ℝ, 0 < z →
        |∫ u in Set.Ioi 1,
            iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) - Work.FTS.PhiStar.RadialWAux.radP α m - 1)|
          ≤ K / (Work.FTS.PhiStar.RadialWAux.radP α m - (k : ℝ)) := by
  intro k hk hkp z hz
  have hlt : (k : ℝ) - radP α m - 1 < -1 := by linarith
  -- the dominating function is integrable on `(Ioi 1)`
  have hKint : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) - radP α m - 1))
      (volume.restrict (Set.Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K
  -- the pointwise bound, a.e. on `(Ioi 1)`
  have hbnd : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ‖iteratedDeriv k c (z * u) * u ^ ((k : ℝ) - radP α m - 1)‖
        ≤ K * u ^ ((k : ℝ) - radP α m - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hrpow : 0 ≤ u ^ ((k : ℝ) - radP α m - 1) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow]
    exact mul_le_mul_of_nonneg_right (hb k hk (z * u) (mul_pos hz hu0)) hrpow
  -- the value of the model integral `∫_{u>1} u^{k-p-1} du = 1/(p-k)`
  have hInt : ∫ u in Set.Ioi 1, u ^ ((k : ℝ) - radP α m - 1)
      = 1 / (radP α m - (k : ℝ)) := by
    rw [integral_Ioi_rpow_of_lt (a := (k : ℝ) - radP α m - 1) hlt (c := 1) zero_lt_one,
      Real.one_rpow]
    have hden : ((k : ℝ) - radP α m - 1) + 1 = (k : ℝ) - radP α m := by ring
    rw [hden, div_eq_div_iff (by linarith : (k : ℝ) - radP α m ≠ 0)
      (by linarith : radP α m - (k : ℝ) ≠ 0)]
    ring
  have hmain : ‖∫ u in Set.Ioi 1,
        iteratedDeriv k c (z * u) * u ^ ((k : ℝ) - radP α m - 1)‖
      ≤ K / (radP α m - (k : ℝ)) := by
    calc ‖∫ u in Set.Ioi 1, iteratedDeriv k c (z * u) * u ^ ((k : ℝ) - radP α m - 1)‖
        ≤ ∫ u in Set.Ioi 1, K * u ^ ((k : ℝ) - radP α m - 1) :=
          norm_integral_le_of_norm_le hKint hbnd
      _ = K * (∫ u in Set.Ioi 1, u ^ ((k : ℝ) - radP α m - 1)) := by
          rw [integral_const_mul]
      _ = K / (radP α m - (k : ℝ)) := by rw [hInt]; ring
  simpa [Real.norm_eq_abs] using hmain

end Work.FTS.PhiStar.RadialWAux
