import Mathlib
import Submission.NK.ChebotarevGeneral.DensityAux

namespace NK.ChebotarevGeneral

open Filter
open scoped Topology

/-- **The converse of `tendsto_primeIdealZetaSum_div_log`.**

If the partial Dirichlet series over `S`, divided by `log (1/(s-1))`, tends to `δ` as `s → 1⁺`,
then `S` has Dirichlet density `δ`.

Indeed, writing `L s = log (1/(s-1))`, the hypothesis says `Z_S / L → δ` and
`Commons.tendsto_primeIdealZetaSum_div_log` (applied to `S = univ`) says `Z_univ / L → 1`. Hence
`Z_S / Z_univ = (Z_S / L) / (Z_univ / L) → δ / 1 = δ`, which is precisely
`NumberField.Set.HasDirichletDensity S δ`. -/
theorem hasDirichletDensity_of_tendsto_primeIdealZetaSum_div_log {K : Type*} [Field K]
    [NumberField K] {S : Set (NK.Chebotarev.PrimeIdeal K)} {δ : ℝ}
    (h : Filter.Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s /
      Real.log (1 / (s - 1))) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds δ)) :
    NumberField.Set.HasDirichletDensity S δ := by
  rw [NumberField.Set.HasDirichletDensity]
  have hU : NumberField.Set.HasDirichletDensity (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) 1 :=
    hasDirichletDensity_univ K
  have hUL : Filter.Tendsto
      (fun s : ℝ => NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s
        / Real.log (1 / (s - 1))) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 1) :=
    Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log hU
  have hq : Filter.Tendsto
      ((fun s : ℝ => NumberField.Set.primeIdealZetaSum S s / Real.log (1 / (s - 1)))
        / (fun s : ℝ => NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s
          / Real.log (1 / (s - 1))))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (δ / 1)) :=
    h.div hUL one_ne_zero
  rw [div_one] at hq
  refine Tendsto.congr' ?_ hq
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 3 / 2 by norm_num)] with s hs
  have hL : Real.log (1 / (s - 1)) ≠ 0 := by
    have hpos : (0 : ℝ) < s - 1 := by linarith [hs.1]
    have : (1 : ℝ) < 1 / (s - 1) := by
      rw [one_lt_div hpos]; linarith [hs.2]
    exact ne_of_gt (Real.log_pos this)
  simp only [Pi.div_apply]
  field_simp

end NK.ChebotarevGeneral
