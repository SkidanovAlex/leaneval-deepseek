import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

open MeasureTheory

/-- The function `v ↦ v^{it} / log v` is interval-integrable on `[N,M]` for `1 < N ≤ M`.

Route: on `[N,M]` one has `v > 1 > 0`, so `v` lies in the slit plane where `Complex.cpow` is
continuous (`ContinuousOn.cpow`) and `Real.log v ≠ 0`, hence `z ↦ (z : ℂ) ^ (I*t)` and
`v ↦ ((Real.log v : ℝ) : ℂ)` are continuous there and so is their quotient
(`ContinuousOn.div`). A function continuous on the compact interval `uIcc N M` is
interval-integrable (`ContinuousOn.intervalIntegrable`). -/
theorem intervalIntegrable_cpow_div_log (t N M : ℝ) (hN : 1 < N) (hNM : N ≤ M) :
    IntervalIntegrable (fun v : ℝ => (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ))
      MeasureTheory.volume N M := by
  refine ContinuousOn.intervalIntegrable ?_
  have hmem : ∀ v ∈ Set.uIcc N M, 1 < v := by
    intro v hv
    rw [Set.uIcc_of_le hNM] at hv
    linarith [hv.1]
  have hpow : ContinuousOn (fun v : ℝ => (v : ℂ) ^ (Complex.I * t)) (Set.uIcc N M) :=
    ContinuousOn.cpow (Complex.continuous_ofReal.continuousOn)
      continuousOn_const
      (fun v hv => by rw [Complex.ofReal_mem_slitPlane]; linarith [hmem v hv])
  have hlog : ContinuousOn (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) (Set.uIcc N M) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono (fun v hv => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (by linarith [hmem v hv])))
  refine hpow.div hlog (fun v hv => ?_)
  exact_mod_cast ne_of_gt (Real.log_pos (hmem v hv))

end Work.BMF.pcsw
