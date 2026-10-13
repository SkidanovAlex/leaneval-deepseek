import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open MeasureTheory Set

/-- The `bkm` integral is the interval integral of the `L∞`-norm of the vorticity. -/
theorem bkm_eq_intervalIntegral_vortLInf (u : Work.LWP.R3 → ℝ → Work.LWP.R3) (t : ℝ) :
    Work.LWP.bkm u t = ∫ s in 0..t, Work.LWP.vortLInf u s := rfl

/-- **BKM growth control.**  If the `L∞`-norm of the vorticity is bounded by `K` on `[0,T)`,
then the Beale--Kato--Majda quantity at any time `t ∈ [0,T)` is at most `K * T`. -/
theorem bkm_le_of_vortLInf_bound
    {u : Work.LWP.R3 → ℝ → Work.LWP.R3} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hint : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) MeasureTheory.volume 0 t)
    (hbd : ∀ s ∈ Set.Ico 0 T, Work.LWP.vortLInf u s ≤ K) :
    ∀ t ∈ Set.Ico 0 T, Work.LWP.bkm u t ≤ K * T := by
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  rw [bkm_eq_intervalIntegral_vortLInf]
  calc ∫ s in 0..t, Work.LWP.vortLInf u s
      ≤ ∫ s in 0..t, K := by
        refine intervalIntegral.integral_mono_on ht0 (hint t ⟨ht0, htT⟩)
          intervalIntegrable_const ?_
        intro x hx
        exact hbd x ⟨hx.1, lt_of_le_of_lt hx.2 htT⟩
    _ = K * t := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
    _ ≤ K * T := mul_le_mul_of_nonneg_left (le_of_lt htT) hK

end Work.ConstructionInstance
