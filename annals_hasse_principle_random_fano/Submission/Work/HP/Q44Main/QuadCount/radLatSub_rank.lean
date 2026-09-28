import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.numaux.rk_orthLat
import Submission.Work.HP.numaux.rk_orthLatDefs

namespace Work.HP.Q44Main.QuadCount

/-- The rank of the integral points of the radical equals the `ℚ`-dimension of the radical.

`radLatSub Q` is the `ℤ`-lattice `{v ∈ ℤ^5 : castL v ∈ radSub Q}`.  Its `ℚ`-span (`spread`)
is `radSub Q`, because every rational vector of `radSub Q` has a nonzero integer multiple that
is integer valued, and `spread` preserves the rank. -/
theorem radLatSub_rank (Q : MvPolynomial (Fin 5) ℚ) :
    Work.HP.rk (Work.HP.MDEstimates.radLatSub Q)
      = Module.finrank ℚ (Work.HP.MDEstimates.radSub Q) := by
  have hc : Work.Q44Geom.toRatLM = Work.HP.numaux.castL (ι := Fin 5) := by
    ext v i; rfl
  -- The ℚ-span of the integral radical points is the whole radical.
  have hspread : Work.HP.numaux.spread (Work.HP.MDEstimates.radLatSub Q)
      = Work.HP.MDEstimates.radSub Q := by
    unfold Work.HP.numaux.spread
    rw [Work.HP.MDEstimates.radLatSub, hc, Submodule.map_comap_eq]
    rw [inf_comm]
    exact Work.HP.numaux.span_restrictScalars_inf _ _ Work.HP.numaux.castL_denom
  unfold Work.HP.rk
  rw [← Work.HP.numaux.spread_finrank (Work.HP.MDEstimates.radLatSub Q), hspread]

end Work.HP.Q44Main.QuadCount
