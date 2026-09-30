import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.uPerim_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The perimeter parameter `u p = uPerim (bnd p)` of a point with `0 < nrm p` lies in `[0,1)`: the
radial projection `bnd p` has sup norm `1` (`nrm_bnd`), and `uPerim` maps such points into `[0,1)`
(`uPerim_mem`). -/
theorem u_mem_of_nrm_pos {p : E2} (h0 : 0 < nrm p) : 0 ≤ u p ∧ u p < 1 := by
  have hpne : p ≠ 0 := by rintro rfl; simp [nrm] at h0
  rw [u]
  exact uPerim_mem (nrm_bnd hpne)

/-- `uS 0 p = u p` for `0 < nrm p`: the `c`-shift of the perimeter lift is trivial at `c = 0`
because `u p ∈ [0,1)`, so its fractional part is itself. -/
theorem uS_zero' {p : E2} (h0 : 0 < nrm p) : uS 0 p = u p := by
  have hfract : Int.fract (u p) = u p := Int.fract_eq_self.mpr (u_mem_of_nrm_pos h0)
  simp only [uS, zero_add, sub_zero]
  exact hfract

theorem ThetaPolarS_zero (v : Fin 5) (p y : E2) (h0 : 0 < nrm p) :
    ThetaPolarS v 0 p y = ThetaPolar v p y := by
  have hS : uS 0 p = u p := uS_zero' h0
  simp only [ThetaPolarS, ThetaPolar, thetaAng, hS, mul_div_assoc]

end Work.Cusp
