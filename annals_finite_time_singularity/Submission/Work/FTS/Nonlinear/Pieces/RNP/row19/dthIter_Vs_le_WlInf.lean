import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

theorem dthIter_Vs_le_WlInf {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) z θ|
        ≤ Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  -- `Vs α Φs` is by definition `Vop (PhiTil α F_* Φs)`, whose `𝒲^{4,∞}`-membership is the
  -- field `StarPkg.V`.  For `i ≥ 1` the angular derivative `D_θ^i` occupies exactly the mixed
  -- slot `(j, k) = (i, 0)` of the `𝒲^{4,∞}`-norm, and the slot bound
  -- `Spaces.pz_Dth_sup_bound` is precisely the stated inequality (with `(z+1)^0 = 1`).
  intro i hi hi4 z hz θ hθ
  have hmem : Work.Spaces.WlInfMem α 4 (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) := by
    simpa only [Work.FTS.Nonlinear.Pieces.RNP.Vs, Work.FTS.Nonlin.PhiTs] using hs.V.1
  have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) hmem
    i 0 hi (by omega) z θ hz hθ
  simpa using h

end Work.FTS.Nonlinear.Pieces.RNP.row19
