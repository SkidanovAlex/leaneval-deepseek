import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

theorem L12DzIterTendsto {C0 : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hC0 : 0 ≤ C0)
    (hF : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (F n)) Work.FTS.EllipticEst.Q0)
    (hG : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ (n : ℕ) (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (F n) z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hconv : ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a G z θ))) :
    ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        Filter.atTop (nhds (Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0)) :=
  -- REPOINTED: the same statement is proved sorry-free in `RXT.Slots`
  -- (`RXT/Slots/v2_L12DzIterTendsto.lean`), which is the twin this stub was carved from.
  Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto hC0 hF hG hbnd hconv

end Work.FTS_RegExport.RXT
