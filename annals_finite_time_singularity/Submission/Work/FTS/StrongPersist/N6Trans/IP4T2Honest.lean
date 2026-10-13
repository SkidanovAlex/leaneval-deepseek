import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.ClauseHon
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TopSlotHon
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

/-- **The level-four `T2` transport clause for `IP4` in the honest class** (the open-quadrant
`SmoothOpen` class with `ℋ⁴`/`ℋ⁵`-honesty, replacing the frozen `RegQ α 4 g` bundle).

Proved by the honest per-slot engine (`Hon.SlotAbsHon`, itself built from the honest radial
integration by parts `Hon.TopSlotHon` and the honest delicate bound `Hon.DelicateHon`) together
with the slot domination `IPGen.ip4SlotDomGen` of the concrete coercive `IP4`. -/
theorem IP4T2Honest : ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
        Work.FTS.VocabO.CoefThMem 1 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      |Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α
          (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 4 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  exact Work.FTS.StrongPersist.N6Trans.Hon.IP4T2Honest_of_pieces
    Work.FTS.StrongPersist.N6Trans.Hon.TopSlotHon
    Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon

end Work.FTS.StrongPersist.N6Trans
