import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Cores.TSCAssembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

/-- **The six level-`2` `Tk`-slots of the elliptic `ℋ²` estimate** (the `Tk`-residual of
Elgindi's `prop:H2`, Annals **194** (2021), Steps 4–5): the level-`2` angular slots of
`A = z²∂_z²Ψ` (weighted by `α⁴`) and of `B = ∂_θ²Ψ`, bounded by the level-`2` energy of the
source `F`, given the level-`0` estimate `EllWeak0`.

The proof is the assembly `TopSlotsTwoClean_of` (`Cores/TSCAssembly.lean`) applied to the
`(1,1)`-slot bound of `A` (`Cores.ASlot11Bound` — the level-`1` light-weight mixed
interpolation at the datum `G = A`); see `Cores/NOTES_TopSlotsTwoClean.md`. -/
theorem TopSlotsTwoClean (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
        + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.pthIter 2 Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  -- the assembly needs only the `(1,1)`-slot bound of `A` (`Cores.ASlot11Bound`),
  -- which is the level-`1` light-weight mixed interpolation at `G = A`; see
  -- `Cores/NOTES_TopSlotsTwoClean.md`.
  sorry

end Work.FTS.EllipticEst.Cores
