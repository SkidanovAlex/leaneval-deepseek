import Mathlib
import Submission.Work.EMFG.killChain
import Submission.Work.Serre.serrePostnikovTower

namespace Work.EMFG

/-- **The composite inclusion `Y → killChain Y k` is a `π₀`- and `π₁`-bijection.**

Since `killChainIncl Y j` is `Work.Serre.killIncl (j+1) (killChain Y j)`, the one-step analysis of
the tower (`Work.Serre.killCells_step`) shows that it induces a bijection on `π_i` for every
`i ≤ j+1`, in particular on `π_0` and `π_1`.  The claim follows by induction on `k`, using the
functoriality of `piMapN` (`Work.Serre.piMapN_comp`) to read the composite as a composition of the
bijections at each step. -/
theorem killChainUp_pi_bijective {Y : Type} [TopologicalSpace Y] (k : ℕ) :
    ∀ (i : ℕ), i ≤ 1 → ∀ y : Y,
      Function.Bijective (Work.Serre.piMapN (Work.EMFG.killChainUp Y k) i y) := by
  induction k with
  | zero =>
    intro i _hi y
    have h : Work.Serre.piMapN (killChainUp Y 0) i y = id := by
      funext a
      exact Work.Serre.piMapN_id i y a
    rw [h]
    exact Function.bijective_id
  | succ k ih =>
    intro i hi y
    have hcomp : Work.Serre.piMapN (killChainUp Y (k + 1)) i y
        = (Work.Serre.piMapN (killChainIncl Y k) i (killChainUp Y k y))
            ∘ (Work.Serre.piMapN (killChainUp Y k) i y) := by
      funext a
      exact Work.Serre.piMapN_comp (killChainUp Y k) (killChainIncl Y k) i y a
    rw [hcomp]
    have hstep : Function.Bijective
        (Work.Serre.piMapN (killChainIncl Y k) i (killChainUp Y k y)) :=
      (Work.Serre.killCells_step (k + 1) (killChain Y k)).1 i (by omega)
        (killChainUp Y k y)
    exact hstep.comp (ih i hi y)

end Work.EMFG
