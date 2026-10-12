import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SecondOrder.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SecondOrder.State

open scoped BigOperators

/-- Continuity of the pair amplitude: a finite sum over partial matchings of
products of the pairing kernel; each kernel entry `x ↦ G (x i) (x j)` is
continuous by `hG`, and finite products/sums of continuous functions are
continuous. -/
theorem continuous_pairAmp {N : ℕ} (wt : ℕ → ℝ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2) :
    Continuous (Work.SecondOrder.pairAmp N wt G) := by
  unfold Work.SecondOrder.pairAmp
  refine continuous_finsetSum (Work.SecondOrder.pmatch N) (fun p _ => ?_)
  refine Continuous.const_mul ?_ (wt (Work.SecondOrder.nPair p))
  refine continuous_finsetProd (Work.SecondOrder.pairRep p) (fun i _ => ?_)
  exact hG.comp (Continuous.prodMk (continuous_apply i) (continuous_apply (p i)))

theorem continuous_pairState {N : ℕ} {psi : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hpsi : Continuous psi) (wt : ℕ → ℝ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2) :
    Continuous (Work.SecondOrder.pairState N psi wt G) := by
  unfold Work.SecondOrder.pairState
  refine Continuous.mul ?_ (continuous_pairAmp wt hG)
  exact continuous_finsetProd Finset.univ (fun i _ => hpsi.comp (continuous_apply i))

end Work.SecondOrder.State
