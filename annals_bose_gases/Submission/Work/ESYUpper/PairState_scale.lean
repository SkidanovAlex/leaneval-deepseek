import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ESYUpper.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ESYUpper

/-- The pair-excited state `Work.SecondOrder.pairState` is homogeneous of degree
`N` in the condensate orbital `ψ`: replacing `ψ` by `s · ψ` multiplies the
state by `s ^ N`.  Indeed `pairState` is the product of the one-particle
factors `∏ i, ψ (x i)` with the pairing amplitude `pairAmp`, which does not
depend on `ψ` at all. -/
theorem PairState_scale (N : ℕ) (s : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (wt : ℕ → ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (x : Submission.BoseGases.X N) :
    Work.SecondOrder.pairState N (fun y => s * ψ y) wt G x
      = s ^ N * Work.SecondOrder.pairState N ψ wt G x := by
  simp only [Work.SecondOrder.pairState]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end Work.ESYUpper
