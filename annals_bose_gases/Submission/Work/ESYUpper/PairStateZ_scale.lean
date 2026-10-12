import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ESYUpper.PairState_scale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ESYUpper

/-- The squared `L²(abox)` norm of the pair-excited state is homogeneous of
degree `2N` in the condensate orbital `ψ`: replacing `ψ` by `s · ψ` multiplies
`pairStateZ` by `s ^ (2 * N)`.

Indeed `pairState N (s·ψ) wt G x = s^N · pairState N ψ wt G x`
(`PairState_scale`), so the pointwise square picks up `s^(2N)`, and this
constant factors out of the box integral. -/
theorem PairStateZ_scale (N : ℕ) (ℓ s : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (wt : ℕ → ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.SecondOrder.pairStateZ N ℓ (fun y => s * ψ y) wt G
      = s ^ (2 * N) * Work.SecondOrder.pairStateZ N ℓ ψ wt G := by
  simp only [Work.SecondOrder.pairStateZ]
  rw [show (fun x => (Work.SecondOrder.pairState N (fun y => s * ψ y) wt G x) ^ 2)
      = fun x => s ^ (2 * N) * (Work.SecondOrder.pairState N ψ wt G x) ^ 2 from by
        funext x
        rw [PairState_scale N s ψ wt G x, mul_pow, ← pow_mul, Nat.mul_comm N 2]]
  rw [MeasureTheory.integral_const_mul]

end Work.ESYUpper
