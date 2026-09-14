import Mathlib
import Submission.Commons.MeasureTheory.Integral.lintegral_sliding_differenceQuotient_le_of_finiteDimensional
import Submission.Commons.Analysis.Calculus.absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient
import Submission.Commons.MeasureTheory.Integral.lintegral_ofReal_sq_deriv_le_liminf_of_ne_top

namespace Commons.MeasureTheory.Integral

open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- **Lower semicontinuity of the Dirichlet energy under uniform convergence.**
Let `F n` be absolutely continuous curves on `[0,τ]` converging uniformly on `[0,τ]` to a
continuous `g`, whose energies `∫⁻ ‖(F n)'‖²` are *uniformly bounded* by `ofReal (M^2)`
(this hypothesis is necessary: without it the statement is false -- the Cantor staircase is a
uniform limit of piecewise linear curves with divergent energies, and is not absolutely
continuous).  Then `g` is absolutely continuous and
`∫⁻_{Ioc 0 τ} ‖g'‖²  ≤  liminf_n ∫⁻_{Ioc 0 τ} ‖F n'‖²`.

The uniform bound `hbd` forces the `liminf` of the energies to be finite, so the result follows
from the finite-`liminf` form
`Commons.MeasureTheory.Integral.lintegral_ofReal_sq_deriv_le_liminf_of_ne_top` (whose proof
runs the announced Fatou/difference-quotient argument): for every `n` the energy is at most
`ofReal (M^2) ≠ ⊤`, hence `liminf ≤ ofReal (M^2) ≠ ⊤`. -/
theorem lintegral_ofReal_sq_deriv_le_liminf {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : ℕ → ℝ → E} {g : ℝ → E} {τ M : ℝ} (hτ : 0 ≤ τ) (hM : 0 ≤ M)
    (hg : ContinuousOn g (Set.Icc 0 τ))
    (hconv : TendstoUniformlyOn F g atTop (Set.Icc 0 τ))
    (hAC : ∀ n, AbsolutelyContinuousOnInterval (F n) 0 τ)
    (hbd : ∀ n, ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2)) :
    AbsolutelyContinuousOnInterval g 0 τ ∧
      ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv g t‖ ^ 2)
        ≤ Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv (F n) t‖ ^ 2))
            atTop := by
  have hle : Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
        ENNReal.ofReal (‖deriv (F n) t‖ ^ 2)) atTop ≤ ENNReal.ofReal (M ^ 2) :=
    Filter.liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hbd))
  exact lintegral_ofReal_sq_deriv_le_liminf_of_ne_top hτ hg hconv hAC
    (ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) hle)

end Commons.MeasureTheory.Integral
