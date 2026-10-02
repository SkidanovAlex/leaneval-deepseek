import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Series.summable_bottcherTerm
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction2.exists_analytic_log_normFactor_of_mem_mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.LogLift

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **Normalisation of a continuous logarithm of the Böttcher factor `p_c(z)/z^4`.**

On the escape set `EscapeSet c = {G_c > 0}` any continuous logarithm `L` of the normalised
Böttcher factor `p_c(z)/z^4` (which is `1 + O(1/z²)` at infinity) can be shifted by a constant
`2πi k` so as to vanish at infinity.  Indeed a continuous logarithm of a holomorphic non-vanishing
function is holomorphic (`Work.Escape.continuousOn_exp_eq_differentiableOn`, packaged as
`Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq`), and for such a logarithm the standard
normalisation at infinity is available
(`Work.Bottcher.Contraction2.exists_normalized_log`); the resulting `L'` is holomorphic, hence in
particular continuous, on the escape set. -/
theorem exists_tendsto_zero_log_of_continuous_log (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    {L : ℂ → ℂ} (hLc : ContinuousOn L (Work.Bottcher.EscapeSet c))
    (hLexp : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4) :
    ∃ L' : ℂ → ℂ, ContinuousOn L' (Work.Bottcher.EscapeSet c) ∧
      (∀ z : ℂ, 0 < Work.Bottcher.green c z →
        Complex.exp (L' z) = Work.Bottcher.pMap c z / z ^ 4) ∧
      Filter.Tendsto L' (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  -- A continuous logarithm of a non-vanishing holomorphic function is holomorphic.
  have hLan : AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c) :=
    Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq c hc hLc hLexp
  -- Standard normalisation of such a (holomorphic) logarithm at infinity.
  obtain ⟨L', hL'an, hL'exp, hL't⟩ :=
    Work.Bottcher.Contraction2.exists_normalized_log hc hLan hLexp
  exact ⟨L', hL'an.continuousOn, hL'exp, hL't⟩

end Work.Bottcher.LogLift
