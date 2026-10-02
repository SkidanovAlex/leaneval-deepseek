import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.liftChange_mul
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_segment
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_eq_zero
import Submission.Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero
import Submission.Work.Bottcher.Contraction.exists_continuous_log_of_monodromy
import Submission.Work.Bottcher.Contraction.isPreconnected_green_eq_zero_of_mem_mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Holomorphic logarithms of the normalised Böttcher factor on the tricorn escape set

For `c` in the mandelbar `M*` the normalised Böttcher factor `η_c(z) = p_c z / z^4`
(`p_c = T_c ∘ T_c`, the monic quartic `pMap c`) admits a holomorphic logarithm `L` on the escape
set `{G_c > 0}`, vanishing at infinity.

The proof constructs `L` as the lift of `η_c` through the exponential covering `ℂ → ℂ*`.  The
crucial point is that `η_c` has trivial monodromy on the escape set: writing `η_c` as the product
`∏_j (· - r_j)/(·)^4` over the four roots `r_j` of `p_c`, the monodromy along a closed curve is
`2πi·(Σ_j wind(γ,r_j) - 4 wind(γ,0))`, and all the windings agree because `0` and the four roots
`r_j` lie in the (connected, for `c ∈ M*`) filled Julia set `{G_c = 0}`, which is disjoint from
the curve.  The lift exists by the lifting criterion for the covering `ℂ → ℂ*`, and it is
automatically holomorphic because a continuous logarithm of a holomorphic nowhere-vanishing
function is holomorphic.
-/

open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- **A holomorphic logarithm of the normalised Böttcher factor on the escape set**, for a
parameter of the mandelbar.  It vanishes at infinity. -/
theorem exists_analytic_log_normFactor_of_mem_mandelbar (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c) ∧
        (∀ z : ℂ, 0 < Work.Bottcher.green c z →
          Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4) ∧
        Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  -- the filled Julia set is connected for a mandelbar parameter
  have hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z = 0} :=
    isPreconnected_green_eq_zero_of_mem_mandelbar c hc
  -- hence the normalised factor has trivial monodromy on the escape set
  have hmono : ∀ (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
      (hγ : ∀ t, 0 < Work.Bottcher.green c (γ t)) (hγne : ∀ t, γ t ≠ 0)
      (h : ∀ t, Work.Bottcher.Contraction.normFactorPath c γ hγne t ≠ 0),
      Work.Bottcher.Contraction.liftChange
        (Work.Bottcher.Contraction.normFactorPath c γ hγne) h = 0 :=
    fun γ hloop hγ hγne h =>
      liftChange_normFactorPath_eq_zero c hc hK γ hloop hγ hγne h
  -- so the exponential lift exists and is continuous
  obtain ⟨L, hcont, hexp, htend⟩ := exists_continuous_log_of_monodromy c hc hmono
  -- and it is automatically holomorphic
  exact ⟨L, analyticOnNhd_log_of_exp_eq c hc hcont hexp, hexp, htend⟩

end

end Work.Bottcher.Contraction
