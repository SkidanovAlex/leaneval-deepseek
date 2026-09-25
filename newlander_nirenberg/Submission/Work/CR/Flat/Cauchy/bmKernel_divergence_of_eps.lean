import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmLhs_tendsto_eps
import Submission.Work.CR.Flat.Cauchy.bmRhs_tendsto_eps

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

/-- **From the regularised identity to the Bochner–Martinelli formula (the limit `ε → 0⁺`).**
Given the regularised identity `hε` for every `ε > 0` (see
`Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral`) and the integrability of the weight
`x ↦ n/(1+nrmSq x)^{n+1}` (`Work.CR.Flat.Cauchy.integrable_bmWeight`), the regularised identity
passes to the limit `ε → 0⁺` and gives the Bochner–Martinelli formula
`Σ_k ∫ x, bmKernel k x * ∂̄_k g x = bmGamma n * g 0`, where
`bmGamma n = -∫ x, n/(1+nrmSq x)^{n+1}` is the normalising constant.  The pointwise limit
`bmKerEps k ε x → bmKernel k x` is dominated by `|bmKernel k x|` (integrable against `∂̄_k g`,
which is compactly supported), and on the right the substitution `x = ε y` turns the weight into
`n/(1+nrmSq y)^{n+1}`, whose limit against the continuous `g(ε y)` is `g 0` times the total integral. -/
theorem bmKernel_divergence_of_eps {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0)
    (hJ : Integrable (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1)))
    (hε : ∀ ε : ℝ, 0 < ε →
      ∑ k, ∫ x, bmKerEps k ε x * dbarCoord k g x
        = -∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x) :
    ∑ k, ∫ x, bmKernel k x * dbarCoord k g x = bmGamma n * g 0 := by
  -- the left-hand side converges, component by component
  have hL : Filter.Tendsto (fun ε : ℝ => ∑ k, ∫ x, bmKerEps k ε x * dbarCoord k g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ k, ∫ x, bmKernel k x * dbarCoord k g x)) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin n))
      (fun k _ => bmLhs_tendsto_eps hn hg hsupp k)
  -- the right-hand side converges to `bmGamma n * g 0`
  have hRhs : Filter.Tendsto (fun ε : ℝ =>
      -∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (bmGamma n * g 0)) := by
    have h := (bmRhs_tendsto_eps hn hR hg hsupp hJ).neg
    simpa only [bmGamma, neg_mul] using h
  -- the two sides agree for every `ε > 0`
  have heq : (fun ε : ℝ => ∑ k, ∫ x, bmKerEps k ε x * dbarCoord k g x)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε : ℝ =>
        -∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x) := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hεpos
    exact hε ε hεpos
  have hL' : Filter.Tendsto (fun ε : ℝ => ∑ k, ∫ x, bmKerEps k ε x * dbarCoord k g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (bmGamma n * g 0)) :=
    hRhs.congr' heq.symm
  exact tendsto_nhds_unique hL hL'

end Work.CR.Flat.Cauchy
