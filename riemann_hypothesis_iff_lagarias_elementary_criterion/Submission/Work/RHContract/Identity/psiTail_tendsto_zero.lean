import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.Identity

/-- `J(x) → 0` as `x → ∞` (ROUTE_LEAD §1, needed to identify the constant of Lemma I with
`γ`).  Formally this is the general measure-theoretic fact that the tail integral of a fixed
function tends to `0` (with Mathlib's convention that a non-integrable Bochner integral is
`0`); the honest convergence of `∫ (ψ t − t) k(t) dt` follows from
`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real`. -/
theorem psiTail_tendsto_zero :
    Filter.Tendsto Work.RHContract.psiTail Filter.atTop (nhds 0) := by
  unfold Work.RHContract.psiTail
  exact MeasureTheory.tendsto_integral_Ioi_zero (μ := MeasureTheory.volume)
    (f := fun t : ℝ => (Chebyshev.psi t - t) * Work.RHContract.kW t)
    (b := fun i : ℝ => i) Filter.tendsto_id

end Work.RHContract.Identity
