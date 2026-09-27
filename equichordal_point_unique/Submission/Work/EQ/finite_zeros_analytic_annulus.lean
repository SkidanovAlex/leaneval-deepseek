import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs

namespace Work.EQ

open Complex Filter _root_.Topology

open scoped Topology

/-- The closed annulus `Ann r₁ r₂` is compact: it is a closed subset of the compact closed
ball of radius `r₂` about `0`. -/
theorem isCompact_ann (r₁ r₂ : ℝ) : IsCompact (Ann r₁ r₂) := by
  have hcl : IsClosed (Ann r₁ r₂) := by
    rw [show Ann r₁ r₂ = {z : ℂ | r₁ ≤ ‖z‖} ∩ Metric.closedBall 0 r₂ from by
      ext z; simp [Ann, Metric.mem_closedBall, dist_eq_norm]]
    exact (isClosed_Ici.preimage continuous_norm).inter Metric.isClosed_closedBall
  exact (isCompact_closedBall (0 : ℂ) r₂).of_isClosed_subset hcl (by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.2)

/-- **Finiteness of the zeros of a nontrivial analytic function on a closed annulus.**
If `f` is analytic on an open preconnected set `U` containing the closed annulus `Ann r₁ r₂`
and `f` is not identically zero on `U`, then `f` has only finitely many zeros in `Ann r₁ r₂`.

The annulus is compact, so an infinite zero set inside it would have an accumulation point
`x ∈ Ann r₁ r₂ ⊆ U`; by the principle of isolated zeros (identity theorem), `f` would then
vanish identically on the preconnected set `U`, contradicting the hypothesis. -/
theorem finite_zeros_analytic_annulus {f : ℂ → ℂ} {U : Set ℂ} {r₁ r₂ : ℝ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hAnn : Ann r₁ r₂ ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hne : ∃ u ∈ U, f u ≠ 0) :
    {z : ℂ | z ∈ Ann r₁ r₂ ∧ f z = 0}.Finite := by
  by_contra hfin
  rw [Set.not_finite] at hfin
  obtain ⟨x, hxAnn, hxacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hfin (isCompact_ann r₁ r₂)
      (fun _ hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = 0 :=
    ((accPt_iff_frequently_nhdsNE).mp hxacc).mono fun _ hz => hz.2
  obtain ⟨u, hu, hfu⟩ := hne
  exact hfu ((hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc (hAnn hxAnn) hfreq) hu)

end Work.EQ
