import Mathlib
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux

namespace Work.EQ

noncomputable section

/-- **The germ rotational stabiliser condition** for the `F3` branch `σ`.

`GermInv a c u₀ R σ τ` says that the rotation `τ` preserves the *germ* of the branch
`t ↦ branchPt a c u₀ R σ t` at `0`: there is a radius `δ > 0`, not exceeding the branch radius
`rhoFin' a c u₀ R N`, such that

`branchPt a c u₀ R σ (τ * t) = branchPt a c u₀ R σ t` for all `0 < ‖t‖ < δ`.

This is exactly the hypothesis appearing in the last conjunct of
`Work.EQ.branchPt_germ_stabiliser`. -/
def GermInv (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) {N : ℕ} (σ : Fin N → Bool)
    (τ : ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ rhoFin' a c u₀ R N ∧
    ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → branchPt a c u₀ R σ (τ * t) = branchPt a c u₀ R σ t

/-- The trivial rotation `1` always preserves the germ, on the full branch radius
`rhoFin' a c u₀ R N`. -/
lemma germInv_one {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) : GermInv a c u₀ R σ 1 :=
  ⟨rhoFin' a c u₀ R N, rhoFin'_pos hR hc, le_rfl, fun t _ _ => by rw [one_mul]⟩

end

end Work.EQ
