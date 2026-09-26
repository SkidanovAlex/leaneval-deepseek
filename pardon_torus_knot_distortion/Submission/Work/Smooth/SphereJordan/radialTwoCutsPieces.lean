import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint
import Submission.Work.Smooth.SphereJordan.radialTwoCutsPiecesFinal2

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

theorem radialTwoCutsPieces (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (W : Set ℂ) (hWcl : IsClosed W) (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (hWdisc : ∃ e : C(Work.Smooth.SphereJordan.Disc, ℂ),
      Function.Injective e ∧ Set.range e = W)
    (h0 : (0 : ℂ) ∈ W)
    (w₁ w₂ : ℂ) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (hne : w₁ ≠ w₂)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₁' : t₁ < 1) (ht₂ : 0 < t₂) (ht₂' : t₂ < 1)
    (hm₁ : t₁ • w₁ ∈ W) (hm₂ : t₂ • w₂ ∈ W)
    (hf₁ : ∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ∉ W)
    (hf₂ : ∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ∉ W) :
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Metric.ball (0 : ℂ) 1 \
        (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1 ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ Φ : C(Work.Smooth.SphereJordan.Disc, ℂ),
        Function.Injective Φ ∧ Set.range Φ = closure P₁) ∧
      (∃ Ψ : C(Work.Smooth.SphereJordan.Disc, ℂ),
        Function.Injective Ψ ∧ Set.range Ψ = closure P₂) := by
  exact radialTwoCutsPiecesFinal2 h W hWcl hWsub hWdisc h0 w₁ w₂ hw₁ hw₂ hne t₁ t₂ ht₁ ht₁' ht₂ ht₂' hm₁ hm₂ hf₁ hf₂
end

end Work.Smooth.SphereJordan
