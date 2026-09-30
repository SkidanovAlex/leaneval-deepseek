import Mathlib
import Submission.Work.Morse.flow_basic
import Submission.Work.Morse.flow_box
import Submission.Work.Morse.flow_box_uniform
import Submission.Work.Morse.flow_group_law
import Submission.Work.Morse.flow_continuous_strip
import Submission.Work.Morse.flow_continuous_global

set_option synthInstance.maxHeartbeats 400000

/-!
# The flow of a smooth vector field on a compact smooth manifold

On a compact smooth manifold `M` without boundary, the flow of a smooth vector field `v` exists for
all time and is jointly continuous in the time and the initial point. The proof assembles

* `Work.Morse.flow_box_local` — a local flow box at every point (Picard–Lindelöf in charts, with the
  coordinate solution staying inside the chart target),
* `Work.Morse.flow_box_uniform` — compactness makes the existence time uniform over `M`,
* `Mathlib`'s `exists_isMIntegralCurve_of_isMIntegralCurveOn` — the global flow,
* `Work.Morse.flow_group_law` — uniqueness of integral curves gives the one-parameter group law,
* `Work.Morse.flow_continuous_strip` — the global flow agrees with the local flow boxes on the strip
  `|t| < ε`, hence is continuous there,
* `Work.Morse.flow_continuous_global` — the strip together with the group law gives joint continuity.
-/

namespace Work.Morse

open scoped Manifold ContDiff Topology

namespace Work.Morse

/-- The flow of a smooth vector field on a compact smooth manifold without boundary exists for all
time and is jointly continuous. -/
theorem continuous_flow {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M]
    (v : (x : M) → TangentSpace (𝓡 n) x)
    (hv : ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M))) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      Continuous (Function.uncurry Φ) := by
  have hv1 : ContMDiff (𝓡 n) (𝓡 n).tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M)) :=
    ContMDiff.of_le hv (by norm_num)
  have hbox := flow_box_local (n := n) v hv
  obtain ⟨ε, hε, hunif, hboxes⟩ := flow_box_uniform (n := n) hbox
  have hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := fun x ↦
    exists_isMIntegralCurve_of_isMIntegralCurveOn hv1 hε hunif x
  let Φ : ℝ → M → M := fun t x ↦ (Classical.choose (hex x)) t
  have h0 : ∀ x, Φ 0 x = x := fun x ↦ (Classical.choose_spec (hex x)).1
  have hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v := fun x ↦ (Classical.choose_spec (hex x)).2
  have hgroup : ∀ s t x, Φ (s + t) x = Φ s (Φ t x) := flow_group_law (n := n) hv1 h0 hΦ
  exact ⟨Φ, h0, hΦ, hgroup,
    flow_continuous_global (n := n) hε hgroup (flow_continuous_strip (n := n) hv1 hε hboxes h0 hΦ)⟩

end Work.Morse

/-- The same statement, directly under the name `Work.Morse.continuous_flow` (the declaration above
sits in a doubly nested `Work.Morse` namespace, as in the original problem file). -/
theorem continuous_flow {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M]
    (v : (x : M) → TangentSpace (𝓡 n) x)
    (hv : ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M))) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      Continuous (Function.uncurry Φ) :=
  _root_.Work.Morse.Work.Morse.continuous_flow v hv

end Work.Morse
