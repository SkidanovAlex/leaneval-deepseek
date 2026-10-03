import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.HB.component_homeo_of_covering_vnotin
import Submission.Work.Horn.HB.v_mem_case

/-! Guidance from the project lead (the requester):

LEAD DESIGN (read Submission/Work/Horn/HB/DESIGN.md). Piece HB4: abstract topology, with no dynamics.
Case v ∉ V: the component `W` of `D ∩ g ⁻¹' V` through `x` is a covering of the simply connected `V`,
hence a homeomorphism: proper, injective, onto, and simply connected.  Proved in
`Work.Horn.HB.component_homeo_of_covering_vnotin`.
Case v ∈ V: `W* = W ∖ g ⁻¹' {v} → V ∖ {v}` is a covering of the punctured disc; the deck analysis of
that covering (via `Work.BasinSC.CoverDisc`) shows it has finite degree `d`, the classification of
coverings of `𝔻*` produces a `d`-th root `ψ` of the uniformising coordinate, and Riemann's removable
singularity theorem forces `g ⁻¹' {v} ∩ W` to be a single point.  This is `Work.Horn.HB.v_mem_case`.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology

theorem proper_of_covering_LF {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {r : ℝ}
    (hDo : IsOpen D) (hg : DifferentiableOn ℂ g D) (hr : 0 < r) (hrv : r < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V) (hVsc : SimplyConnectedSpace V)
    (h0V : (0 : ℂ) ∉ V) {x : ℂ} (hxD : x ∈ D) (hxV : g x ∈ V) {W : Set ℂ}
    (hW : W = connectedComponentIn (D ∩ g ⁻¹' V) x) :
    (∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K)) ∧ V ⊆ g '' W ∧
      SimplyConnectedSpace W ∧ (v ∉ V → Set.InjOn g W) ∧
      (v ∈ V → ∃ a ∈ W, g a = v ∧ (∀ b ∈ W, g b = v → b = a) ∧
        (¬ Set.InjOn g W → deriv g a = 0)) := by
  by_cases hvV : v ∈ V
  · obtain ⟨hprop, hsurj, hsc, hv⟩ :=
      v_mem_case (V := V) hDo hg hr hrv hcov hLF hVo hVc hVsc h0V hvV hxD hxV hW
    exact ⟨hprop, hsurj, hsc, fun h => absurd hvV h, fun _ => hv⟩
  · obtain ⟨hinj, hsurj, hprop, hsc⟩ :=
      component_homeo_of_covering_vnotin (V := V) hVo hVc.nonempty hVsc h0V hvV hcov hxD hxV hW
    exact ⟨hprop, hsurj, hsc, fun _ => hinj, fun h => absurd h hvV⟩

end Work.Horn.HB
