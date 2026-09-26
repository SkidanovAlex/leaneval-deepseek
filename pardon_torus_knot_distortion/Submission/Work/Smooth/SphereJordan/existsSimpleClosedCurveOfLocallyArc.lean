import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.LocallyArcInPlane
import Submission.Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle

namespace Work.Smooth.SphereJordan

open Set Function

open scoped Topology

/-- **A nonempty compact preconnected nontrivial locally-arc subset of the plane admits a
`2π`-periodic injective parametrisation.** -/
theorem existsSimpleClosedCurveOfLocallyArc {L : Set ℂ} (hLc : IsCompact L)
    (hLpre : IsPreconnected L) (hnt : L.Nontrivial)
    (hloc : ∀ x ∈ L, ∃ (ε : ℝ) (γ : ℝ → ℂ), 0 < ε ∧ Continuous γ ∧ Function.Injective γ ∧
      γ 0 = x ∧ γ '' Set.Ioo (-1) 1 = L ∩ Metric.ball x ε) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = L := by
  haveI : CompactSpace ↥L := isCompact_iff_compactSpace.mp hLc
  haveI : PreconnectedSpace ↥L := Subtype.preconnectedSpace hLpre
  haveI : Nonempty ↥L := ⟨⟨hnt.nonempty.choose, hnt.nonempty.choose_spec⟩⟩
  have hH : Work.Smooth.SphereJordan.IsLocallyArc ↥L :=
    LocalArc.isLocallyArc_of_locallyArcInPlane hloc
  obtain ⟨γL, hcont, hper, hinj, hrange⟩ :=
    LocalArc.compactPreconnectedLocallyArc_isCircle (X := ↥L) hH
  refine ⟨fun t => (γL t : ℂ), continuous_subtype_val.comp hcont, fun t => ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (hper t)
  · intro t ht s hs hts
    exact hinj ht hs (Subtype.ext hts)
  · rw [show (fun t : ℝ => (γL t : ℂ)) = (fun y : ↥L => (y : ℂ)) ∘ γL from rfl,
      Set.range_comp, hrange,
      show (fun y : ↥L => (y : ℂ)) = ((↑) : ↥L → ℂ) from rfl,
      Subtype.coe_image_univ L]

end Work.Smooth.SphereJordan
