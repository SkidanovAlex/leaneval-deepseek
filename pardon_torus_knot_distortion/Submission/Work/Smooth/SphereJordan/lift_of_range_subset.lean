import Mathlib
import Submission.Work.Smooth.Jordan.Defs

namespace Work.Smooth.SphereJordan

/-- **Lifting a map into the range of an embedded disc.**

If `e : 𝔻 → ℝ³` is a continuous injection and `f : 𝔻 → ℝ³` is a continuous injection whose image
lies in the image of `e`, then `f` factors through `e` by a continuous injection
`g : 𝔻 → 𝔻` in the unique way: `e (g z) = f z` for all `z`.

The point is that `𝔻` is compact and `ℝ³` is Hausdorff, so the continuous injection `e` is a closed
embedding, hence a homeomorphism onto its image; the lift is then `e⁻¹ ∘ f`, a composite of
continuous maps.  Injectivity follows because `f = e ∘ g` is injective. -/
theorem lift_of_range_subset (e : C(Work.Smooth.Jordan.Disc, LeanEval.KnotTheory.PardonDistortion.R3)) (he : Function.Injective e) (f : C(Work.Smooth.Jordan.Disc, LeanEval.KnotTheory.PardonDistortion.R3)) (hf : Function.Injective f) (h : Set.range f ⊆ Set.range e) : ∃ g : C(Work.Smooth.Jordan.Disc, Work.Smooth.Jordan.Disc), Function.Injective g ∧ ∀ z, e (g z) = f z := by
  -- `e` is a closed embedding since its source is compact and its target is Hausdorff.
  have hEmb : Topology.IsEmbedding (e : Work.Smooth.Jordan.Disc → LeanEval.KnotTheory.PardonDistortion.R3) :=
    (e.continuous.isClosedEmbedding he).toIsEmbedding
  -- the homeomorphism `𝔻 ≃ₜ range e` induced by `e`.
  let eH : Work.Smooth.Jordan.Disc ≃ₜ
      Set.range (e : Work.Smooth.Jordan.Disc → LeanEval.KnotTheory.PardonDistortion.R3) :=
    hEmb.toHomeomorph
  -- the lift, as an explicit function.
  let gf : Work.Smooth.Jordan.Disc → Work.Smooth.Jordan.Disc :=
    fun z => eH.symm ⟨f z, h (Set.mem_range_self z)⟩
  have hcont : Continuous gf :=
    eH.symm.continuous.comp (Continuous.subtype_mk f.continuous _)
  -- the defining property of the lift.
  have hkey : ∀ z, e (gf z) = f z := by
    intro z
    have h1 : eH (gf z) = ⟨f z, h (Set.mem_range_self z)⟩ := eH.apply_symm_apply _
    have h2 : ((eH (gf z) :
        Set.range (e : Work.Smooth.Jordan.Disc → LeanEval.KnotTheory.PardonDistortion.R3)) :
          LeanEval.KnotTheory.PardonDistortion.R3) = e (gf z) :=
      Topology.IsEmbedding.toHomeomorph_apply_coe hEmb (gf z)
    rw [h1] at h2
    exact h2.symm
  refine ⟨⟨gf, hcont⟩, ?_, hkey⟩
  intro z w hzw
  have hzw' : gf z = gf w := hzw
  apply hf
  rw [← hkey z, ← hkey w, hzw']

end Work.Smooth.SphereJordan
