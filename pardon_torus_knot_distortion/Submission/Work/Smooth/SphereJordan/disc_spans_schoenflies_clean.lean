import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.disc_interiors_meet_of_common_boundary

/-!
# `disc_spans_schoenflies_clean`

Let `γ : ℝ → ℂ` be a simple closed plane curve whose trace lies in the *open* unit disc, let
`S : PlaneSchoenflies γ` be a planar Schoenflies datum for it (so `S.V` is the bounded side and
`S.e : 𝔻 → ℂ` an embedded spanning disc with image `closure S.V`), and let `F : C(𝔻, 𝔻)` be a
continuous injection whose boundary circle is mapped to the curve (`F (e^{iθ}) = γ θ` for all `θ`).

The theorem `Work.Smooth.SphereJordan.disc_spans_schoenflies_clean` says that `F` spans the same
disc: its image is `closure S.V` and the image of the open unit disc is the bounded side `S.V`.

## The proof

Write `f z` for the complex number underlying `F z` and `A := openImage f = f '' {z | ‖z‖ < 1}`
(`Work.Smooth.SphereJordan.openImage`) for the image of the *open* disc.  The argument has three
steps.

1. **`A` lies on one side of the curve.**  `A` is preconnected
   (`openImage_preconnected`) and disjoint from the trace of `γ` (`openImage_subset_compl_range`),
   hence `A ⊆ S.U` or `A ⊆ S.V` (`Work.Smooth.Jordan.plane_separation_preconnected_subset`).

2. **The case `A ⊆ S.U` is impossible.**  The Schoenflies disc `S.e` and `f` are two injective
   continuous maps of `𝔻` into `ℂ` with the same boundary circle, so by
   `Work.Smooth.SphereJordan.disc_interiors_meet_of_common_boundary` their open images intersect:
   there are `z`, `w` of the open disc with `S.e z = f w`.  But `S.e z ∈ S.V`
   (`Work.Smooth.Jordan.plane_schoenflies_openDisc_eq`) while `f w ∈ A ⊆ S.U`, against the
   disjointness of the two sides of the curve.  (The cited lemma is the Borsuk–Ulam parity form of
   the Jordan curve theorem: it uses only the covering space `ℝ → S¹`.)

3. **The case `A ⊆ S.V`.**  Then `A ⊆ S.V = openImage S.e`
   (`Work.Smooth.Jordan.plane_schoenflies_openDisc_eq`), so `f` and `S.e` have the same range and
   the same open image by `Work.Smooth.SphereJordan.eq_of_openImage_subset` (which lifts `f`
   through the embedding `S.e` and applies Brouwer's surjectivity theorem
   `Work.Smooth.SphereJordan.discEmbedding_surjective`).  This is the conclusion, using
   `S.range_e`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **The image of an injective disc in the plane, with the same boundary as a Schoenflies disc, is
that Schoenflies disc.**

Let `γ` be a simple closed plane curve with trace in the open unit disc, `S` a Schoenflies datum for
it, and `F : C(𝔻, 𝔻)` a continuous injection whose boundary circle maps to `γ` in the given
parametrisation.  Then `F` and the Schoenflies embedding `S.e` have the same image
(`closure S.V`) and the same image of the open disc (`S.V`). -/
theorem disc_spans_schoenflies_clean {γ : Work.Smooth.Jordan.PlaneCurve} (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)}
    (hFinj : Function.Injective F)
    (hFbd : ∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.circlePoint θ) : Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) :
    Set.range (fun z : Work.Smooth.SphereJordan.Disc => ((F z : Work.Smooth.SphereJordan.Disc) : ℂ)) = closure S.V ∧
      ((fun z : Work.Smooth.SphereJordan.Disc => ((F z : Work.Smooth.SphereJordan.Disc) : ℂ)) ''
        {z : Work.Smooth.SphereJordan.Disc | ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1}) = S.V := by
  have hcont : Continuous fun z : Work.Smooth.SphereJordan.Disc =>
      ((F z : Work.Smooth.SphereJordan.Disc) : ℂ) :=
    continuous_subtype_val.comp F.continuous
  set f : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
    ⟨fun z : Work.Smooth.SphereJordan.Disc => ((F z : Work.Smooth.SphereJordan.Disc) : ℂ), hcont⟩
    with hfdef
  have hfinj : Function.Injective f := fun a b h => hFinj (Subtype.ext h)
  have hfb : ∀ θ : ℝ, f (Work.Smooth.SphereJordan.circlePoint θ) = γ.γ θ := fun θ => hFbd θ
  have hpre : IsPreconnected (openImage f) := openImage_preconnected f
  have hsub : openImage f ⊆ (γ.trace)ᶜ := by
    have h := openImage_subset_compl_range hfinj hfb
    simpa [Work.Smooth.Jordan.PlaneCurve.trace] using h
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S.toPlaneSeparation hpre hsub
    with hU | hV
  · -- ## the case `openImage f ⊆ S.U` is impossible
    -- Two embedded discs of the plane with the same boundary have intersecting interiors; applied
    -- to `S.e` and `f` this point lies both in `S.V` and in `S.U`.
    exfalso
    obtain ⟨z, w, hz, hw, hzw⟩ :=
      disc_interiors_meet_of_common_boundary (f := S.e) (g := f) S.inj hfinj (fun θ => by
        show S.e (Work.Smooth.SphereJordan.circlePoint θ)
          = f (Work.Smooth.SphereJordan.circlePoint θ)
        rw [S.boundary θ]
        exact (hfb θ).symm)
    have hzV : S.e z ∈ S.V := by
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact ⟨z, hz, rfl⟩
    have hwU : S.e z ∈ S.U := by
      rw [hzw]
      exact hU ⟨w, hw, rfl⟩
    exact (Set.disjoint_left.mp S.disjoint_UV hwU) hzV
  · -- ## the case `openImage f ⊆ S.V`
    have hopene : openImage S.e = S.V := Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S
    have hsubV : openImage f ⊆ openImage S.e := by
      rw [hopene]
      exact hV
    obtain ⟨hrange, hopen⟩ := eq_of_openImage_subset (c := γ.γ) hfinj S.inj hfb S.boundary hsubV
    refine ⟨?_, ?_⟩
    · change Set.range (⇑f) = closure S.V
      rw [hrange, S.range_e]
    · change (⇑f) '' {z : Work.Smooth.SphereJordan.Disc |
        ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1} = S.V
      rw [show (⇑f) '' {z : Work.Smooth.SphereJordan.Disc |
          ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1} = openImage f from rfl]
      rw [hopen, hopene]

end

end Work.Smooth.SphereJordan
