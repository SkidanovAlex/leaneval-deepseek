import Mathlib
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.disc_interiors_meet_of_common_boundary
import Submission.Work.Smooth.Jordan.plane_schoenflies_openDisc_eq
import Submission.Work.Smooth.Jordan.plane_separation_preconnected_subset

/-!
# An injective disc map spans the Schoenflies disc of its boundary curve

`discCurve F` is the plane curve traced by the boundary circle of an injective continuous map
`F : 𝔻 → ℂ`.  The main theorem `discCurveSpans` says that `F` *spans* that curve: its image is the
closure of the bounded side `S.V` of a Jordan–Schoenflies datum `S` for the curve, and the image of
the *open* disc is exactly `S.V`.

This is the uniqueness of the spanning disc of a Jordan curve: two embeddings of the closed disc
whose boundaries (with the same parametrisation) coincide have the same image.  The proof is the
one of `Work.Smooth.SphereJordan.disc_spans_schoenflies_clean`, with the hypothesis that the curve
lies inside the unit disc removed (it is unused there).

Write `A := openImage F` for the image of the open disc.  It is preconnected
(`openImage_preconnected`) and disjoint from the trace of the curve
(`openImage_subset_compl_range`), so `A ⊆ S.U` or `A ⊆ S.V`
(`Work.Smooth.Jordan.plane_separation_preconnected_subset`).

* If `A ⊆ S.U`, then a contradiction: `F` and the Schoenflies embedding `S.e` are two embeddings of
  the disc agreeing on the boundary circle, so their open images meet
  (`disc_interiors_meet_of_common_boundary`, the Borsuk–Ulam parity form of the Jordan curve
  theorem); but a point of `openImage S.e` lies in `S.V`
  (`Work.Smooth.Jordan.plane_schoenflies_openDisc_eq`) while a point of `A` lies in `S.U`, and the
  two sides are disjoint.
* If `A ⊆ S.V = openImage S.e`, then `F` and `S.e` have the same range and the same open image
  (`eq_of_openImage_subset`: lift `F` through the embedding `S.e` and use Brouwer's theorem that an
  injective self-map of the disc fixing the boundary circle is surjective).  With `S.range_e` this
  is the claim.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **An injective disc map with boundary curve `γ` spans the Schoenflies disc of `γ`.**

If `F : 𝔻 → ℂ` is a continuous injection whose boundary circle traces the plane curve `γ`, and
`S` is a Jordan–Schoenflies datum for `γ`, then the image of `F` is the closure of the bounded side
of `γ` and the image of the open disc is that bounded side. -/
theorem range_eq_closure_of_boundary_eq {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {F : C(Disc, ℂ)}
    (hF : Function.Injective F) (hbd : ∀ θ : ℝ, F (circlePoint θ) = γ.γ θ) :
    Set.range F = closure S.V ∧ openImage F = S.V := by
  have hpre : IsPreconnected (openImage F) := openImage_preconnected F
  have hsub : openImage F ⊆ γ.traceᶜ := by
    have h := openImage_subset_compl_range hF hbd
    simpa [Work.Smooth.Jordan.PlaneCurve.trace] using h
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S.toPlaneSeparation hpre hsub
    with hU | hV
  · -- the image of the open disc cannot lie on the unbounded side
    exfalso
    obtain ⟨z, w, hz, hw, hzw⟩ :=
      disc_interiors_meet_of_common_boundary (f := S.e) (g := F) S.inj hF
        (fun θ => by rw [S.boundary θ, ← hbd θ])
    have hzV : S.e z ∈ S.V := by
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact ⟨z, hz, rfl⟩
    have hzU : S.e z ∈ S.U := by
      rw [hzw]
      exact hU ⟨w, hw, rfl⟩
    exact (Set.disjoint_left.mp S.disjoint_UV hzU) hzV
  · have hopene : openImage S.e = S.V := Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S
    have hsubV : openImage F ⊆ openImage S.e := hopene ▸ hV
    obtain ⟨hrange, hopen⟩ :=
      eq_of_openImage_subset (c := γ.γ) hF S.inj hbd S.boundary hsubV
    exact ⟨by rw [hrange, S.range_e], by rw [hopen, hopene]⟩

/-- **The image of an injective disc map is the closure of the bounded side of its boundary curve,
and the image of the open disc is that bounded side.** -/
theorem discCurveSpans {F : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hF : Function.Injective F)
    (S : Work.Smooth.Jordan.PlaneSchoenflies (Work.Smooth.SphereJordan.discCurve F)) :
    Set.range (fun z : Work.Smooth.SphereJordan.Disc => (F z : ℂ)) = closure S.V ∧
    ((fun z : Work.Smooth.SphereJordan.Disc => (F z : ℂ)) ''
        {z : Work.Smooth.SphereJordan.Disc |
          ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1} = S.V) := by
  have hbd : ∀ θ : ℝ, F (circlePoint θ) = (discCurve F).γ θ := fun θ => (discCurve_apply F θ).symm
  obtain ⟨hrange, hopen⟩ := range_eq_closure_of_boundary_eq S hF hbd
  refine ⟨?_, ?_⟩
  · change Set.range ⇑F = closure S.V
    rw [hrange]
  · change ⇑F '' {z : Disc | ‖((z : Disc) : ℂ)‖ < 1} = S.V
    rw [show ⇑F '' {z : Disc | ‖((z : Disc) : ℂ)‖ < 1} = openImage F from rfl]
    rw [hopen]

end

end Work.Smooth.SphereJordan
