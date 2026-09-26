import Mathlib
import Submission.Work.SphereJordan.annulusTargetSpans
import Submission.Work.SphereJordan.tgtSpansClean
import Submission.Work.SphereJordan.twoCutsAssembly

/-!
# The planar annulus theorem in its injection form (the two-cuts route)

The final assembly of `Work.Smooth.SphereJordan.annulusInjectionTwoCutsAlt`, Pardon's geometric
core: for a simple closed plane curve `γ` inside the open unit disc, with Schoenflies datum `S`,
there is an injective continuous self-map `F` of the model disc fixing `∂𝔻` pointwise and carrying
the inner circle of radius `1/2` onto `γ`, with the precise parametrisation
`F (halfCirclePoint (s * θ)) = γ.γ θ` for one of the two signs `s = ±1`.

The proof collects the four ingredients of the fleet:

* the two-cuts configuration (`t₁ s₁ t₂ s₂`, the two parameters `θ₁ θ₂` on `γ`), from
  `Work.SphereJordan.exists_targetData`, bundled as a `Work.SphereJordan.SpanHyp`;
* the pairing flag `b` for which the bounded side of `γ` lies on the unbounded side of both
  four-arc curves, from `Work.SphereJordan.tgtSpans_pairingExists`;
* the two halves of the cut annulus, from `Work.SphereJordan.tgtSpans_spansOfPairing` (whose
  images cover `annulus S` and meet exactly in the two crosscuts);
* the gluing of the two target spanning discs with the two model half-annulus discs, together with
  the reparametrisation of the inner circle, from `Work.SphereJordan.twoCutsAssembly` (whose last
  step is `Work.SphereJordan.annulusInnerReparam`).
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

theorem annulusInjectionTwoCutsAlt (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  -- the two-cuts configuration
  obtain ⟨t₁, s₁, t₂, s₂, θ₁, θ₂, ht₁, ht₁s₁, ht₂, ht₂s₂, ha₁, hseg₁, hout₁, ha₂, hseg₂, hout₂,
    hθ₁, hθ₂, hθ, hθ', hmax₁, hmax₂⟩ :=
    Work.SphereJordan.exists_targetData h hs hball S
  let H : Work.SphereJordan.SpanHyp h hs hball S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, θ₁ := θ₁, θ₂ := θ₂,
      ht₁ := ht₁, ht₁s₁ := ht₁s₁, ht₂ := ht₂, ht₂s₂ := ht₂s₂,
      ha₁ := ha₁, hseg₁ := hseg₁, hout₁ := hout₁,
      ha₂ := ha₂, hseg₂ := hseg₂, hout₂ := hout₂,
      hθ₁ := hθ₁, hθ₂ := hθ₂, hθ := hθ, hθ' := hθ', hmax₁ := hmax₁, hmax₂ := hmax₂ }
  -- the pairing flag for which the bounded side of `γ` is on the unbounded side of both pieces
  obtain ⟨b, hb⟩ := Work.SphereJordan.tgtSpans_pairingExists h hs hball S H
  -- the two halves of the cut annulus
  have hspans := Work.SphereJordan.tgtSpans_spansOfPairing H b
    (Work.SphereJordan.tgtSpans_upSch h hs hball S H b)
    (Work.SphereJordan.tgtSpans_dnSch h hs hball S H b) hb
  obtain ⟨-, -, -, -, -, -, hun, hin⟩ := hspans
  -- the gluing, and the reparametrisation of the inner circle
  refine Work.SphereJordan.twoCutsAssembly h hs hball S b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂
    (Work.SphereJordan.tgtSpans_upSch h hs hball S H b)
    (Work.SphereJordan.tgtSpans_dnSch h hs hball S H b) ?_ ?_
  · rw [← (Work.SphereJordan.tgtSpans_upSch h hs hball S H b).range_e,
      ← (Work.SphereJordan.tgtSpans_dnSch h hs hball S H b).range_e]
    exact hun
  · rw [← (Work.SphereJordan.tgtSpans_upSch h hs hball S H b).range_e,
      ← (Work.SphereJordan.tgtSpans_dnSch h hs hball S H b).range_e]
    exact hin

end

end Work.Smooth.SphereJordan
