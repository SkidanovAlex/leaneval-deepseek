import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTargetSpans
import Submission.Work.Smooth.SphereJordan.PCopy.tgtSpansClean
import Submission.Work.Smooth.SphereJordan.PCopy.twoCutsAssembly

/-!
# The planar pcannulus theorem in its injection form (the two-pccuts route)

The final assembly of `Work.Smooth.SphereJordan.pcannulusInjectionTwoCutsAlt`, Pardon's geometric
core: for a simple closed plane curve `γ` inside the open unit disc, with Schoenflies datum `S`,
there is an injective continuous self-map `F` of the model disc fixing `∂𝔻` pointwise and carrying
the inner circle of radius `1/2` onto `γ`, with the precise parametrisation
`F (halfCirclePoint (s * θ)) = γ.γ θ` for one of the two signs `s = ±1`.

The proof collects the four ingredients of the fleet:

* the two-pccuts configuration (`t₁ s₁ t₂ s₂`, the two parameters `θ₁ θ₂` on `γ`), from
  `Work.SphereJordan.pcexists_targetData`, bundled as a `Work.SphereJordan.pcSpanHyp`;
* the pairing flag `b` for which the bounded side of `γ` lies on the unbounded side of both
  four-arc curves, from `Work.SphereJordan.pctgtSpans_pairingExists`;
* the two halves of the cut pcannulus, from `Work.SphereJordan.pctgtSpans_spansOfPairing` (whose
  images cover `pcannulus S` and meet exactly in the two crosscuts);
* the gluing of the two target spanning discs with the two model half-pcannulus discs, together with
  the reparametrisation of the inner circle, from `Work.SphereJordan.pctwoCutsAssembly` (whose last
  step is `Work.SphereJordan.pcannulusInnerReparam`).
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

theorem pcannulusInjectionTwoCutsAlt (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  -- the two-pccuts configuration
  obtain ⟨t₁, s₁, t₂, s₂, θ₁, θ₂, ht₁, ht₁s₁, ht₂, ht₂s₂, ha₁, hseg₁, hout₁, ha₂, hseg₂, hout₂,
    hθ₁, hθ₂, hθ, hθ', hmax₁, hmax₂⟩ :=
    Work.SphereJordan.pcexists_targetData h hs hball S
  let H : Work.SphereJordan.pcSpanHyp h hs hball S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, θ₁ := θ₁, θ₂ := θ₂,
      ht₁ := ht₁, ht₁s₁ := ht₁s₁, ht₂ := ht₂, ht₂s₂ := ht₂s₂,
      ha₁ := ha₁, hseg₁ := hseg₁, hout₁ := hout₁,
      ha₂ := ha₂, hseg₂ := hseg₂, hout₂ := hout₂,
      hθ₁ := hθ₁, hθ₂ := hθ₂, hθ := hθ, hθ' := hθ', hmax₁ := hmax₁, hmax₂ := hmax₂ }
  -- the pairing flag for which the bounded side of `γ` is on the unbounded side of both pieces
  obtain ⟨b, hb⟩ := Work.SphereJordan.pctgtSpans_pairingExists h hs hball S H
  -- the two halves of the cut pcannulus
  have hspans := Work.SphereJordan.pctgtSpans_spansOfPairing H b
    (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b)
    (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b) hb
  obtain ⟨-, -, -, -, -, -, hun, hin⟩ := hspans
  -- the gluing, and the reparametrisation of the inner circle
  refine Work.SphereJordan.pctwoCutsAssembly h hs hball S b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂
    (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b)
    (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b) ?_ ?_
  · rw [← (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b).range_e,
      ← (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b).range_e]
    exact hun
  · rw [← (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b).range_e,
      ← (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b).range_e]
    exact hin

end

end Work.Smooth.SphereJordan
