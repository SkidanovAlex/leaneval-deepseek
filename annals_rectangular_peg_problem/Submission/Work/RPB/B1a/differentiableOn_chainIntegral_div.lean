import Mathlib
import Submission.Work.RPB.B1a.SegChain
import Submission.Work.RPB.B1a.hasDerivAt_segIntegral_div

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral
open scoped Topology

/-! ## Differentiability of the Cauchy-type chain integral off the chain

This file assembles the chain-level statement from the single-segment analytic input
`hasDerivAt_segIntegral_div` (differentiation under the integral sign for the parametrized
segment integral).  The chain integral is a finite sum of segment integrals, so it suffices
to induct on the list of segments.

The two elementary trace inclusions used in the induction step are proved inline so that this
file depends only on the core vocabulary of `SegChain` (`segIntegral`, `chainIntegral`,
`chainTrace`, `mem_segment_param`, `chainIntegral_cons`, `chainIntegral_nil`). -/

/-- **Pointwise differentiability of the Cauchy-type chain integral off the chain.**  If `f` is
continuous on the trace of the polygonal chain `L`, then the map
`w ↦ chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L` is complex differentiable at every point `w`
outside the trace. -/
theorem differentiableAt_chainIntegral_div {f : ℂ → ℂ} (L : List (ℂ × ℂ))
    (hf : ContinuousOn f (chainTrace L)) (w : ℂ) (hw : w ∉ chainTrace L) :
    DifferentiableAt ℂ (fun w => chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L) w := by
  induction L with
  | nil =>
    simp only [chainIntegral_nil]
    exact differentiableAt_const 0
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    -- the tail trace is contained in the full trace
    have htail : ∀ z ∈ chainTrace L, z ∈ chainTrace ((a, b) :: L) :=
      fun _ hz => by obtain ⟨t, ht, hz⟩ := hz; exact ⟨t, by simp [ht], hz⟩
    have hf_head : ContinuousOn f (segment ℝ a b) :=
      hf.mono fun _ hz => ⟨(a, b), by simp, hz⟩
    have hw_head : w ∉ segment ℝ a b :=
      fun hz => hw ⟨(a, b), by simp, hz⟩
    have hf_tail : ContinuousOn f (chainTrace L) := hf.mono htail
    have hw_tail : w ∉ chainTrace L := fun hz => hw (htail _ hz)
    rw [show (fun w => chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) ((a, b) :: L))
        = fun w => segIntegral (fun ζ => f ζ * (ζ - w)⁻¹) a b
            + chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L from by
      funext w
      simp [chainIntegral_cons]]
    exact (hasDerivAt_segIntegral_div hw_head hf_head).differentiableAt.add (ih hf_tail hw_tail)

theorem differentiableOn_chainIntegral_div {f : ℂ → ℂ} (L : List (ℂ × ℂ))
    (hf : ContinuousOn f (chainTrace L)) :
    DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L)
      (chainTrace L)ᶜ := by
  intro w hw
  exact (differentiableAt_chainIntegral_div L hf w hw).differentiableWithinAt

end Work.RPB.B1a
