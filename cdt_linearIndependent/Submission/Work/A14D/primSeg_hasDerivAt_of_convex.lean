import Mathlib
import Submission.Work.A14D.LC_setup
import Submission.Work.C17g.segment_primitive

/-!
# `Work.A14D.primSeg_hasDerivAt_of_convex`

The primitive `primSeg f c z = ∫₀¹ f (c + t(z−c))·(z−c) dt` along the segment from `c` to `z`
is holomorphic on a convex open set `S` on which `f` is holomorphic, with complex derivative
`f z` at every `z ∈ S`.

The proof rewrites `primSeg f c` as `z ↦ (z − c) • ∫₀¹ f (c + t • (z−c))`, which is the
"segment integral" form of the Poincaré primitive on a convex set, and applies the general
Banach-space statement `Work.C17g.segment_primitive`.  (The computation of the integral against
the right endpoint of the segment is the content of `intervalIntegral.integral_mul_const`.)
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace Work.A14D

theorem primSeg_hasDerivAt_of_convex {S : Set ℂ} (hSc : Convex ℝ S) (hSo : IsOpen S) {c : ℂ}
    (hc : c ∈ S) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (Work.A14D.primSeg f c) S ∧
      ∀ z ∈ S, HasDerivAt (Work.A14D.primSeg f c) (f z) z := by
  have h := Work.C17g.segment_primitive (E := ℂ) hSc hSo hc hf
  have hfun : Work.A14D.primSeg f c
      = fun z => (z - c) • ∫ t in (0 : ℝ)..1, f (c + t • (z - c)) := by
    funext z
    rw [Work.A14D.primSeg]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    simp [Complex.real_smul, mul_comm]
  rw [hfun]
  exact h

end Work.A14D
