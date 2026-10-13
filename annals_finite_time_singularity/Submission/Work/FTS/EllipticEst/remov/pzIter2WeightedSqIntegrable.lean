import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# Honesty of the angular slice `θ ↦ (∂_z²Ψ)² · sin(2θ)^{-η}`

For a datum of the weak hypothesis class `Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` with
`k ≥ 1`, the angular slice `θ ↦ (∂_z²Ψ z θ)² sin(2θ)^{-η}` is integrable over `Iθ` for every
`z > 0`.

The proof is a direct consequence of the honesty hypothesis
`Work.Spaces.HkMem α k (fun z θ => z² ∂_z²Ψ z θ)` carried by the class: the `i = 0` term of the
first (`D_z`-)sum of `Work.Spaces.HkIntegrand` is the square
`(z²∂_z²Ψ · w z / sin(2θ)^{η/2})²`, which dominates `z⁴ w z² · (∂_z²Ψ)² sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.mul_w_sin_rpow_sq`), and it is integrable on the slice by
`Work.FTS.EllipticEst.integrableOn_zSummand`.  Since `z⁴ w z² ≠ 0` for `z > 0`, the
corresponding factor can be divided out.
-/

/-- **Honesty of a single weighted `z`-slice.**  If `G` is `C^∞` on the open quadrant and
`HkMem α k G`, then for every `z > 0` the angular slice `θ ↦ (G z θ)² sin(2θ)^{-η}` is
integrable over `Iθ`.

The `i = 0` summand of `HkIntegrand` is `(G z θ · w z / sin(2θ)^{η/2})²`, which equals
`(w z)² · (G z θ)² sin(2θ)^{-η}` on `Iθ` (`Work.FTS.EllipticEst.mul_w_sin_rpow_sq`); it is
integrable by `Work.FTS.EllipticEst.integrableOn_zSummand`, and the factor `(w z)²` is nonzero
for `z > 0`. -/
private theorem integrable_sq_rpow_of_HkMem {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (hmem : Work.Spaces.HkMem α k G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable
      (fun θ : ℝ => (G z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  have hkey : ∀ θ ∈ Work.Spaces.Iθ,
      ((Work.Spaces.w z) ^ 2)⁻¹
          * (G z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (G z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq (G z θ) (Work.Spaces.w z) hθ]
    field_simp
  have hint := Work.FTS.EllipticEst.integrableOn_zSummand α k hG hmem 0 (Nat.zero_le k) hzIz
  have hI2 : MeasureTheory.Integrable
      (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * (G z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint.const_mul _
  refine hI2.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact hkey θ hθ

theorem pzIter2WeightedSqIntegrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  have hA : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hGs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen]
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_fst.pow 2
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      hA.pzIter 2
    exact h1.mul h2
  have key : MeasureTheory.Integrable
      (fun θ : ℝ => ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_sq_rpow_of_HkMem hGs h.memA hz
  refine (key.const_mul (((z ^ 2) ^ 2)⁻¹)).congr ?_
  filter_upwards with θ
  rw [mul_pow, ← mul_assoc,
    inv_mul_cancel_left₀ (pow_ne_zero 2 (pow_ne_zero 2 hz'))]

end Work.FTS.EllipticEst.remov
