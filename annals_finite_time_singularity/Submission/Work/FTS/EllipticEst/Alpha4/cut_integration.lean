/-
The `z`-integration step of the mixed weighted interpolation estimate.

`cut_integration`: a slicewise inequality, valid at each `z > 0`, is integrated against the
nonnegative planar weight `zc φ k z · w(z)²`, where `zc φ k` is the logarithmic cut-off of
`Alpha4/Cut.lean` (supported in the compact interval `[1/k², k²] ⊂ (0,∞)`, with values in
`[0,1]`) and `w(z) = (1+z)²/z²` is the radial weight of the paper.

The point of the logarithmic cut-off is precisely that it makes the `z`-integration legitimate
without any integrability hypothesis on the slices: `zc φ k` vanishes outside the compact box
`[1/k², k²]`, on which the smooth data `G` is bounded, so the three weighted slice integrals
occurring in the statement are automatically integrable
(`Alpha4/cut_slices_integrable.lean`).  Multiplying the slicewise inequality by the
nonnegative weight and integrating over `z ∈ Iz` then gives the stated inequality
(`Alpha4/weighted_slice_mono.lean`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Alpha4.cut_slices_integrable
import Submission.Work.FTS.EllipticEst.Alpha4.weighted_slice_mono
import Submission.Work.FTS.EllipticEst.interpol_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false

theorem cut_integration {k : ℕ} (hk2 : 2 ≤ k) {c₁ : ℝ} {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ)
          + c₁ * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) :
    (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
        * (∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.Alpha4.zc φ k z)
            * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ))
      ≤ - (∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.Alpha4.zc φ k z)
            * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
                * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
                * Work.FTS.EllipticEst.thEta θ))
        + c₁ * (∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.Alpha4.zc φ k z)
            * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  -- the three weighted `z`-slice integrals are integrable: the cut-off lives on the compact
  -- box `[1/k², k²]`, on which the smooth datum `G` is bounded
  obtain ⟨hA, hB, hC⟩ := cut_slices_integrable hk2 hφK hsm
  -- integrate the slicewise inequality against the nonnegative weight `zc φ k z · w(z)²`
  refine weighted_slice_mono (κ := (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) (c₁ := c₁)
    (γ := fun z => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2)
    (A := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    (B := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
      * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
      * Work.FTS.EllipticEst.thEta θ)
    (C := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ?_ hA hB hC
  intro z hz
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with h0 | hpos
  · -- at `z = 0` both sides vanish, since `w 0 = 0`
    subst h0
    simp [Work.Spaces.w]
  · -- for `z > 0` multiply the slicewise inequality by the nonnegative weight
    have hzc : 0 ≤ Work.FTS.EllipticEst.Alpha4.zc φ k z :=
      Work.FTS.EllipticEst.Alpha4.zc_nonneg
        (fun t => (hφK.2.2.2.1 (Real.log t / Real.log (k : ℝ))).1) z
    have hnn : 0 ≤ Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg hzc (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right (hslice z hpos) hnn
    calc ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * ((Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ))
        = (((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ))
          * (Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (- (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
                * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
                * Work.FTS.EllipticEst.thEta θ)
            + c₁ * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
          * (Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2) := h1
      _ = -((Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
                * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
                * Work.FTS.EllipticEst.thEta θ))
          + c₁ * ((Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2)
              * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by ring

end Work.FTS.EllipticEst.Alpha4
