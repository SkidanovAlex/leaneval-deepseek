/-
Copyright: work module for the Elgindi finite-time singularity project.

# The open-class angular Poincaré comparison for the `ℋ^k`-integrals

For every `k` there is `C > 0` (independent of `α ∈ (0,1]`) such that for every `f` which is
`C^∞` on the half-strip `(0,∞) × (-1, π/2+1)`, vanishes on the two angular boundary lines and
whose `ℋ^k`-integral of `∂_θ²f` is honest,

  `∫_{Iθ} HkIntegrand α k (∂_θ f) z θ ≤ C ∫_{Iθ} HkIntegrand α k (∂_θ² f) z θ`   for all `z ∈ [0,∞)`.

This is the split of `ThetaU.HkIntegrand_integral_le_pth2_pth_point` (the honest `C^∞` port of
`Blocks.HkIntegrand_integral_le_pth2_pth`, whose `SmoothNbhd` hypothesis is *analyticity* in this
Mathlib) from its analytic input: the level-dependent constants of the honest slice estimate
`ThetaU.slice_d_bound_open` are uniformised over the finitely many levels `K ≤ k`.

NOTE on the order type.  In this Mathlib `ContDiffOn ℝ ⊤` is the *analytic* order `ω`, not `C^∞`:
so `Work.Spaces.SmoothNbhd` and `Work.FTS.EllipticEst.SliceSmooth` are analyticity, and neither
is available for the residual `EllResid α F Ψ` (whose `L₁₂(F)` is only `C^∞` on `(0,∞)`).  The
honest classes are `ContDiffOn ℝ ∞` (`∞ = Work.Stability.smoothOrder`), which is
`ThetaU.SmoothOpenθ` on the half-strip and `ThetaU.SliceSmoothO` on a slice.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaU.Defs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ThetaU.slice_d_bound_open
import Submission.Work.FTS.EllipticEst.ThetaU.HkIntegrand_integral_le_pth2_pth_point

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The per-`z` angular Poincaré comparison of the `ℋ^k`-integrands, in the `C^∞` class.** -/
theorem pth_HkIntegrand_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → SmoothOpenθ f →
      Work.Spaces.VanishTheta f →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
  -- the level-dependent constants of the slice estimate `slice_d_bound_open`
  let cd : ℕ → ℝ := fun K => Classical.choose (slice_d_bound_open K)
  have hcd : ∀ K : ℕ, 0 < cd K ∧
      (∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → SliceSmoothO u → u 0 = 0 →
        u (Real.pi / 2) = 0 →
        MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          Work.Spaces.Iθ →
        (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
        (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
              ≤ cd K * Work.FTS.EllipticEst.slicePhi α K u θ) ∧
          (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
                ≤ cd K * Work.FTS.EllipticEst.slicePhi α K u θ)) :=
    fun K => Classical.choose_spec (slice_d_bound_open K)
  -- the uniform constant over the finitely many levels `K ≤ k`
  let C2 : ℝ := (∑ K ∈ Finset.range (k + 1), cd K) + 1
  have hle : ∀ K : ℕ, K ≤ k → cd K ≤ C2 := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : cd K ≤ ∑ K' ∈ Finset.range (k + 1), cd K' :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcd K').1) hmem
    simp only [C2]; linarith
  have hC2 : ∀ (K : ℕ), K ≤ k → ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      SliceSmoothO u → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ →
      (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
      (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ C2 * Work.FTS.EllipticEst.slicePhi α K u θ) ∧
        (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
              ≤ C2 * Work.FTS.EllipticEst.slicePhi α K u θ) := by
    intro K hK α u hα0 hα1 hsm h0 hpi hint hm
    obtain ⟨b1, b2⟩ := (hcd K).2 α u hα0 hα1 hsm h0 hpi hint hm
    have hKle := hle K hK
    exact ⟨fun θ hθ => le_trans (b1 θ hθ)
        (mul_le_mul_of_nonneg_right hKle
          (Work.FTS.EllipticEst.Blocks.slicePhi_nonneg α K u hθ)),
      fun i hi θ hθ => le_trans (b2 i hi θ hθ)
        (mul_le_mul_of_nonneg_right hKle
          (Work.FTS.EllipticEst.Blocks.slicePhi_nonneg α K u hθ))⟩
  exact HkIntegrand_integral_le_pth2_pth_point k C2 hC2

end Work.FTS.EllipticEst.ThetaU
