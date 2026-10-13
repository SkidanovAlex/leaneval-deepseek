import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary auxiliary facts -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
private lemma continuous_sinCos2_snd :
    Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
  simp only [Work.Elliptic.sinCos2]
  exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).comp continuous_snd

/-- **The pointwise domination on the box.**

For `0 < a < z` and `θ ∈ Iθ`,
`|pzIter 2 Ψ z θ · sinθcos²θ| ≤ a⁻⁴ · HkIntegrand α k (z²∂_z²Ψ) z θ + 1`.

This is the combination of `abs_mul_sinCos2_le_weighted` (which absorbs the angular profile
into `(pzIter 2 Ψ · w/sin(2θ)^{η/2})² + 1`) with the single-summand bound
`sq_le_HkIntegrand_z` (applied at `i = 0` to `z²∂_z²Ψ`) and the trivial `z ≥ a`. -/
private lemma pointwise_bound {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ} {a z θ : ℝ}
    (ha : 0 < a) (hz : a < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ|
      ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1 := by
  have hzpos : 0 < z := lt_trans ha hz
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ) hzpos hθ
  have hz4 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hzpos)
  have h2 : (Work.Spaces.pzIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [eq_inv_mul_iff_mul_eq₀ hz4]
    ring
  have h3 : (Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ≥
      ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hh := Work.Spaces.sq_le_HkIntegrand_z α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
    simpa using hh
  have hcinv : (0 : ℝ) ≤ (a ^ 4)⁻¹ := by positivity
  have hzipow : (z ^ 4)⁻¹ ≤ (a ^ 4)⁻¹ := by
    rw [inv_le_inv₀ (show (0 : ℝ) < z ^ 4 by positivity)
      (show (0 : ℝ) < a ^ 4 by positivity)]
    exact pow_le_pow_left₀ ha.le hz.le 4
  have hX : (0 : ℝ) ≤ ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_nonneg _
  calc |Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pzIter 2 Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := h1
    _ = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        rw [h2]
    _ ≤ (a ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hstep := mul_le_mul_of_nonneg_right hzipow hX
        linarith
    _ ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1 := by
        have hstep := mul_le_mul_of_nonneg_left h3 hcinv
        linarith

/-! ## The main lemma -/

/-- **Box integrability of `θ ↦ pzIter 2 Ψ z θ * sinCos2 θ`.**

For a datum of the weak class `EllWeakPos α k F Ψ`, every `a > 0` (and every `b`), the function
`(z, θ) ↦ pzIter 2 Ψ z θ * sinCos2 θ` is integrable on the product of `(a, b]` and `Iθ`.

Proof sketch.  From `HkMem α k (fun z θ => z^2 * pzIter 2 Ψ z θ)` and Tonelli, the square
`(z, θ) ↦ (z^2 * pzIter 2 Ψ z θ * (w z / sin(2θ)^(η/2)))^2` has finite integral over the box;
Cauchy–Schwarz against `θ ↦ sin(2θ)^(η/2) / (z^2 * w z) = sin(2θ)^(η/2)/(1+z)^2`
(whose square is integrable over the box since `b` is finite and `a > 0`) gives the claim.
A.e. measurability on the box comes from the smoothness of `Ψ` on the open quadrant.
The ready-made reference is `remov/hkMemSliceAbsIntegrable.lean`, conjunct 3. -/
theorem weakSliceBoxIntegrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ a b : ℝ, 0 < a → MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro a b ha
  haveI hfinθ : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ]; infer_instance
  haveI hfinz : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc a b)) := inferInstance
  haveI hfinprod : IsFiniteMeasure ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := inferInstance
  -- smoothness of `Ψ` and of `z ↦ z²∂_z²Ψ` on the open quadrant
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSOg : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    (contDiff_fst.pow 2).contDiffOn.mul (hSO.pzIter 2)
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iz := fun x hx => by
    rw [Work.Spaces.Iz]; exact le_of_lt (lt_trans ha hx.1)
  -- ## Step 1: the `H^k`-integrand is integrable on the box
  have hKint : MeasureTheory.Integrable (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.FTS.EllipticEst.integrable_prod_ae ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => Filter.Eventually.of_forall (fun θ => ?_))
      rw [Work.Spaces.HkIntegrand]
      exact add_nonneg (Work.Spaces.hkZSum_nonneg α k _ z θ)
        (Work.Spaces.hkMixedSum_nonneg α k _ z θ)
    · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
        (hSOg.continuousOn_HkIntegrand α k) ha.le
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
      exact h.memA.1 z (hsub hz)
    · exact h.memA.2.mono_set hsub
  -- ## Step 2: the dominating function is integrable on the box
  refine MeasureTheory.Integrable.mono'
    (g := fun p : ℝ × ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2 + 1) ?_ ?_ ?_
  · exact (hKint.const_mul ((a ^ 4)⁻¹)).add (MeasureTheory.integrable_const 1)
  · refine Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
      (((hSO.pzIter 2).continuousOn).mul continuous_sinCos2_snd.continuousOn) ha.le
  · rw [MeasureTheory.Measure.prod_restrict (Set.Ioc a b) Work.Spaces.Iθ]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc))
      (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := hp
    simp only [Real.norm_eq_abs]
    exact pointwise_bound ha hz.1 hθ

end

end Work.FTS.EllipticEst.remov.SourceBound
