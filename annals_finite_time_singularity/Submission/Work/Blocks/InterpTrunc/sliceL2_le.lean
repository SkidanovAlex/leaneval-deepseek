/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted slice Poincaré–Sobolev bound for the truncation of `interp_truncation`

For a `C^∞` slice `f` on a neighbourhood of `[0, π/2]` which vanishes at both endpoints, the
weighted `L²`-norms of `f` and of `f'` are bounded by the weighted `L²`-norm of `f''`:

  `∫_θ f² σ ≤ K ∫_θ (f'')² σ`  and  `∫_θ (f')² σ ≤ K ∫_θ (f'')² σ`,  `σ = sin(2θ)^{-η}`,

with a universal `K`.  The proof is a two-line consequence of the pointwise boundary bounds of
`Submission/Work/FTS/EllipticEst/ThetaU/SliceDerivSelfOpen.lean`
(`slice_deriv_sq_le_open`, `slice_self_sq_le_open`), which bound `(f' θ)²` and `f θ²` by
`A · B` with `A = ∫(f'')²σ` and `B = ∫ sin(2θ)^η ≤ π/2`, together with `∫_θ σ ≤ 10000`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Blocks.InterpTruncDefs
import Submission.Work.FTS.EllipticEst.ThetaU.SliceDerivSelfOpen
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

theorem sliceV_continuousOn_of_sliceSmoothO {u : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.ThetaU.SliceSmoothO u) :
    ContinuousOn (Work.FTS.EllipticEst.sliceV u) Work.Spaces.Iθ := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub

theorem integrableOn_sliceV_sq_mul_thEta {u : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.ThetaU.SliceSmoothO u) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta (sliceV_continuousOn_of_sliceSmoothO hsm)

/-- **The weighted slice Poincaré–Sobolev bound.** -/
theorem sliceL2_le : ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
    Work.FTS.EllipticEst.ThetaU.SliceSmoothO f → f 0 = 0 → f (Real.pi / 2) = 0 →
    (∫ θ in Work.Spaces.Iθ,
        (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ K * ∫ θ in Work.Spaces.Iθ,
        (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ∧
    (∫ θ in Work.Spaces.Iθ,
        (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ K * ∫ θ in Work.Spaces.Iθ,
        (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  refine ⟨10000 * (Real.pi / 2) ^ 3, by positivity, ?_⟩
  intro f hsm h0 h1
  have hint := integrableOn_sliceV_sq_mul_thEta hsm
  obtain ⟨-, hB⟩ := Work.FTS.EllipticEst.integrableOn_sin_two_rpow
    (le_of_lt Work.Spaces.eta_pos)
  obtain ⟨hσint, hσ⟩ := Work.FTS.EllipticEst.integrableOn_thEta
  have hend : f 0 = f (Real.pi / 2) := by rw [h0, h1]
  have hd := Work.FTS.EllipticEst.ThetaU.slice_deriv_sq_le_open hsm hend hint
  have hs := Work.FTS.EllipticEst.ThetaU.slice_self_sq_le_open hsm h0 h1 hint
  simp only [Work.FTS.EllipticEst.sliceV] at hd hs ⊢
  -- nonnegativity of the key integral and the size of the two auxiliary constants
  have hQ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hx))
  have hB0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hx) _)
  have hσ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => Work.FTS.EllipticEst.thEta_nonneg hx)
  have hpi : (1 : ℝ) < Real.pi / 2 := by
    have := Real.pi_gt_three
    linarith
  have hcube : (Real.pi / 2) ≤ (Real.pi / 2) ^ 3 := by
    have hsq : (1 : ℝ) ≤ (Real.pi / 2) ^ 2 := by nlinarith [hpi]
    nlinarith [hsq, hpi]
  have hIntB : MeasureTheory.Integrable
      (fun θ => (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
            * Work.FTS.EllipticEst.thEta x)
          * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
          * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hσint.const_mul _
  constructor
  · have key : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
            * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                  * Work.FTS.EllipticEst.thEta x)
                * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
              * Work.FTS.EllipticEst.thEta θ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ hIntB ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
            with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
            with θ hθ
          exact mul_le_mul_of_nonneg_right (hd θ hθ) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      rwa [MeasureTheory.integral_const_mul] at h1
    have h2 : ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
            * Work.FTS.EllipticEst.thEta x)
          * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
        ≤ 10000 * (Real.pi / 2) ^ 3 * (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
            * Work.FTS.EllipticEst.thEta x) := by
      have hBC : (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
          ≤ (Real.pi / 2) * 10000 := by nlinarith [hB, hσ, hB0, hσ0]
      have hmid : ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x)
            * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
          ≤ (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
            * ((Real.pi / 2) * 10000) := by
        rw [show ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                * Work.FTS.EllipticEst.thEta x)
              * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
            = (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                * Work.FTS.EllipticEst.thEta x)
              * ((∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
                * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)) from by ring]
        exact mul_le_mul_of_nonneg_left hBC hQ0
      have hlast : (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x) * ((Real.pi / 2) * 10000)
          ≤ 10000 * (Real.pi / 2) ^ 3 * (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x) := by
        rw [show (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x) * ((Real.pi / 2) * 10000)
            = 10000 * (Real.pi / 2) * (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x) from by ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcube (by norm_num)) hQ0
      linarith [hmid, hlast]
    linarith [key, h2]
  · have key : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ((Real.pi / 2) ^ 2
            * ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                  * Work.FTS.EllipticEst.thEta x)
              * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))))
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              ((Real.pi / 2) ^ 2
                * ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                      * Work.FTS.EllipticEst.thEta x)
                  * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))))
              * Work.FTS.EllipticEst.thEta θ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hσint.const_mul _) ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
            with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
            with θ hθ
          exact mul_le_mul_of_nonneg_right (hs θ hθ) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      rwa [MeasureTheory.integral_const_mul] at h1
    have h2 : ((Real.pi / 2) ^ 2
          * ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                * Work.FTS.EllipticEst.thEta x)
            * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))))
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
        ≤ 10000 * (Real.pi / 2) ^ 3 * (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
            * Work.FTS.EllipticEst.thEta x) := by
      have hBC : (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
          ≤ (Real.pi / 2) * 10000 := by nlinarith [hB, hσ, hB0, hσ0]
      have h4 : (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x)
            * ((∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ))
          ≤ (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
            * ((Real.pi / 2) * 10000) := mul_le_mul_of_nonneg_left hBC hQ0
      calc ((Real.pi / 2) ^ 2
              * ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                    * Work.FTS.EllipticEst.thEta x)
                * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))))
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ)
          = (Real.pi / 2) ^ 2
              * ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
                    * Work.FTS.EllipticEst.thEta x)
                * ((∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
                  * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ))) := by ring
        _ ≤ (Real.pi / 2) ^ 2 * ((∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x) * ((Real.pi / 2) * 10000)) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
        _ = (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
              * ((Real.pi / 2) ^ 3 * 10000) := by ring
        _ = 10000 * (Real.pi / 2) ^ 3 * (∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2
              * Work.FTS.EllipticEst.thEta x) := by ring
    linarith [key, h2]

end Work.Blocks.InterpTrunc
