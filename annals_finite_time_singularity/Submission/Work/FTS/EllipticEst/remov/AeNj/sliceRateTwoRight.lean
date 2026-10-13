import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.weightedCS
import Submission.Work.EllipticEst.Core.thEtaFacts
import Submission.Work.EllipticEst.Core.thEtaInvIntegralBounds
import Submission.Work.FTS.EllipticEst.TT.sliceFtcKey
import Submission.Work.FTS.EllipticEst.TT.sqBoundTendstoPos
import Submission.Work.FTS.EllipticEst.EllTwoAsm.HeavyDerivIntegrable
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.AeNj

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The endpoint rate at `π/2`.**  For a `C¹` slice `f` on `(0, π/2)` with integrable
weighted derivative energy `∫ (f')² thEta` and vanishing right endpoint trace
`f → 0` as `θ → (π/2)⁻`,

  `|f θ| ≤ 2 (π/2 - θ)^((1+η)/2) (∫_{θ}^{π/2} (f')² thEta)^{1/2}`

on `(0, π/2)`.  The proof is the fundamental theorem of calculus
(`sliceFtcKey`), Cauchy–Schwarz for the weighted integral (`weightedCS`) with the sharp
bound `∫_{θ}^{π/2} thEta⁻¹ ≤ 2 (π/2-θ)^{1+η}` (`thEtaInvIntegralBounds`), and the
identification of the boundary constant with `0` (uniqueness of limits, using h1). -/
theorem sliceRateTwoRight {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ| ≤ 2 * Real.sqrt (∫ θ' in Set.Ioo θ (Real.pi / 2),
          (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ')
        * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) := by
  have heta0 : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have heta1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  -- ## Integrability of `deriv f` on every open subinterval of `(0, π/2)`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.FTS.EllipticEst.thEta] using hint
  have hI : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b) :=
    (Work.FTS.EllipticEst.EllTwoAsm.HeavyDerivIntegrable (-(Work.Spaces.eta))
      (by linarith) (by linarith) f hf hint').2
  -- ## The primitive computed from the right end
  obtain ⟨c, hc⟩ := (Work.FTS.EllipticEst.TT.sliceFtcKey f hf hI).2
  have hEtaPos := Work.EllipticEst.Core.thEtaFacts
  have hEtaInv := Work.EllipticEst.Core.thEtaInvIntegralBounds
  -- ## The key Cauchy–Schwarz bound with the sharp endpoint constant
  have hkey : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
        (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
    intro θ hθ
    have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo θ (Real.pi / 2))
      measurableSet_Ioo
      (w := Work.FTS.EllipticEst.thEta) (g := fun t => deriv f t)
      (fun t ht => hEtaPos.1 t (hsub ht))
      (hEtaPos.2.2.2.mono hsub)
      ((hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub)
      (hint.mono_set hsub)
      (hEtaInv.2.2.1 θ hθ)
    have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
    rw [hc θ hθ, neg_sq]
    calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left (hEtaInv.2.2.2 θ hθ) hAnn
      _ = 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  -- ## Monotonicity of the energy
  have hAtot0 : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hmono : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    · filter_upwards with t ht
      exact ⟨lt_trans hθ.1 ht.1, ht.2⟩
  -- ## The boundary constant is the limit, which is `0`
  have hboundTot : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ (2 * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
        * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) := by
    intro θ hθ
    have hpos : 0 ≤ (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) :=
      Real.rpow_nonneg (by linarith [hθ.2]) _
    calc (f θ - c) ^ 2 ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := hkey θ hθ
      _ ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_le_mul_of_nonneg_left (hmono θ hθ) (mul_nonneg (by norm_num) hpos)
      _ = (2 * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
          * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) := by ring
  have hp : 0 < 1 + Work.Spaces.eta := by linarith
  have hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) :=
    (Work.FTS.EllipticEst.TT.sqBoundTendstoPos (p := 1 + Work.Spaces.eta) hp).2 f c
      (2 * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
      (by linarith) hboundTot
  have hc0 : c = 0 := tendsto_nhds_unique hlim h1
  -- ## Conclusion
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  intro θ hθ
  have h := hkey θ hθ
  rw [hc0, sub_zero] at h
  have hbase : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
  have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg
        ⟨le_of_lt (lt_trans hθ.1 ht.1), le_of_lt ht.2⟩))
  have hsqrt_rpow : Real.sqrt ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
      = (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase]
    congr 1
    ring
  calc |f θ| = Real.sqrt ((f θ) ^ 2) := (Real.sqrt_sq_eq_abs (f θ)).symm
    _ ≤ Real.sqrt (2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := Real.sqrt_le_sqrt h
    _ = Real.sqrt 2 * Real.sqrt ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by
          rw [show 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
                (∫ t in Set.Ioo θ (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
              = 2 * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
                (∫ t in Set.Ioo θ (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) from by ring,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * (Real.sqrt ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by
          rw [Real.sqrt_mul (Real.rpow_nonneg hbase _)]
    _ = Real.sqrt 2 * ((Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by
          rw [hsqrt_rpow]
    _ = (Real.sqrt 2 * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
    _ ≤ (2 * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsqrt2 (Real.rpow_nonneg hbase _)) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) := by ring

end Work.FTS.EllipticEst.remov.AeNj
