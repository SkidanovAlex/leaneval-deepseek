import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `T45Common` — the common slot estimate for the row `T45aRow`

For every leaf weight `ρ = w²·σ` of the slot `(a,b)`, the pairing
`slotPairing ρ a b (L₁₂ f · A) f` is bounded by `C_A√D(10⁷C_L+1)/2 · K·α^{-1/2}(1+|f|²_{ℋ⁶})`.
This is the body of the proof of `T45aRow`, factored out so that the three leaf weights can be
dispatched by instantiation.
-/

/-- **The common slot estimate.** -/
theorem T45common {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {f A : ℝ → ℝ → ℝ} {a b : ℕ}
    {ρ : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} {K CA CL D : ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hm6 : Work.Spaces.HkMem α 6 f)
    (hCL0 : 0 ≤ CL) (hCA0 : 0 ≤ CA) (hD0 : 0 ≤ D) (hK0 : 0 ≤ K)
    (hHknn : 0 ≤ Work.Spaces.HkSq α 6 f)
    (hAop : ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CA * K * Abnd α i θ)
    (hρσ : ∀ z θ : ℝ, ρ z θ = (Work.Spaces.w z) ^ 2 * σ θ)
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hσint : MeasureTheory.IntegrableOn (fun θ => σ θ * (Abnd α a θ) ^ 2) Work.Spaces.Iθ)
    (hσbd : (∫ θ in Work.Spaces.Iθ, σ θ * (Abnd α a θ) ^ 2) ≤ D * α ^ (-(1 : ℝ)))
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hab : a + b ≤ 6) (hb : b ≤ 6)
    (hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (hXint : ∀ k : ℕ, k ≤ 6 → MeasureTheory.IntegrableOn (fun z =>
        (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (hXbd : ∀ k : ℕ, k ≤ 6 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ CL * Work.Spaces.HkSq α 6 f)
    (hXaesm : ∀ k : ℕ, k ≤ 6 → AEStronglyMeasurable (fun z =>
        Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
        (volume.restrict Work.Spaces.Iz)) :
    |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => Work.Construction.L12 f z * A z θ) f|
      ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨hSWint, hSWbd⟩ := SW_bound (α := α) (f := f) (CL := CL) hCL0 (b := b) hb
    (X := fun k z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
    hXint hXbd hXaesm
  have hApt : ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CA * K * Abnd α i θ :=
    fun j i hji z θ hz h1 h2 => hAop j i hji z θ hz h1 h2
  have hρnnIθ : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ := fun z θ hθ => by
    rw [hρσ z θ]; exact mul_nonneg (sq_nonneg _) (hσnn θ hθ)
  -- ## the `Λ²`-bound
  have hLamBd : (∫ z in Work.Spaces.Iz,
      (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) ^ 2)
      ≤ Work.Spaces.HkSq α 6 f := by
    have h1 : (∫ z in Work.Spaces.Iz,
        (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
        Real.sq_sqrt (MeasureTheory.integral_nonneg_of_ae
          (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
            mul_nonneg (hρnnIθ z θ hθ) (sq_nonneg _)))))
    rw [h1]
    exact (rhoV2_z hα0 hso hm6 hleaf hab).2
  -- ## the angular slice bound
  have hslice : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, ρ z θ *
          |Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * A z θ) z θ|
          * |Work.Spaces.mixed b a f z θ|)
        ≤ CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * (Work.Spaces.w z *
                (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
                  |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
                * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                    ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) := by
    intro z hz
    have hw : 0 < Work.Spaces.w z := w_pos_of_pos hz
    -- the pointwise coefficient bound
    have hcoe : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * A z θ) z θ|
          ≤ (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
            * (CA * K * Abnd α a θ) := by
      intro θ h1 h2
      have hleib := leibniz_radial_mul hXsm hAso b a hb z θ hz h1 h2
      rw [hleib]
      have hbd : ∀ k ∈ Finset.range (b + 1),
          |Work.Spaces.mixed (b - k) a A z θ| ≤ CA * K * Abnd α a θ := by
        intro k hk
        have hk' : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact hApt (b - k) a (by omega) z θ hz h1 h2
      calc |∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
            (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
              * Work.Spaces.mixed (b - k) a A z θ)|
          ≤ ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * |Work.Spaces.mixed (b - k) a A z θ|) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (b.choose k))]
        _ ≤ ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * (CA * K * Abnd α a θ)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hbd k hk) (abs_nonneg _)) (Nat.cast_nonneg _)
        _ = (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
              * (CA * K * Abnd α a θ) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k hk => by ring
    -- the a.e. pointwise bound for the integrand
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ρ z θ * |Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * A z θ) z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ CA * K * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
            * (ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|) := by
      filter_upwards [Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => hcoe θ h1 h2),
        ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hθ)] with θ hθ hθI
      have hρ0 : 0 ≤ ρ z θ := hρnnIθ z θ hθI
      calc ρ z θ * |Work.Spaces.mixed b a
              (fun z θ => Work.Construction.L12 f z * A z θ) z θ|
            * |Work.Spaces.mixed b a f z θ|
          ≤ ρ z θ * ((∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
                |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
              * (CA * K * Abnd α a θ)) * |Work.Spaces.mixed b a f z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hρ0) (abs_nonneg _)
        _ = CA * K * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
                |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
              * (ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|) := by ring
    -- integrability of the dominating function
    have hAbndInt : MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Abnd α a θ) ^ 2) Work.Spaces.Iθ := by
      have h1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
          (σ θ * (Abnd α a θ) ^ 2)) Work.Spaces.Iθ := hσint.const_mul _
      exact h1.congr_fun (fun θ hθ => by rw [hρσ z θ, mul_assoc]) measurableSet_Icc
    have hVint : MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ :=
      (rhoV2_slice hα0 hso hm6 hleaf hab hz).1
    have hAbsVint : MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono'
        ((hAbndInt.add hVint).const_mul (1 / 2)) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => ρ p.1 p.2 * Abnd α a p.2 *
            |Work.Spaces.mixed b a f p.1 p.2|) ?_ hz
        exact ((continuousOn_leaf hleaf).mul (continuousOn_Abnd α a)).mul
          (((hso.mixed b a).continuousOn).abs)
      · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        have hρ0 : 0 ≤ ρ z θ := hρnnIθ z θ hθ
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hρeq : ρ z θ = (Work.Spaces.w z) ^ 2 * σ θ := hρσ z θ
        have hsq : Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) = ρ z θ := Real.mul_self_sqrt hρ0
        have hxy : ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|
            = (Real.sqrt (ρ z θ) * Abnd α a θ)
              * (Real.sqrt (ρ z θ) * |Work.Spaces.mixed b a f z θ|) := by
          rw [show (Real.sqrt (ρ z θ) * Abnd α a θ)
              * (Real.sqrt (ρ z θ) * |Work.Spaces.mixed b a f z θ|)
              = (Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ)) * Abnd α a θ
                * |Work.Spaces.mixed b a f z θ| from by ring, hsq]
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hρ0 (Abnd_nonneg hα0 hθ a))
          (abs_nonneg _)), hxy]
        simp only [Pi.add_apply]
        have hnn : 0 ≤ (Real.sqrt (ρ z θ) * Abnd α a θ)
            * (Real.sqrt (ρ z θ) * |Work.Spaces.mixed b a f z θ|) :=
          mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Abnd_nonneg hα0 hθ a))
            (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        have h := abs_mul_le_half (Real.sqrt (ρ z θ) * Abnd α a θ)
          (Real.sqrt (ρ z θ) * |Work.Spaces.mixed b a f z θ|)
        rw [abs_of_nonneg hnn] at h
        have e1 : (Real.sqrt (ρ z θ) * Abnd α a θ) ^ 2
            = ρ z θ * (Abnd α a θ) ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ0]
        have e2 : (Real.sqrt (ρ z θ) * |Work.Spaces.mixed b a f z θ|) ^ 2
            = ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hρ0, sq_abs]
        rw [e1, e2] at h
        linarith [h]
    have hint : MeasureTheory.IntegrableOn (fun θ => CA * K *
        (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
        * (ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|)) Work.Spaces.Iθ :=
      hAbsVint.const_mul _
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (mul_nonneg (hρnnIθ z θ hθ) (abs_nonneg _)) (abs_nonneg _)))
      hint hpt
    -- the Cauchy–Schwarz chain on the angular slice
    have hBint : MeasureTheory.IntegrableOn
        (fun θ => σ θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
      have h1 : MeasureTheory.IntegrableOn (fun θ => (((Work.Spaces.w z) ^ 2)⁻¹) *
          (ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) Work.Spaces.Iθ := hVint.const_mul _
      exact h1.congr_fun (fun θ hθ => by
        show ((Work.Spaces.w z) ^ 2)⁻¹ * (ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
            = σ θ * (Work.Spaces.mixed b a f z θ) ^ 2
        rw [hρσ z θ, mul_assoc,
          inv_mul_cancel_left₀ (pow_ne_zero 2 (ne_of_gt hw))]) measurableSet_Icc
    have hAbndVeq : (∫ θ in Work.Spaces.Iθ,
          ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            Real.sqrt (σ θ * (Abnd α a θ) ^ 2)
              * Real.sqrt (σ θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae
        (Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_))
      show ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|
          = (Work.Spaces.w z) ^ 2 * (Real.sqrt (σ θ * (Abnd α a θ) ^ 2)
              * Real.sqrt (σ θ * (Work.Spaces.mixed b a f z θ) ^ 2))
      have hσ0 : 0 ≤ σ θ := hσnn θ ⟨le_of_lt h1, le_of_lt h2⟩
      calc ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|
          = (Work.Spaces.w z) ^ 2 * σ θ * Abnd α a θ
              * |Work.Spaces.mixed b a f z θ| := by rw [hρσ z θ]
        _ = (Work.Spaces.w z) ^ 2 * (Real.sqrt (σ θ) * Abnd α a θ)
              * (Real.sqrt (σ θ) * |Work.Spaces.mixed b a f z θ|) := by
            rw [show (Work.Spaces.w z) ^ 2 * (Real.sqrt (σ θ) * Abnd α a θ)
                  * (Real.sqrt (σ θ) * |Work.Spaces.mixed b a f z θ|)
                = (Work.Spaces.w z) ^ 2 * (Real.sqrt (σ θ) * Real.sqrt (σ θ))
                  * Abnd α a θ * |Work.Spaces.mixed b a f z θ| from by ring,
              Real.mul_self_sqrt hσ0]
        _ = (Work.Spaces.w z) ^ 2 * (Real.sqrt (σ θ * (Abnd α a θ) ^ 2)
              * Real.sqrt (σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)) := by
            rw [Real.sqrt_mul hσ0, Real.sqrt_sq_eq_abs, Real.sqrt_mul hσ0,
              Real.sqrt_sq_eq_abs, abs_of_nonneg (Abnd_nonneg hα0 ⟨le_of_lt h1, le_of_lt h2⟩ a)]
            ring
    have hCS : (∫ θ in Work.Spaces.Iθ, Real.sqrt (σ θ * (Abnd α a θ) ^ 2)
          * Real.sqrt (σ θ * (Work.Spaces.mixed b a f z θ) ^ 2))
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, σ θ * (Abnd α a θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              σ θ * (Work.Spaces.mixed b a f z θ) ^ 2) :=
      cs_sqrt_le_ae_Iθ hσint hBint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
          mul_nonneg (hσnn θ hθ) (sq_nonneg _)))
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
          mul_nonneg (hσnn θ hθ) (sq_nonneg _)))
    have hsqrt_bd : Real.sqrt (∫ θ in Work.Spaces.Iθ, σ θ * (Abnd α a θ) ^ 2)
        ≤ Real.sqrt (D * α ^ (-(1 : ℝ))) := Real.sqrt_le_sqrt hσbd
    -- the `σ`-integral as `w⁻¹` times `Λ`
    have hLamEq : (Work.Spaces.w z) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        = Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              σ θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => ?_)
        show ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
            = (Work.Spaces.w z) ^ 2 * (σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        rw [hρσ z θ, mul_assoc]
      rw [h1, Real.sqrt_mul (sq_nonneg (Work.Spaces.w z)), Real.sqrt_sq (le_of_lt hw)]
    -- assembly of the slice bound
    have hsliceBV : (∫ θ in Work.Spaces.Iθ,
          ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|)
        ≤ Work.Spaces.w z * Real.sqrt (D * α ^ (-(1 : ℝ)))
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by
      rw [hAbndVeq]
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              Real.sqrt (σ θ * (Abnd α a θ) ^ 2)
                * Real.sqrt (σ θ * (Work.Spaces.mixed b a f z θ) ^ 2))
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, σ θ * (Abnd α a θ) ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
        _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sqrt (D * α ^ (-(1 : ℝ)))
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsqrt_bd (Real.sqrt_nonneg _)) (sq_nonneg _)
        _ = Work.Spaces.w z * Real.sqrt (D * α ^ (-(1 : ℝ)))
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by
            rw [show (Work.Spaces.w z) ^ 2 * (Real.sqrt (D * α ^ (-(1 : ℝ)))
                  * Real.sqrt (∫ θ in Work.Spaces.Iθ, σ θ * (Work.Spaces.mixed b a f z θ) ^ 2))
                = (Work.Spaces.w z * Real.sqrt (D * α ^ (-(1 : ℝ))))
                  * (Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                      σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)) from by ring, hLamEq]
    calc (∫ θ in Work.Spaces.Iθ, ρ z θ *
          |Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * A z θ) z θ|
          * |Work.Spaces.mixed b a f z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, CA * K *
            (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
            * (ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|) := hmono
      _ = CA * K * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
            * (∫ θ in Work.Spaces.Iθ, ρ z θ * Abnd α a θ * |Work.Spaces.mixed b a f z θ|) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ CA * K * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
              |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
            * (Work.Spaces.w z * Real.sqrt (D * α ^ (-(1 : ℝ)))
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsliceBV
            (mul_nonneg (mul_nonneg hCA0 hK0)
              (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))
      _ = CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * (Work.Spaces.w z * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
                  |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
                * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                    ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) := by ring
  -- ## the radial integration
  have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, ρ z θ *
        |Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * A z θ) z θ|
        * |Work.Spaces.mixed b a f z θ|)
      ≤ CA * K * Real.sqrt (D * α ^ (-(1 : ℝ))) * (Work.Spaces.w z *
          (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
            |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · subst h0
      have hρ0 : ∀ θ : ℝ, ρ 0 θ = 0 := fun θ => by
        rw [hρσ 0 θ, Work.Spaces.w]
        norm_num
      have hz0 : (fun θ : ℝ => ρ 0 θ *
            |Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * A z θ) 0 θ|
            * |Work.Spaces.mixed b a f 0 θ|) = fun _ => (0 : ℝ) := by
        funext θ; rw [hρ0 θ]; ring
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      rw [hz0, integral_zero, hw0]
      simp
    · exact hslice z h0
  set SWz : ℝ → ℝ := fun z => ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) *
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| with hSWz
  set Lamz : ℝ → ℝ := fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
      ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) with hLamz
  have hLamInt : MeasureTheory.IntegrableOn (fun z => (Lamz z) ^ 2) Work.Spaces.Iz := by
    refine (rhoV2_z hα0 hso hm6 hleaf hab).1.congr ?_
    filter_upwards with z
    rw [hLamz]
    exact (Real.sq_sqrt (MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (hρnnIθ z θ hθ) (sq_nonneg _))))).symm
  have hhLamBd : (∫ z in Work.Spaces.Iz, (Lamz z) ^ 2) ≤ Work.Spaces.HkSq α 6 f := hLamBd
  have hSWint2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z * SWz z) ^ 2)
      Work.Spaces.Iz := by
    refine hSWint.congr ?_
    filter_upwards with z
    rw [hSWz]
    ring
  have hSWnn : ∀ z : ℝ, 0 ≤ SWz z := fun z => by
    rw [hSWz]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hSWbd2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * SWz z) ^ 2)
      ≤ 10000000 * CL * Work.Spaces.HkSq α 6 f := by
    have h1 := hSWbd
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by
      show (Work.Spaces.w z) ^ 2 * (SWz z) ^ 2 = (Work.Spaces.w z * SWz z) ^ 2
      ring)] at h1
    exact h1
  have hc0 : 0 ≤ CA * K * Real.sqrt (D * α ^ (-(1 : ℝ))) :=
    mul_nonneg (mul_nonneg hCA0 hK0) (Real.sqrt_nonneg _)
  have hdom : MeasureTheory.IntegrableOn
      (fun z => CA * K * Real.sqrt (D * α ^ (-(1 : ℝ))) * (Work.Spaces.w z * SWz z * Lamz z))
      Work.Spaces.Iz := by
    have hmaj : Integrable (fun z => CA * K * Real.sqrt (D * α ^ (-(1 : ℝ))) *
        ((1 / 2) * (Work.Spaces.w z * SWz z) ^ 2 + (1 / 2) * (Lamz z) ^ 2))
        (volume.restrict Work.Spaces.Iz) :=
      ((hSWint2.const_mul (1 / 2)).add (hLamInt.const_mul (1 / 2))).const_mul _
    refine hmaj.mono' ?_ ?_
    · have hSWaesm : AEStronglyMeasurable SWz (volume.restrict Work.Spaces.Iz) := by
        rw [hSWz]
        exact aesm_finset_sum_loc _ (fun k hk => (((hXaesm k (le_trans
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hb)).norm).congr
            (Filter.Eventually.of_forall fun z => Real.norm_eq_abs _)).const_mul _)
      have hLamAESM : AEStronglyMeasurable Lamz (volume.restrict Work.Spaces.Iz) := by
        rw [hLamz]
        exact Real.continuous_sqrt.comp_aestronglyMeasurable
          ((Work.Spaces.aesm_of_continuousOn_Qd _
            ((continuousOn_leaf hleaf).mul (((hso.mixed b a).continuousOn).pow 2)))
              |>.integral_prod_right')
      exact (((measurable_w.aestronglyMeasurable).mul hSWaesm).mul hLamAESM).const_mul _
    · filter_upwards with z
      rw [Real.norm_of_nonneg]
      · exact mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg (Work.Spaces.w z * SWz z - Lamz z), sq_nonneg (Lamz z)])
          hc0
      · exact mul_nonneg hc0 (mul_nonneg (mul_nonneg (w_nonneg z) (hSWnn z))
          (Real.sqrt_nonneg _))
  have hrpow_sqrt : Real.sqrt (α ^ (-(1 : ℝ))) = α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hα0.le]
    norm_num
  have hstep2 : (∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
          * (Work.Spaces.w z * SWz z * Lamz z))
      ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hAM4 : (∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
          * (Work.Spaces.w z * SWz z * Lamz z))
        ≤ ∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * ((1 / 2) * (Work.Spaces.w z * SWz z) ^ 2 + (1 / 2) * (Lamz z) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z =>
          mul_nonneg hc0 (mul_nonneg (mul_nonneg (w_nonneg z) (hSWnn z))
            (Real.sqrt_nonneg _)))
        (((hSWint2.const_mul (1 / 2)).add (hLamInt.const_mul (1 / 2))).const_mul _) ?_
      filter_upwards with z
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (Work.Spaces.w z * SWz z - Lamz z), sq_nonneg (Lamz z)]) hc0
    have hEval : (∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * ((1 / 2) * (Work.Spaces.w z * SWz z) ^ 2 + (1 / 2) * (Lamz z) ^ 2))
        = CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
          * ((1 / 2) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * SWz z) ^ 2)
            + (1 / 2) * (∫ z in Work.Spaces.Iz, (Lamz z) ^ 2)) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hSWint2.const_mul (1 / 2)) (hLamInt.const_mul (1 / 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    calc (∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
          * (Work.Spaces.w z * SWz z * Lamz z))
        ≤ ∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * ((1 / 2) * (Work.Spaces.w z * SWz z) ^ 2 + (1 / 2) * (Lamz z) ^ 2) := hAM4
      _ = CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * ((1 / 2) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * SWz z) ^ 2)
              + (1 / 2) * (∫ z in Work.Spaces.Iz, (Lamz z) ^ 2)) := hEval
      _ ≤ CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
            * ((1 / 2) * (10000000 * CL * Work.Spaces.HkSq α 6 f)
              + (1 / 2) * Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          exact add_le_add (mul_le_mul_of_nonneg_left hSWbd2 (by norm_num))
            (mul_le_mul_of_nonneg_left hhLamBd (by norm_num))
      _ = CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          rw [Real.sqrt_mul hD0, hrpow_sqrt]
          ring
      _ ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
            * (1 + Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_left (by linarith [hHknn]) ?_
          have hp1 : 0 ≤ CA * Real.sqrt D := mul_nonneg hCA0 (Real.sqrt_nonneg _)
          have hp2 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) :=
            mul_nonneg hp1 (by linarith [hCL0])
          have hp3 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 := by positivity
          exact mul_nonneg (mul_nonneg hp3 hK0) (Real.rpow_nonneg hα0.le _)
  have hstep1 : |Work.FTS.TransportS.slotPairing ρ a b
      (fun z θ => Work.Construction.L12 f z * A z θ) f|
      ≤ (∫ z in Work.Spaces.Iz, CA * K * Real.sqrt (D * α ^ (-(1 : ℝ)))
          * (Work.Spaces.w z * SWz z * Lamz z)) := by
    rw [Work.FTS.TransportS.slotPairing]
    refine (abs_integral_le_integral_abs).trans ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
      hdom (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_))
    refine (abs_integral_le_integral_abs).trans ?_
    refine (MeasureTheory.integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => by rw [abs_mul, abs_mul, abs_of_nonneg (hρnnIθ z θ hθ)]))).le.trans ?_
    exact hinner z hz
  exact hstep1.trans hstep2

end Work.FTS.StrongPersist.H6Pair6Aux
