import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroCutoff
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.HonestHardSlotLem
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.BSlotTop.GsumBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The source slot bounded by `HkSq α k F` alone**, from `srcBoundFts` (the reduction form),
the `A`-slot bound `A_top_slot_bound`, and the two hypotheses of the induction step. -/
theorem Gsum_bound_fts (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F) →
      (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F) →
      GsumC α k F Ψ ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  obtain ⟨Cs, hCspos, hsrc⟩ := srcBoundFts D hD k hk
  obtain ⟨CA, hCApos, hA⟩ := Work.FTS.EllipticEst.remov.A_top_slot_bound D hD k hk
  refine ⟨Cs * (1 + CA ^ 2 + 2 * D ^ 2), by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have hTkA : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ CA ^ 2 * Work.Spaces.HkSq α k F := by
    have hAnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg α k _
    have hA' := hA α F Ψ hα hα4 hwk h1 h2
    calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        = (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hAnn]; ring
      _ ≤ (CA * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)) hA' 2
      _ = CA ^ 2 * Work.Spaces.HkSq α k F := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hAcase : α ^ 4 * Work.Spaces.HkSq α (k - 1)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hb : 0 ≤ Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
      Work.Spaces.HkNorm_nonneg α (k - 1) _
    have h1' : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ D * Work.Spaces.HkNorm α k F := by
      linarith [h1]
    calc α ^ 4 * Work.Spaces.HkSq α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        = (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) _)]
          ring
      _ ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (sq_nonneg α)
            (Work.Spaces.HkNorm_nonneg α (k - 1) _)) h1' 2
      _ = D ^ 2 * Work.Spaces.HkSq α k F := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hDzBcase : Work.Spaces.HkSq α (k - 1)
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hb : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α (k - 1) _)
    have h2' : Work.Spaces.HkNorm α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) ≤ D * Work.Spaces.HkNorm α k F := by
      linarith [h2]
    calc Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        = (Work.Spaces.HkNorm α (k - 1)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))) ^ 2 := by
          rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) _)]
      _ ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1) _) h2' 2
      _ = D ^ 2 * Work.Spaces.HkSq α k F := by
          rw [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
  have hmain := hsrc α F Ψ hα hα4 hwk h1 h2
  calc GsumC α k F Ψ
      ≤ Cs * (Work.Spaces.HkSq α k F
          + α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                z θ * Work.Spaces.Wt α z θ) ^ 2)
          + Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          + α ^ 4 * Work.Spaces.HkSq α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := hmain
    _ ≤ Cs * ((1 + CA ^ 2 + 2 * D ^ 2) * Work.Spaces.HkSq α k F) := by
        refine mul_le_mul_of_nonneg_left ?_ hCspos.le
        have hTkA' : α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              z θ * Work.Spaces.Wt α z θ) ^ 2) ≤ CA ^ 2 * Work.Spaces.HkSq α k F := hTkA
        linarith [hTkA', hAcase, hDzBcase]
    _ = (Cs * (1 + CA ^ 2 + 2 * D ^ 2)) * Work.Spaces.HkSq α k F := by ring

end Work.FTS.EllipticEst.Prop.BSlotTop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.BSlotTop.SliceAngGenFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- On `Iθ` the weight `sin(2θ)` is nonnegative. -/
private lemma sin_two_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin(2θ)` is positive on the open interval. -/
private lemma sin_two_pos_Ioo_fts {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `Ioo 0 (π/2)` is co-null in `volume.restrict Iθ`. -/
private lemma haeIoo_fts :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

private lemma angRHS_nonneg_fts (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    0 ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨hA, hB, hC, hD⟩ := Work.FTS.EllipticEst.remov.angRHS_rest_nonneg k γ u g
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _))
  rw [Work.FTS.EllipticEst.remov.angSlot_AngRHS_unfold]
  linarith

/-- The `H4`-slot of `AngRHS` is bounded by `AngRHS`. -/
private lemma h4slot_le_angRHS_fts (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨hA, hB, hC, hD⟩ := Work.FTS.EllipticEst.remov.angRHS_rest_nonneg k γ u g
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _))
  rw [Work.FTS.EllipticEst.remov.angSlot_AngRHS_unfold]
  linarith

/-- A single `H3`-slot of `AngRHS` is bounded by `AngRHS`. -/
private lemma h3slot_le_angRHS_fts {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} {j : ℕ}
    (hj : j ∈ Finset.Icc 3 (k + 1)) :
    (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨hA, hB, hC, hD⟩ := Work.FTS.EllipticEst.remov.angRHS_rest_nonneg k γ u g
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _))
  have hsingle : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
      ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j' u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.single_le_sum (f := fun j' => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j' u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ))
      (fun j' _ => MeasureTheory.setIntegral_nonneg
        (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _)))
      hj
  rw [Work.FTS.EllipticEst.remov.angSlot_AngRHS_unfold]
  linarith

/-- **The final assembly of the one-dimensional angular estimate.** -/
theorem sliceAngGenFinalFts (k : ℕ) (hk : 2 ≤ k)
    (hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g → ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨Cv, hCvpos, hVb⟩ := hV
  set CM : ℝ := ((k : ℝ) + 2) * (2 : ℝ) ^ (2 * (k + 1)) with hCMdef
  have hCMnn : 0 ≤ CM := by rw [hCMdef]; positivity
  refine ⟨3 * (CM * ((k : ℝ) + 2) * Cv + 37), by positivity, ?_⟩
  intro γ u g h
  obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hIk2, hIgk, hIhigh, hI2, hI1, hI0⟩ := h
  set v : ℝ → ℝ := fun t => u t / Real.cos t with hvdef
  have hSlice : Work.FTS.EllipticEst.remov.SliceHyp k γ u g :=
    ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hIk2, hIgk, hIhigh, hI2, hI1, hI0⟩
  have hv_cd : ContDiffOn ℝ (k + 2) v (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hvdef]
    exact Work.FTS.EllipticEst.remov.TopCoreB.contDiffOn_vF hu
  have hv_cdAt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffAt ℝ (k + 2) v θ := fun θ hθ =>
    hv_cd.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hRnn : 0 ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := angRHS_nonneg_fts k γ u g
  -- ## the `u^{(k)}`-slot majorant
  have hSk : ∃ Sk : ℝ → ℝ, MeasureTheory.IntegrableOn Sk Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, Sk θ) ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g
      ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ Sk θ := by
    rcases eq_or_lt_of_le hk with hk2 | hk3
    · subst hk2
      refine ⟨fun θ => (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)), hI2, ?_, ?_⟩
      · exact h4slot_le_angRHS_fts 2 γ u g
      · intro θ hθ
        have h2e : iteratedDeriv 2 u θ = deriv (deriv u) θ := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
        rw [h2e]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_Ioo_fts hθ) (Real.sin_le_one _) ?_
        have heta := Work.Spaces.eta_pos
        have hcast : 2 * ((2 : ℕ) : ℝ) = 4 := by norm_num
        rw [hcast]
        have : Work.Spaces.eta ≤ 4 - γ := by
          rw [show Work.Spaces.eta = 99 / 100 from rfl]; linarith
        linarith [heta, this]
    · refine ⟨fun θ => (iteratedDeriv k u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - 4 - γ),
        hIhigh k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), ?_, ?_⟩
      · exact h3slot_le_angRHS_fts (k := k) (γ := γ) (u := u) (g := g)
          (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · intro θ hθ
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_Ioo_fts hθ) (Real.sin_le_one _) ?_
        linarith
  obtain ⟨Sk, hSkint, hSkbd, hSkmaj⟩ := hSk
  -- ## the pointwise Leibniz bound
  have hlevB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2
        ≤ CM * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 := by
    intro θ hθ
    have hev : (fun t => Real.tan t * u t) =ᶠ[𝓝 θ] (Real.sin * v) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      have hct : Real.cos t ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      simp only [Pi.mul_apply, hvdef]
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have h1 : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        = iteratedDeriv (k + 1) (Real.sin * v) θ :=
      Filter.EventuallyEq.iteratedDeriv_eq _ hev
    rw [h1]
    have hcd_sin : ContDiffAt ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) Real.sin θ :=
      (Real.contDiff_sin (n := (((k + 1 : ℕ)) : WithTop ℕ∞))).contDiffAt
    have hcd_v : ContDiffAt ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) v θ :=
      (hv_cdAt θ hθ).of_le
        (by exact_mod_cast (Nat.le_succ (k + 1) : k + 1 ≤ k + 2))
    have hlev := iteratedDeriv_mul hcd_sin hcd_v
    rw [hlev]
    have habs : |∑ i ∈ Finset.range (k + 2), (((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.sin θ * iteratedDeriv (k + 1 - i) v θ)|
        ≤ ∑ i ∈ Finset.range (k + 2),
            (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro i _
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((k + 1).choose i : ℕ) : ℝ))]
      have hs := Work.FTS.EllipticEst.remov.TopCoreB.abs_iteratedDeriv_sin_le_one i θ
      have hch : (((k + 1).choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        have := Work.FTS.EllipticEst.remov.TopCoreB.choose_le_two_pow (k + 1) i
        exact_mod_cast this
      calc (((k + 1).choose i : ℕ) : ℝ) * |iteratedDeriv i Real.sin θ|
            * |iteratedDeriv (k + 1 - i) v θ|
          ≤ (2 : ℝ) ^ (k + 1) * 1 * |iteratedDeriv (k + 1 - i) v θ| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul hch hs (abs_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ| := by ring
    have hstep1 : (∑ i ∈ Finset.range (k + 2), (((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.sin θ * iteratedDeriv (k + 1 - i) v θ)) ^ 2
        ≤ (∑ i ∈ Finset.range (k + 2),
            (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa only [sq_abs] using h
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 2))
      (f := fun i => (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|)
    have hreindex : (∑ i ∈ Finset.range (k + 2),
          ((2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2)
        = (2 : ℝ) ^ (2 * (k + 1)) * ∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2 := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_range_reflect (fun m => (2 : ℝ) ^ (2 * (k + 1))
        * (iteratedDeriv m v θ) ^ 2) (k + 2)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hidx : k + 2 - 1 - i = k + 1 - i := by omega
      rw [hidx]
      have hsq2 : ((2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2
          = (2 : ℝ) ^ (2 * (k + 1)) * (iteratedDeriv (k + 1 - i) v θ) ^ 2 := by
        rw [mul_pow, sq_abs]
        rw [show ((2 : ℝ) ^ (k + 1)) ^ 2 = (2 : ℝ) ^ (2 * (k + 1)) from by
          rw [← pow_mul]; congr 1; ring]
      rw [hsq2]
    calc (∑ i ∈ Finset.range (k + 2), (((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.sin θ * iteratedDeriv (k + 1 - i) v θ)) ^ 2
        ≤ (∑ i ∈ Finset.range (k + 2),
            (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2 := hstep1
      _ ≤ ((Finset.range (k + 2)).card : ℝ)
            * ∑ i ∈ Finset.range (k + 2),
              ((2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2 := hsq
      _ = ((k : ℝ) + 2) * ((2 : ℝ) ^ (2 * (k + 1))
            * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) := by
          rw [Finset.card_range, hreindex]; push_cast; ring
      _ = CM * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 := by
          rw [hCMdef]; ring
  -- ## the pointwise bound for the top slot
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ 3 * (CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2)
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + 36 * Sk θ
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
    intro θ hθ
    have hode := Work.FTS.EllipticEst.remov.ang_ode_iterate k hu hg θ hθ
    have hlb := hlevB θ hθ
    have hSkb := hSkmaj θ hθ
    set qθ : ℝ := Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) with hqθdef
    have hqnn : 0 ≤ qθ := by
      rw [hqθdef]; exact Real.rpow_nonneg (le_of_lt (sin_two_pos_Ioo_fts hθ)) _
    have hsq : (iteratedDeriv (k + 2) u θ) ^ 2
        ≤ 3 * ((iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2
            + 36 * (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) := by
      have h : iteratedDeriv (k + 2) u θ
          = iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
            + (-(6 * iteratedDeriv k u θ)) + (-(iteratedDeriv k g θ)) := by linarith
      have h3 := sq_three_le (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ)
        (-(6 * iteratedDeriv k u θ)) (-(iteratedDeriv k g θ))
      rw [h]
      nlinarith [h3, sq_nonneg (iteratedDeriv k u θ), sq_nonneg (iteratedDeriv k g θ)]
    have hchain : (iteratedDeriv (k + 2) u θ) ^ 2 * qθ
        ≤ 3 * (CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ)
            + 36 * Sk θ
            + (iteratedDeriv k g θ) ^ 2 * qθ) := by
      refine le_trans (mul_le_mul_of_nonneg_right hsq hqnn) ?_
      have hkey : CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ)
          + 36 * ((iteratedDeriv k u θ) ^ 2 * qθ)
          + (iteratedDeriv k g θ) ^ 2 * qθ
          ≤ CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ)
            + 36 * Sk θ
            + (iteratedDeriv k g θ) ^ 2 * qθ := by
        have h4 : 36 * ((iteratedDeriv k u θ) ^ 2 * qθ) ≤ 36 * Sk θ :=
          mul_le_mul_of_nonneg_left hSkb (by norm_num)
        linarith [h4]
      have h1 : (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2 * qθ
          ≤ CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ) := by
        have := mul_le_mul_of_nonneg_right hlb hqnn
        simpa only [mul_assoc] using this
      have hthis : 3 * ((iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2
            + 36 * (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) * qθ
          = 3 * ((iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2 * qθ
            + 36 * ((iteratedDeriv k u θ) ^ 2 * qθ)
            + (iteratedDeriv k g θ) ^ 2 * qθ) := by ring
      rw [hthis]
      nlinarith [hkey, h1]
    exact hchain
  -- ## the majorant and its integrability
  have hsumInt : MeasureTheory.IntegrableOn (fun θ => (∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      Work.Spaces.Iθ := by
    rw [show (fun θ => (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2)
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        = fun θ => ∑ m ∈ Finset.range (k + 2), ((iteratedDeriv m v θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) from by
      funext θ; rw [Finset.sum_mul]]
    exact MeasureTheory.integrable_finset_sum _ (fun m hm =>
      (hVb γ u g hSlice m (by have := Finset.mem_range.mp hm; omega)).1)
  have hIF1 : MeasureTheory.IntegrableOn (fun θ => CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
      Work.Spaces.Iθ := hsumInt.const_mul CM
  have hIF2 : MeasureTheory.IntegrableOn (fun θ => CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ) Work.Spaces.Iθ := hIF1.add (hSkint.const_mul 36)
  have hIF3 : MeasureTheory.IntegrableOn (fun θ => CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ := hIF2.add hIgk
  have hMajInt : MeasureTheory.IntegrableOn (fun θ => 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) Work.Spaces.Iθ := hIF3.const_mul 3
  have hmain : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
          (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (haeIoo_fts.mono fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos_Ioo_fts hθ)) _))
      hMajInt
      (haeIoo_fts.mono fun θ hθ => hpt θ hθ)
  -- ## evaluating the majorant
  have hsumEval : (∫ θ in Work.Spaces.Iθ, (∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = ∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      rw [Finset.sum_mul])]
    exact MeasureTheory.integral_finsetSum _ (fun m hm =>
      (hVb γ u g hSlice m (by have := Finset.mem_range.mp hm; omega)).1)
  have hsumEval' : (∫ θ in Work.Spaces.Iθ, (∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = ∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := hsumEval
  have hsumBd : (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ ((k : ℝ) + 2) * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
    calc (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∑ _m ∈ Finset.range (k + 2), Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
          Finset.sum_le_sum fun m hm =>
            (hVb γ u g hSlice m (by have := Finset.mem_range.mp hm; omega)).2
      _ = ((Finset.range (k + 2)).card : ℝ)
            * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((k : ℝ) + 2) * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
          rw [Finset.card_range]; push_cast; ring
  have hval : (∫ θ in Work.Spaces.Iθ, 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
      = 3 * (CM * (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * (∫ θ in Work.Spaces.Iθ, Sk θ)
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (CM * ((∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = (∫ θ in Work.Spaces.Iθ, (CM * ((∑ m ∈ Finset.range (k + 2),
              (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + 36 * Sk θ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
      MeasureTheory.integral_add hIF2 hIgk
    have h2 : (∫ θ in Work.Spaces.Iθ, (CM * ((∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * Sk θ))
        = (∫ θ in Work.Spaces.Iθ, CM * ((∑ m ∈ Finset.range (k + 2),
              (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          + (∫ θ in Work.Spaces.Iθ, 36 * Sk θ) :=
      MeasureTheory.integral_add hIF1 (hSkint.const_mul 36)
    have h3 : (∫ θ in Work.Spaces.Iθ, CM * ((∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = CM * (∫ θ in Work.Spaces.Iθ, (∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
      MeasureTheory.integral_const_mul CM _
    have h4 : (∫ θ in Work.Spaces.Iθ, 36 * Sk θ) = 36 * (∫ θ in Work.Spaces.Iθ, Sk θ) :=
      MeasureTheory.integral_const_mul 36 _
    rw [MeasureTheory.integral_const_mul, h1, h2, h3, h4, hsumEval]
  -- ## the final estimate
  have hgbd : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
    Work.FTS.EllipticEst.remov.g_slot_le_angRHS k γ u g
  calc (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
          (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := hmain
    _ = 3 * (CM * (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * (∫ θ in Work.Spaces.Iθ, Sk θ)
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := hval
    _ ≤ 3 * (CM * (((k : ℝ) + 2) * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g))
          + 36 * Work.FTS.EllipticEst.remov.AngRHS k γ u g
          + Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        nlinarith [hsumBd, hSkbd, hgbd, mul_nonneg hCMnn hRnn, hRnn]
    _ = (3 * (CM * ((k : ℝ) + 2) * Cv + 37)) * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
        ring
end Work.FTS.EllipticEst.Prop.BSlotTop
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.angBlk_sinSqGam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter
open Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux (AngBlk)

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


lemma volume_real_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

lemma volume_Iθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-! ## The profile `sin²θ·Γ` and the `C^∞`-regularity of its `D_θ`-jets on `(0,π/2)` -/

/-- The unnormalised profile `θ ↦ sin²θ·Γ(α,θ)`. -/
abbrev sinSqGam (α : ℝ) : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ

/-- `Γ(α,·) = (sinθ·cos²θ)^{α/3}` is `C^∞` (at the honest smooth order `∞`) on the open
angular interval `(0,π/2)`, where its base is strictly positive. -/
lemma gam_contDiffOn_Ioo (α : ℝ) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo 0 (Real.pi / 2)) := by
  show ContDiffOn ℝ ∞ (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
    (Set.Ioo 0 (Real.pi / 2))
  have hbase : ContDiffOn ℝ ∞ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.contDiff_sin (n := ∞)).contDiffOn).mul
      (((Real.contDiff_cos (n := ∞)).contDiffOn).pow 2)
  refine hbase.rpow_const_of_ne (fun θ hθ => ?_)
  have h1 : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩
  positivity

lemma sinSqGam_contDiffOn_Ioo (α : ℝ) :
    ContDiffOn ℝ ∞ (sinSqGam α) (Set.Ioo 0 (Real.pi / 2)) :=
  (((Real.contDiff_sin (n := ∞)).pow 2).contDiffOn).mul (gam_contDiffOn_Ioo α)

/-- `D_θ` preserves `C^∞`-regularity of a one-variable function on the open angular
interval. -/
lemma dthU_iter_contDiffOn_Ioo {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 (Real.pi / 2))) (i : ℕ) :
    ContDiffOn ℝ ∞ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2)) := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hsin : ContDiffOn ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by
        fun_prop
      exact hsin.mul (ih.deriv_of_isOpen isOpen_Ioo (by simp))

/-! ## `AngBlk` under a constant multiple -/

/-- `AngBlk` is quadratic in its profile argument. -/
lemma AngBlk_const_mul (α a : ℝ) (f : ℝ → ℝ) (θ : ℝ) :
    AngBlk α (fun θ => a * f θ) θ = a ^ 2 * AngBlk α f θ := by
  simp only [AngBlk, Work.Spaces.dthU_iter_const_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 1 ≤ i
    · simp only [h, if_true]; ring
    · simp only [h, if_false]; ring

/-! ## The pointwise bound -/

/-- **The pointwise bound.**  For `α ∈ (0,1]`, `θ ∈ Iθ` and any `B` witnessing the jet bound,
`AngBlk α (sin²·Γ)` is dominated by an explicit integrable majorant. -/
lemma angBlk_le_majorant {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {B : ℕ → ℝ}
    (hBnn : ∀ i, 0 ≤ B i)
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[i] (sinSqGam α) θ|
        ≤ Work.Spaces.Gam α θ * (α * 100000 + B i * (Real.sin (2 * θ)) ^ 2))
    (T : ℝ) (hT : T = ∑ i ∈ Finset.range 7, 2 * (B i) ^ 2)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    AngBlk α (sinSqGam α) θ
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)
        + T := by
  set s : ℝ := Real.sin (2 * θ) with hs
  have hs0 : 0 ≤ s := by rw [hs]; exact sin_two_nonneg_Iθ hθ
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hGnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hG2 : (Work.Spaces.Gam α θ) ^ 2 ≤ s ^ (2 * α / 3) := by
    rw [hs]; exact Work.Coercivity.Gam_sq_le_sin_two α hα θ hθ
  have hweta : 0 ≤ s ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
  have hwgam : 0 ≤ s ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hne1 : 2 * α / 3 + -(Work.Spaces.eta) ≠ 0 := by
    have hlt : 2 * α / 3 < Work.Spaces.eta := by
      rw [Work.Spaces.eta]; nlinarith [hα1]
    intro h; linarith
  have hne2 : 2 * α / 3 + -(Work.Spaces.gam α) ≠ 0 := by
    have hlt : 2 * α / 3 < Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; nlinarith [hα]
    intro h; linarith
  have hexp3 : 0 < 4 + (2 * α / 3 - Work.Spaces.gam α) := by
    rw [Work.Spaces.gam]; nlinarith [hα, hα1]
  have hne3 : 4 + (2 * α / 3 + -(Work.Spaces.gam α)) ≠ 0 := by
    intro h; linarith [hexp3]
  -- the two exponent identities
  have hcol1 : s ^ (2 * α / 3) * s ^ (-(Work.Spaces.eta))
      = s ^ (2 * α / 3 + -(Work.Spaces.eta)) := (Real.rpow_add' hs0 hne1).symm
  have hcol2 : s ^ (2 * α / 3) * s ^ (-(Work.Spaces.gam α))
      = s ^ (2 * α / 3 + -(Work.Spaces.gam α)) := (Real.rpow_add' hs0 hne2).symm
  -- the `i = 0` block
  have h0 : (sinSqGam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))
      ≤ s ^ (2 * α / 3 - Work.Spaces.eta) := by
    have hsin2 : Real.sin θ ^ 2 ≤ 1 := by
      have h := Real.abs_sin_le_one θ
      nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ), h]
    have hsin4 : Real.sin θ ^ 4 ≤ 1 := by
      nlinarith [hsin2, sq_nonneg (Real.sin θ ^ 2)]
    have hsq : (sinSqGam α θ) ^ 2 = Real.sin θ ^ 4 * (Work.Spaces.Gam α θ) ^ 2 := by
      simp only [sinSqGam]; ring
    calc (sinSqGam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))
        = Real.sin θ ^ 4 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))) := by
          rw [hsq]; ring
      _ ≤ 1 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hsin4 (mul_nonneg (sq_nonneg _) hweta)
      _ = (Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.eta)) := by ring
      _ ≤ s ^ (2 * α / 3) * s ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right hG2 hweta
      _ = s ^ (2 * α / 3 - Work.Spaces.eta) := hcol1
  -- the two key blocks for the `i ≥ 1` terms
  have hkey1 : (Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
      ≤ s ^ (2 * α / 3 - Work.Spaces.gam α) :=
    calc (Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
        ≤ s ^ (2 * α / 3) * s ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hG2 hwgam
      _ = s ^ (2 * α / 3 - Work.Spaces.gam α) := hcol2
  have hkey2 : s ^ 4 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α))) ≤ 1 := by
    have h4 : s ^ 4 = s ^ (4 : ℝ) := (Real.rpow_natCast s 4).symm
    have hcol4 : s ^ (4 : ℝ) * s ^ (2 * α / 3 + -(Work.Spaces.gam α))
        = s ^ (4 + (2 * α / 3 + -(Work.Spaces.gam α))) := (Real.rpow_add' hs0 hne3).symm
    calc s ^ 4 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α)))
        ≤ s ^ 4 * s ^ (2 * α / 3 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_left hkey1 (pow_nonneg hs0 4)
      _ = s ^ (4 : ℝ) * s ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [h4]
      _ = s ^ (4 + (2 * α / 3 - Work.Spaces.gam α)) := hcol4
      _ ≤ 1 := Real.rpow_le_one hs0 hs1 hexp3.le
  -- the per-`i` term bound
  have hterm : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
      (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
        ≤ 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2 := by
    intro i hi1 hi6
    have hb := hB i hi1 hi6 θ hθ
    simp only [← hs] at hb
    have hsq : (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
        ≤ (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hxy : (α * 100000 + B i * s ^ 2) ^ 2
        ≤ 2 * ((α * 100000) ^ 2 + (B i * s ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (α * 100000 - B i * s ^ 2)]
    have hstep : (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2
        ≤ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (α * 100000) ^ 2
            + (Work.Spaces.Gam α θ) ^ 2 * (B i) ^ 2 * s ^ 4) := by
      rw [show (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2
            = (Work.Spaces.Gam α θ) ^ 2 * (α * 100000 + B i * s ^ 2) ^ 2 by ring]
      calc (Work.Spaces.Gam α θ) ^ 2 * (α * 100000 + B i * s ^ 2) ^ 2
          ≤ (Work.Spaces.Gam α θ) ^ 2 * (2 * ((α * 100000) ^ 2 + (B i * s ^ 2) ^ 2)) :=
            mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
        _ = 2 * ((Work.Spaces.Gam α θ) ^ 2 * (α * 100000) ^ 2
              + (Work.Spaces.Gam α θ) ^ 2 * (B i) ^ 2 * s ^ 4) := by ring
    calc (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
        ≤ (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2
            * s ^ (-(Work.Spaces.gam α)) := mul_le_mul_of_nonneg_right hsq hwgam
      _ ≤ (2 * ((Work.Spaces.Gam α θ) ^ 2 * (α * 100000) ^ 2
              + (Work.Spaces.Gam α θ) ^ 2 * (B i) ^ 2 * s ^ 4))
            * s ^ (-(Work.Spaces.gam α)) := mul_le_mul_of_nonneg_right hstep hwgam
      _ = 2 * ((α * 100000) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α)))
            + (B i) ^ 2 * (s ^ 4 * ((Work.Spaces.Gam α θ) ^ 2
                * s ^ (-(Work.Spaces.gam α))))) := by ring
      _ ≤ 2 * ((α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + (B i) ^ 2 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hkey1 (sq_nonneg _))
            (mul_le_mul_of_nonneg_left hkey2 (sq_nonneg _))
      _ = 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2 := by
          ring
  -- the sum of the `i ≥ 1` terms
  have hsum : (∑ i ∈ Finset.range 7,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
          * s ^ (-(Work.Spaces.gam α)) else 0))
      ≤ 14 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + T := by
    have hstep1 : (∑ i ∈ Finset.range 7,
          (if 1 ≤ i then (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
        ≤ ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α)
              + 2 * (B i) ^ 2 else 0) := by
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h1 : 1 ≤ i
      · have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
        rw [if_pos h1, if_pos h1]
        exact hterm i h1 hi6
      · rw [if_neg h1, if_neg h1]
    have hstep2 : (∑ i ∈ Finset.range 7,
            (if 1 ≤ i then 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α)
              + 2 * (B i) ^ 2 else 0))
        ≤ ∑ i ∈ Finset.range 7,
            (2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1]
      · rw [if_neg h1]
        exact add_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)) (by positivity)
    have hstep3 : (∑ i ∈ Finset.range 7,
            (2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2))
        = 14 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + T := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hT]
      ring
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  -- assemble
  have hgoal : AngBlk α (sinSqGam α) θ
      = (sinSqGam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * s ^ (-(Work.Spaces.gam α)) else 0) := by
    simp only [AngBlk, ← hs]
  rw [hgoal]
  linarith [h0, hsum]

/-! ## The core uniform bound for the unnormalised profile -/

theorem angBlk_sinSqGam_bound : ∃ Bang0 : ℝ, 0 < Bang0 ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (fun θ => AngBlk α (sinSqGam α) θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, AngBlk α (sinSqGam α) θ) ≤ Bang0 := by
  -- the jet bound (local Leibniz + the two factor bounds)
  obtain ⟨B, hBnn, hB⟩ : ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[i] (sinSqGam α) θ|
          ≤ Work.Spaces.Gam α θ * (α * 100000 + B i * (Real.sin (2 * θ)) ^ 2) := by
    refine Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_Gfun_bound ?_
    intro β hβmem j hj6
    exact Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_mul_Ioo j
      (fun θ => Real.sin θ ^ 2) (fun θ => Work.Spaces.Gam β θ)
      (fun k _ => (dthU_iter_contDiffOn_Ioo
        (((Real.contDiff_sin (n := ∞)).pow 2).contDiffOn) k).differentiableOn (by simp))
      (fun k _ => (dthU_iter_contDiffOn_Ioo (gam_contDiffOn_Ioo β) k).differentiableOn
        (by simp))
  -- the two `sin(2θ)`-block integrals
  have hIntBlock : ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) ≤ 400 ∧
      MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ 120 / (17 * α) :=
    Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.sin_two_rpow_block_integrals
  have hBangsq : 0 ≤ ∑ i ∈ Finset.range 7, 2 * (B i) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  refine ⟨400 + (14 * 120 / 17) * (10 : ℝ) ^ 10
      + Real.pi / 2 * (∑ i ∈ Finset.range 7, 2 * (B i) ^ 2) + 1, ?_, fun α hαmem => ?_⟩
  · have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have := mul_nonneg hπ hBangsq
    linarith
  obtain ⟨hα, hα1⟩ := hαmem
  have hmem : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα, hα1⟩
  obtain ⟨hEAint, hEAle, hEGint, hEGle⟩ := hIntBlock α hmem
  set T : ℝ := ∑ i ∈ Finset.range 7, 2 * (B i) ^ 2 with hT
  have hTnn : 0 ≤ T := by rw [hT]; exact hBangsq
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) Work.Spaces.Iθ := hEAint
  have hIntB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 14 * (α * 100000) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    hEGint.const_mul _
  have hIntT : MeasureTheory.IntegrableOn (fun _ : ℝ => T) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := T) volume_Iθ_ne_top
  have hMajInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T)
      Work.Spaces.Iθ := (hIntA.add hIntB).add hIntT
  -- measurability
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hcontWeight : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  have hcontWeightEta : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  have hmeasJet : ∀ i : ℕ, i ≤ 6 → AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    intro i _
    have hcont_i : ContinuousOn (fun θ : ℝ => Work.Spaces.dthU^[i] (sinSqGam α) θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (dthU_iter_contDiffOn_Ioo (sinSqGam_contDiffOn_Ioo α) i).continuousOn
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact ((hcont_i.pow 2).mul hcontWeight).aestronglyMeasurable measurableSet_Ioo
  have hmeas0 : AEStronglyMeasurable
      (fun θ : ℝ => (sinSqGam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont0 : ContinuousOn (fun θ : ℝ => sinSqGam α θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (sinSqGam_contDiffOn_Ioo α).continuousOn
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact ((hcont0.pow 2).mul hcontWeightEta).aestronglyMeasurable measurableSet_Ioo
  have hmeasSum : AEStronglyMeasurable
      (∑ i ∈ Finset.range 7, fun θ : ℝ => (if 1 ≤ i then
        (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        else 0)) (volume.restrict Work.Spaces.Iθ) := by
    refine Finset.aestronglyMeasurable_sum _ fun i hi => ?_
    by_cases h1 : 1 ≤ i
    · have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
      simpa only [h1, if_true] using hmeasJet i hi6
    · simpa only [h1, if_false] using
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun θ => AngBlk α (sinSqGam α) θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hstep : (fun θ => AngBlk α (sinSqGam α) θ)
        = (fun θ : ℝ => (sinSqGam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∑ i ∈ Finset.range 7, fun θ : ℝ => (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) := by
      funext θ
      simp only [AngBlk, Pi.add_apply, Finset.sum_apply]
    rw [hstep]
    exact hmeas0.add hmeasSum
  -- nonnegativity and the pointwise bound
  have hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ AngBlk α (sinSqGam α) θ := by
    intro θ hθ
    have hs0 := sin_two_nonneg_Iθ hθ
    simp only [AngBlk]
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h1 : 1 ≤ i
    · simp only [h1, if_true]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · simp only [h1, if_false]; exact le_refl 0
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ, AngBlk α (sinSqGam α) θ
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T :=
    fun θ hθ => angBlk_le_majorant hα hα1 hBnn (hB α hmem) T hT hθ
  -- integrability of `AngBlk` by domination
  have hAngInt : MeasureTheory.IntegrableOn (fun θ => AngBlk α (sinSqGam α) θ)
      Work.Spaces.Iθ :=
    hMajInt.mono' hmeas (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (hnn θ hθ)]
      exact hpoint θ hθ)
  refine ⟨hAngInt, ?_⟩
  -- the integral bound
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun θ => AngBlk α (sinSqGam α) θ)
    (g := fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
      + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T)
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hnn θ hθ)
    hMajInt
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpoint θ hθ)
  have hval : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T))
      = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta))
        + 14 * (α * 100000) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        + (Real.pi / 2) * T := by
    have hsplit1 : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
          + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T))
        = (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
            + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))
          + (∫ θ in Work.Spaces.Iθ, T) :=
      MeasureTheory.integral_add (hIntA.add hIntB) hIntT
    have hsplit2 : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
          + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta))
          + (∫ θ in Work.Spaces.Iθ, 14 * (α * 100000) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) :=
      MeasureTheory.integral_add hIntA hIntB
    rw [hsplit1, hsplit2, MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const,
      volume_real_Iθ, smul_eq_mul]
  have hb2 : 14 * (α * 100000) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      ≤ 14 * (α * 100000) ^ 2 * (120 / (17 * α)) :=
    mul_le_mul_of_nonneg_left hEGle (by positivity)
  have hb3 : 14 * (α * 100000) ^ 2 * (120 / (17 * α)) ≤ (14 * 120 / 17) * (10 : ℝ) ^ 10 := by
    rw [show 14 * (α * 100000) ^ 2 * (120 / (17 * α))
        = (14 * 120 / 17) * (10 : ℝ) ^ 10 * α by
      field_simp
      ring]
    nlinarith [hα, hα1]
  linarith [hmono, hval, hEAle, hb2, hb3]

/-! ## The requested statement -/

theorem angBlk_sinSqGam : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ Bang : ℝ, 0 < Bang ∧
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α
      (fun θ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α
      (fun θ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) θ) ≤ Bang := by
  intro α hαmem
  obtain ⟨hα, hα1⟩ := hαmem
  have hmem : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα, hα1⟩
  obtain ⟨B0, hB0pos, hB0⟩ := angBlk_sinSqGam_bound
  obtain ⟨hIntG, hleG⟩ := hB0 α hmem
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hinv_le : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 10)]
    norm_num
    linarith
  have hinvnn : 0 ≤ (Work.Spaces.c α)⁻¹ := le_of_lt (inv_pos.mpr hcpos)
  have hc2 : (-(Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    nlinarith [hinv_le, hinvnn]
  have hfun : (fun θ : ℝ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
      = fun θ => (-(Work.Spaces.c α)⁻¹) * sinSqGam α θ := by
    funext θ; simp only [sinSqGam]; ring
  have hAng : ∀ θ : ℝ, AngBlk α (fun θ => (-(Work.Spaces.c α)⁻¹) * sinSqGam α θ) θ
      = (-(Work.Spaces.c α)⁻¹) ^ 2 * AngBlk α (sinSqGam α) θ :=
    fun θ => AngBlk_const_mul α (-(Work.Spaces.c α)⁻¹) (sinSqGam α) θ
  rw [hfun]
  simp only [hAng]
  refine ⟨100 * B0 + 1, by positivity, ?_, ?_⟩
  · exact hIntG.const_mul _
  · rw [MeasureTheory.integral_const_mul]
    calc (-(Work.Spaces.c α)⁻¹) ^ 2 * (∫ θ in Work.Spaces.Iθ, AngBlk α (sinSqGam α) θ)
        ≤ (-(Work.Spaces.c α)⁻¹) ^ 2 * B0 := mul_le_mul_of_nonneg_left hleG (sq_nonneg _)
      _ ≤ 100 * B0 := mul_le_mul_of_nonneg_right hc2 hB0pos.le
      _ ≤ 100 * B0 + 1 := by linarith

end Work.FTS.StrongEps.E4R3.Nblock6.aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false




/-- **The vanishing of the mode pairing.**  The pairing of `Φ` against `bslOp α (ρ ⊗ e_m)` with
the self-adjoint weight `z^((5-α)/α)·cos θ` vanishes.  Pair the equation `bslOp α Φ = 0` against
the compactly supported cut-off test functions `ρ ⊗ (χ_n·e_m)` (`perN_zero_set`); the difference
of the two integrands is supported in the two boundary layers of width `2δ_n` and is bounded by
`abs_sub_modeTest_le` (`SlotsZeroDiffBound`), whose integral is `O(δ_n^((1+η)/2))` by the layer
estimate (`SlotsZeroLayerSetBound`) and hence tends to `0` (`SlotsZeroLayerTendsto`).  The last
identification of the product-measure integral with the iterated one is `SlotsZeroPairingFubini`.
-/
theorem key_iter {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ} {C : ℝ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m)
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|)
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|)
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2))
    (hCpos : 0 ≤ C)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b))
    (hEsqrt : MeasureTheory.IntegrableOn (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b))
    (ha : 0 < a) (hsub : tsupport ρ ⊆ Set.Icc a b) :
    (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Φ z θ
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
      * (z ^ ((5 - α) / α) * Real.cos θ)) = 0 := by
  classical
  obtain ⟨A, hA0, hAdiff⟩ := SlotsZeroDiffBound (α := α) (Φ := Φ) (ρ := ρ) (m := m)
    (a := a) (b := b) hsm hρ hCut hΦint hEint ha hsub
  have hbox : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) Work.FTS.EllipticEst.Q0 :=
    integrableOn_absPhi_box hsm hΦint hEint
  have hf : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * bslWeight α p) Work.FTS.EllipticEst.Q0 :=
    integrableOn_modeIntegrand (α := α) (Φ := Φ) (ρ := ρ) (m := m) hsm hρ ha hsub hbox
  have hM0 : 0 ≤ ∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z) :=
    integral_nonneg (fun z => Real.sqrt_nonneg _)
  have hstep : ∀ n : ℕ, 2 ≤ n →
      |∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2
        * bslWeight α p|
      ≤ A * (1 + 1 / delta n) * (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z))) := by
    intro n hn2
    have hδpos : 0 < delta n := hCut.delta_pos n
    have hn0 : 0 < 2 * delta n := by linarith
    have hn1 : 2 * delta n ≤ π / 4 := by
      have h1 : delta n ≤ 1 / 3 := by
        rw [delta]
        refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) ?_
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      linarith
    obtain ⟨hdnint, hdnbnd⟩ := hAdiff n
    have hzero : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p) = 0 :=
      perN_zero_set (α := α) (Φ := Φ) (ρ := ρ) (m := m) hsm hsol hρ hρc hρs hCut n
    have hsplit : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p)
        = (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2 * bslWeight α p)
          + ∫ p in Work.FTS.EllipticEst.Q0,
              (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                - Φ p.1 p.2 * Work.Elliptic.bslOp α
                    (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
                  * bslWeight α p) := by
      have hcongr : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
          * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p)
          = ∫ p in Work.FTS.EllipticEst.Q0,
              ((Φ p.1 p.2 * Work.Elliptic.bslOp α (fun z θ => ρ z
                    * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p)
                + (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                  - Φ p.1 p.2 * Work.Elliptic.bslOp α (fun z θ => ρ z
                      * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p)) :=
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => by ring)
      rw [hcongr, MeasureTheory.integral_add hf hdnint]
    have h7 : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2 * bslWeight α p)
        = -(∫ p in Work.FTS.EllipticEst.Q0,
              (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                - Φ p.1 p.2 * Work.Elliptic.bslOp α
                    (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
                  * bslWeight α p)) := by linarith [hsplit, hzero]
    have hL : (∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2|
          * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
        ≤ 2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)) :=
      SlotsZeroLayerSetBound (Φ := Φ) (C := C) (a := a) (b := b)
        hsm hΦint hC hEint hEsqrt ha hn0 hn1
    calc |∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2 * bslWeight α p|
        = |∫ p in Work.FTS.EllipticEst.Q0,
              (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                - Φ p.1 p.2 * Work.Elliptic.bslOp α
                    (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
                  * bslWeight α p)| := by rw [h7, abs_neg]
      _ ≤ ∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2
            * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
            - Φ p.1 p.2 * Work.Elliptic.bslOp α
                (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
              * bslWeight α p| := abs_integral_le_integral_abs
      _ ≤ A * (1 + 1 / delta n) * (∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2|
            * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) := hdnbnd
      _ ≤ A * (1 + 1 / delta n) * (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
            * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z))) := by
          refine mul_le_mul_of_nonneg_left hL ?_
          exact mul_nonneg hA0 (add_nonneg zero_le_one (div_nonneg zero_le_one hδpos.le))
  have htend : Filter.Tendsto (fun n : ℕ => A * (1 + 1 / delta n)
      * (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)))) Filter.atTop (nhds 0) :=
    SlotsZeroLayerTendsto (A := A) (C := C)
      (M := ∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)) hA0 hCpos hM0
  have hbound : |∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2 * bslWeight α p| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htend
      (eventually_atTop.mpr ⟨2, fun n hn => hstep n hn⟩)
  have hfzero : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * bslWeight α p) = 0 :=
    abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  rw [← SlotsZeroPairingFubini (α := α) (Φ := Φ) (ρ := ρ) (m := m) (a := a) (b := b)
    hsm hρ ha hsub hΦint hEint]
  exact hfzero

/-! ## The two delegated modules instantiate the bundles -/

example {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    L2Facts α Φ :=
  SlotsZeroModeL2 hsm hHk

example (m : ℕ) : CutFacts m := SlotsZeroCutoff m


end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.E2hat_mem_contDiff_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

theorem E2hat_mem_contDiff_O (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : n ≤ 4) {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α n f)
    (hmemd : Work.Spaces.HkMem α n (Work.Spaces.Dth f)) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.E2hat f) ∧
      ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  -- the angular derivative is again `C^∞` on the open quadrant
  have hDthO : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := hO.Dth
  -- the `z`-only multiplier `φ(z) = z/(1+z)²`: smooth on `(-1,∞)`, `Zop`-iterates bounded
  obtain ⟨K, hK0, hKb⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le n
  have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) :=
    Work.FTS.CoercivityFix.E2Bound.contDiffOn_zDiv
  -- `ℋⁿ`-membership of the two products `φ·f` and `φ·D_θf`
  have hmul_f : Work.Spaces.HkMem α n (fun z θ => (z / (1 + z) ^ 2) * f z θ) :=
    ((hC α (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hφsm f hO).2 hmem).1
  have hmul_d : Work.Spaces.HkMem α n
      (fun z θ => (z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) :=
    ((hC α (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hφsm
      (Work.Spaces.Dth f) hDthO).2 hmemd).1
  -- smoothness of the two summands
  have hφSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z) ^ 2) :=
    E2hatOAux.smoothOpen_zOnly E2hatOAux.phiZ_contDiffOn
  have hA_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
    E2hatOAux.smoothOpen_const_mul 2 (E2hatOAux.smoothOpen_mul hφSO hO)
  have hB_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ)) :=
    E2hatOAux.smoothOpen_const_mul 3 (E2hatOAux.smoothOpen_mul hφSO hDthO)
  -- the explicit `z`-multiplier form of the defect
  have hE2 : Work.FTS.CoercivityFix.E2hat f
      = fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
          + 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) :=
    Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f
  constructor
  · rw [hE2]
    exact Work.FTS.EllipticEst.HkMem_add_open hA_sm hB_sm
      (Work.FTS.LocData.HkMem_const_mul α n 2 hmul_f)
      (Work.FTS.LocData.HkMem_const_mul α n 3 hmul_d)
  · have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat f) := by
      rw [hE2]
      exact Work.FTS.EllipticEst.smoothOpen_add hA_sm hB_sm
    have h := (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (Work.FTS.CoercivityFix.E2hat f)).mp hsm n
    simpa only [Work.FTS.EllipticEst.Q0] using h

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_Pi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-! ## Helpers -/

/-- A property that holds for a.e. `x` with `∀ y, P x y` holds for a.e. point of the plane. -/
private theorem ae_prod_of_ae_fst {P : ℝ → ℝ → Prop}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), ∀ y, P x y) :
    ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), P z.1 z.2 := by
  rw [MeasureTheory.ae_iff] at h ⊢
  refine measure_mono_null (t := {a : ℝ | ¬ ∀ y : ℝ, P a y} ×ˢ Set.univ) ?_ ?_
  · intro z hz
    exact ⟨fun hc => hz (hc z.2), Set.mem_univ _⟩
  · rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h, zero_mul]

/-- A function of the first coordinate, integrable over `[-1,1]` in the `lintegral` sense,
times the indicators of `[-1,1]` in both coordinates, is integrable on the plane. -/
private theorem integrable_prod_of_lintegral_Icc {g : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g (volume : Measure ℝ))
    (hg : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1, ‖g q₁‖ₑ < ⊤) :
    Integrable (fun q : ℝ × ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q.1 * g q.1
      * (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q.2)
      (volume : Measure (ℝ × ℝ)) := by
  classical
  have hgon : IntegrableOn g (Set.Icc (-1 : ℝ) 1) := ⟨hgm.restrict, hg⟩
  have hf1 : Integrable
      (fun q₁ : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₁ * g q₁)
      (volume : Measure ℝ) := by
    rw [show (fun q₁ : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₁ * g q₁)
        = (Set.Icc (-1 : ℝ) 1).indicator g from by
      funext x
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hgon
  have hf2 : Integrable
      (fun q₂ : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₂)
      (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simpa using isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ))))
  have hprod := hf1.mul_prod hf2
  exact hprod

/-! ## The main theorem -/

theorem JepsMarginalZero_Pi {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    (htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ)
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam z)))
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2))
    (hjtr : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0)) :
    ∀ z ∈ Set.Ioi (0:ℝ),
      (∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))) = 0 := by
  intro z hz
  set Dfun : ℝ → ℝ := fun u => ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2 with hDfun
  set Cα : ℝ := Real.sqrt (100 / (Work.Spaces.gam α - 1)) with hCα
  have hCα0 : 0 ≤ Cα := Real.sqrt_nonneg _
  have hgam1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    simp only [Work.Spaces.gam]; linarith [hα.1]
  have h100 : (0 : ℝ) ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) (le_of_lt hgam1)
  have hCαsq : Cα ^ 2 = 100 / (Work.Spaces.gam α - 1) := Real.sq_sqrt h100
  -- the uniform bound on `ρ`
  obtain ⟨Cρ, hCρ0, hCρ⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ × ℝ, ‖ρ q‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      hρ.moll.cont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun q => ?_⟩
    by_cases hq : q ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
    · exact le_trans (hC q hq) (le_max_left _ _)
    · have hq0 : ρ q = 0 := by
        by_contra hne
        have hle : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := hρ.moll.support q hne
        have h1 : 1 < q.1 ^ 2 ∨ 1 < q.2 ^ 2 := by
          have hq' : ¬ (q.1 ∈ Set.Icc (-1 : ℝ) 1) ∨ ¬ (q.2 ∈ Set.Icc (-1 : ℝ) 1) := by
            simpa only [Set.mem_prod, not_and_or] using hq
          rcases hq' with h | h
          · rw [Set.mem_Icc, not_and_or] at h
            rcases h with h | h
            · left; rw [not_le] at h; nlinarith
            · left; rw [not_le] at h; nlinarith
          · rw [Set.mem_Icc, not_and_or] at h
            rcases h with h | h
            · right; rw [not_le] at h; nlinarith
            · right; rw [not_le] at h; nlinarith
        rcases h1 with h1 | h1 <;> nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      simp [hq0]
  -- `ρ` vanishes off the square
  have hρvan : ∀ q : ℝ × ℝ, q ∉ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 → ρ q = 0 := by
    intro q hq
    by_contra hne
    have hle : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := hρ.moll.support q hne
    have h1 : |q.1| ≤ 1 := by nlinarith [sq_nonneg q.2, abs_nonneg q.1, sq_abs q.1]
    have h2 : |q.2| ≤ 1 := by nlinarith [sq_nonneg q.1, abs_nonneg q.2, sq_abs q.2]
    exact hq (Set.mem_prod.mpr ⟨abs_le.mp h1, abs_le.mp h2⟩)
  -- `Dfun` is nonnegative
  have hDnn : ∀ u : ℝ, 0 ≤ Dfun u := by
    intro u
    rw [show Dfun u = ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2 from rfl]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc]
      with σ hσ
    refine mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ?_) _) (sq_nonneg _)
    exact ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  -- (1) local integrability on the interval `[z e^{-ε}, z e^{ε}]`
  have hza : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  have hzab : z * Real.exp (-ε) ≤ z * Real.exp ε :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le
  have hDint : ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε),
      ENNReal.ofReal (Real.sqrt (Dfun u)) < ⊤ :=
    SqrtDLocInt hα hm (a := z * Real.exp (-ε)) (b := z * Real.exp ε) hza
  have hLamInt : ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε),
      ENNReal.ofReal |lam u| < ⊤ :=
    LamLocInt hα hso hlamm htr hbd (a := z * Real.exp (-ε)) (b := z * Real.exp ε) hza hzab hDint
  -- (2) the `lintegral` bounds of the two factors over `[-1,1]`
  have hgD_lint : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) < ⊤ := by
    have h1 : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal (Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))))
        = ENNReal.ofReal (Cρ * Cα) * ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Cρ * Cα)) _
        ENNReal.ofReal_lt_top.ne]
      refine MeasureTheory.lintegral_congr fun q₁ => ?_
      rw [ENNReal.ofReal_mul (mul_nonneg hCρ0 hCα0)]
    rw [h1]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact lt_of_le_of_lt
      (LintegralExpCompIcc hz hε (fun u => ENNReal.ofReal (Real.sqrt (Dfun u))))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDint)
  have hgL_lint : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (Cρ * |lam (z * Real.exp (-(ε * q₁)))|) < ⊤ := by
    have h1 : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal (Cρ * |lam (z * Real.exp (-(ε * q₁)))|)
        = ENNReal.ofReal Cρ * ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
            ENNReal.ofReal |lam (z * Real.exp (-(ε * q₁)))| := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal Cρ) _ ENNReal.ofReal_lt_top.ne]
      refine MeasureTheory.lintegral_congr fun q₁ => ?_
      rw [ENNReal.ofReal_mul hCρ0]
    rw [h1]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact lt_of_le_of_lt
      (LintegralExpCompIcc hz hε (fun u => ENNReal.ofReal |lam u|))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLamInt)
  -- (3) the factors, the bound and its integrability
  set gD : ℝ → ℝ := fun q₁ => Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) with hgD
  set gL : ℝ → ℝ := fun q₁ => Cρ * |lam (z * Real.exp (-(ε * q₁)))| with hgL
  set hI : ℝ → ℝ := fun q₂ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₂ with hhI
  have hgD_meas : AEStronglyMeasurable gD (volume : Measure ℝ) :=
    (SqrtDMeas hα hz hε hso).const_mul (Cρ * Cα)
  have hgL_meas : AEStronglyMeasurable gL (volume : Measure ℝ) :=
    ((hlamm.comp (by fun_prop : Measurable fun q₁ : ℝ => z * Real.exp (-(ε * q₁)))).abs).aestronglyMeasurable.const_mul Cρ
  have hgD_lint' : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1, ‖gD q₁‖ₑ < ⊤ := by
    rw [MeasureTheory.lintegral_congr (fun q₁ => ?_)]
    exact hgD_lint
    rw [Real.enorm_eq_ofReal_abs,
      show gD q₁ = Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) from rfl]
    congr 1
    exact abs_of_nonneg (mul_nonneg (mul_nonneg hCρ0 hCα0) (Real.sqrt_nonneg _))
  have hgL_lint' : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1, ‖gL q₁‖ₑ < ⊤ := by
    rw [MeasureTheory.lintegral_congr (fun q₁ => ?_)]
    exact hgL_lint
    rw [Real.enorm_eq_ofReal_abs,
      show gL q₁ = Cρ * |lam (z * Real.exp (-(ε * q₁)))| from rfl]
    congr 1
    exact abs_of_nonneg (mul_nonneg hCρ0 (abs_nonneg _))
  have hboundInt : Integrable (fun q : ℝ × ℝ => hI q.1 * gD q.1 * hI q.2)
      (volume : Measure (ℝ × ℝ)) :=
    integrable_prod_of_lintegral_Icc hgD_meas hgD_lint'
  have hkMajInt : Integrable (fun q : ℝ × ℝ => hI q.1 * gL q.1 * hI q.2)
      (volume : Measure (ℝ × ℝ)) :=
    integrable_prod_of_lintegral_Icc hgL_meas hgL_lint'
  -- (4) the trace part is integrable
  have hk : Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))
      (volume : Measure (ℝ × ℝ)) := by
    refine Integrable.mono' hkMajInt ?_ ?_
    · exact hρ.moll.cont.aestronglyMeasurable.mul
        ((hlamm.comp (by fun_prop : Measurable fun q : ℝ × ℝ => z * Real.exp (-(ε * q.1)))).aestronglyMeasurable)
    · filter_upwards with q
      by_cases hq : q ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
      · have h1 : q.1 ∈ Set.Icc (-1 : ℝ) 1 := (Set.mem_prod.mp hq).1
        have h2 : q.2 ∈ Set.Icc (-1 : ℝ) 1 := (Set.mem_prod.mp hq).2
        have hle : ‖ρ q * lam (z * Real.exp (-(ε * q.1)))‖
            ≤ Cρ * |lam (z * Real.exp (-(ε * q.1)))| := by
          rw [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hCρ q) (abs_nonneg _)
        rw [show hI q.1 = 1 from Set.indicator_of_mem h1 (fun _ => (1 : ℝ)),
          show hI q.2 = 1 from Set.indicator_of_mem h2 (fun _ => (1 : ℝ))]
        simpa using hle
      · rw [hρvan q hq, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          (mul_nonneg hCρ0 (abs_nonneg _))) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  -- (5) the a.e. "good in `q₁`" statement
  have hgood : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0:ℝ))),
      (Filter.Tendsto (fun θ => f u θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam u)))
      ∧ (∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
          (f u θ - lam u)^2 ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) * Dfun u) := by
    filter_upwards [htr, hbd] with u h1 h2
    exact ⟨h1, fun θ hθ => h2 θ hθ⟩
  have hgood_q : ∀ᵐ q₁ ∂(volume : Measure ℝ),
      (Filter.Tendsto (fun θ => f (z * Real.exp (-(ε * q₁))) θ)
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam (z * Real.exp (-(ε * q₁))))))
      ∧ (∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
          (f (z * Real.exp (-(ε * q₁))) θ - lam (z * Real.exp (-(ε * q₁))))^2
            ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
              * Dfun (z * Real.exp (-(ε * q₁)))) :=
    AeCompExpNeg hz hε hgood
  -- (6) the map `Gfun`
  set Gfun : ℝ → ℝ × ℝ → ℝ := fun θ q => ρ q *
    (f (z * Real.exp (-(ε * q.1))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2))))
      - lam (z * Real.exp (-(ε * q.1)))) with hGfun
  have hGfun_meas : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      AEStronglyMeasurable (Gfun θ) (volume : Measure (ℝ × ℝ)) := by
    intro θ hθ
    have hΦcont : Continuous (fun q : ℝ × ℝ =>
        (z * Real.exp (-(ε * q.1)), Work.FTS.StrongEps.thShift θ (ε * q.2))) := by
      refine Continuous.prodMk ?_ ?_
      · fun_prop
      · simp only [Work.FTS.StrongEps.thShift]; fun_prop
    have hΦmem : ∀ q : ℝ × ℝ,
        (z * Real.exp (-(ε * q.1)), Work.FTS.StrongEps.thShift θ (ε * q.2)) ∈ Work.FTS.EllipticEst.Q0 := by
      intro q
      refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨?_, ?_, ?_⟩
      · exact mul_pos hz (Real.exp_pos _)
      · exact (Work.FTS.StrongEps.thShift_mem hθ).1
      · exact (Work.FTS.StrongEps.thShift_mem hθ).2
    have hf_cont : Continuous (fun q : ℝ × ℝ =>
        f (z * Real.exp (-(ε * q.1))) (Work.FTS.StrongEps.thShift θ (ε * q.2))) :=
      ((Work.FTS.EllipticEst.SmoothOpen.forall hso 0).continuousOn).comp_continuous hΦcont hΦmem
    have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        f (z * Real.exp (-(ε * q.1))) (Work.FTS.StrongEps.thShift θ (ε * q.2)))
        (volume : Measure (ℝ × ℝ)) := hf_cont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : ℝ × ℝ => lam (z * Real.exp (-(ε * q.1))))
        (volume : Measure (ℝ × ℝ)) :=
      (hlamm.comp (by fun_prop : Measurable fun q : ℝ × ℝ => z * Real.exp (-(ε * q.1)))).aestronglyMeasurable
    exact hρ.moll.cont.aestronglyMeasurable.mul (h1.sub h2)
  -- (7) the eventual set in `θ`
  have hS : Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ}
      ∈ nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)) :=
    Filter.inter_mem (Ioo_mem_nhdsLT (by positivity))
      (Real.tendsto_tan_pi_div_two.eventually (eventually_gt_atTop (Real.exp ε)))
  have hbnd_pt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ},
      ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), ‖Gfun θ q‖ ≤ hI q.1 * gD q.1 * hI q.2 := by
    intro θ hθS
    obtain ⟨hθ, htanθ⟩ := hθS
    have hae : ∀ᵐ q₁ ∂(volume : Measure ℝ), ∀ q₂ : ℝ,
        ‖Gfun θ (q₁, q₂)‖ ≤ hI q₁ * gD q₁ * hI q₂ := by
      filter_upwards [hgood_q] with q₁ hq₁ q₂
      obtain ⟨-, hbdq⟩ := hq₁
      by_cases hq1 : q₁ ∈ Set.Icc (-1 : ℝ) 1
      · by_cases hq2 : q₂ ∈ Set.Icc (-1 : ℝ) 1
        · -- main case: the `hbd` bound applies
          have hΘ : Work.FTS.StrongEps.thShift θ (ε * q₂) ∈ Set.Ioo (Real.pi/4) (Real.pi/2) := by
            refine ⟨?_, (Work.FTS.StrongEps.thShift_mem hθ).2⟩
            have hexp : Real.exp (-ε) ≤ Real.exp (-(ε * q₂)) :=
              Real.exp_le_exp.mpr (by nlinarith [hq2.2])
            have h1 : 1 < Real.tan θ * Real.exp (-(ε * q₂)) := by
              have h2 : 1 < Real.tan θ * Real.exp (-ε) := by
                have hmul : Real.exp ε * Real.exp (-ε) = 1 := by
                  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
                rw [← hmul]
                exact mul_lt_mul_of_pos_right htanθ (Real.exp_pos (-ε))
              exact lt_of_lt_of_le h2
                (mul_le_mul_of_nonneg_left hexp (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2).le)
            calc Real.pi/4 = Real.arctan 1 := Real.arctan_one.symm
              _ < Real.arctan (Real.tan θ * Real.exp (-(ε * q₂))) := Real.arctan_strictMono h1
              _ = Work.FTS.StrongEps.thShift θ (ε * q₂) := rfl
          have hbd' := hbdq (Work.FTS.StrongEps.thShift θ (ε * q₂)) hΘ
          have hsin1 : (Real.sin (2 * Work.FTS.StrongEps.thShift θ (ε * q₂)))
              ^ (Work.Spaces.gam α - 1) ≤ 1 := by
            refine Real.rpow_le_one ?_ ?_ (le_of_lt hgam1)
            · exact Real.sin_nonneg_of_mem_Icc
                ⟨by linarith [hΘ.1, Real.pi_pos], by linarith [hΘ.2, Real.pi_pos]⟩
            · exact Real.sin_le_one _
          have hsq : (f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
              - lam (z * Real.exp (-(ε * q₁)))) ^ 2 ≤ (Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) ^ 2 := by
            calc (f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
                  - lam (z * Real.exp (-(ε * q₁)))) ^ 2
                ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2 * Work.FTS.StrongEps.thShift θ (ε * q₂)))
                    ^ (Work.Spaces.gam α - 1) * Dfun (z * Real.exp (-(ε * q₁))) := hbd'
              _ ≤ 100 / (Work.Spaces.gam α - 1) * 1 * Dfun (z * Real.exp (-(ε * q₁))) := by
                  refine mul_le_mul_of_nonneg_right ?_ (hDnn _)
                  exact mul_le_mul_of_nonneg_left hsin1 h100
              _ = (Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) ^ 2 := by
                  rw [mul_pow, hCαsq, Real.sq_sqrt (hDnn _)]
                  ring
          have habs : |f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
              - lam (z * Real.exp (-(ε * q₁)))| ≤ Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) := by
            calc |f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
                  - lam (z * Real.exp (-(ε * q₁)))|
                = Real.sqrt ((f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
                  - lam (z * Real.exp (-(ε * q₁)))) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt ((Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) ^ 2) := Real.sqrt_le_sqrt hsq
              _ = Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) := by
                  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hCα0 (Real.sqrt_nonneg _))]
          have hmain : ‖Gfun θ (q₁, q₂)‖ ≤ Cρ * (Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) := by
            rw [show Gfun θ (q₁, q₂) = ρ (q₁, q₂) * (f (z * Real.exp (-(ε * q₁)))
                (Work.FTS.StrongEps.thShift θ (ε * q₂)) - lam (z * Real.exp (-(ε * q₁)))) from rfl,
              norm_mul, Real.norm_eq_abs]
            exact mul_le_mul (hCρ (q₁, q₂)) habs (abs_nonneg _) hCρ0
          rw [show hI q₁ = 1 from Set.indicator_of_mem hq1 (fun _ => (1 : ℝ)),
            show hI q₂ = 1 from Set.indicator_of_mem hq2 (fun _ => (1 : ℝ))]
          simpa [gD, mul_assoc] using hmain
        · -- `q₂` outside the square: `ρ` vanishes
          have hq2' : ¬ (q₂ ∈ Set.Icc (-1 : ℝ) 1) := hq2
          have h0 : ρ (q₁, q₂) = 0 := by
            refine hρvan (q₁, q₂) fun hc => hq2' (Set.mem_prod.mp hc).2
          rw [show Gfun θ (q₁, q₂) = ρ (q₁, q₂) * (f (z * Real.exp (-(ε * q₁)))
              (Work.FTS.StrongEps.thShift θ (ε * q₂)) - lam (z * Real.exp (-(ε * q₁)))) from rfl, h0, zero_mul,
            norm_zero, show hI q₂ = 0 from Set.indicator_of_notMem hq2 (fun _ => (1 : ℝ))]
          simp
      · -- `q₁` outside the square: `ρ` vanishes
        have h0 : ρ (q₁, q₂) = 0 := by
          refine hρvan (q₁, q₂) fun hc => hq1 (Set.mem_prod.mp hc).1
        rw [show Gfun θ (q₁, q₂) = ρ (q₁, q₂) * (f (z * Real.exp (-(ε * q₁)))
            (Work.FTS.StrongEps.thShift θ (ε * q₂)) - lam (z * Real.exp (-(ε * q₁)))) from rfl, h0, zero_mul,
          norm_zero, show hI q₁ = 0 from Set.indicator_of_notMem hq1 (fun _ => (1 : ℝ))]
        simp
    exact ae_prod_of_ae_fst hae
  -- (8) integrability of `Gfun θ` for `θ` in the eventual set
  have hGint : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ},
      Integrable (Gfun θ) (volume : Measure (ℝ × ℝ)) := by
    intro θ hθS
    refine Integrable.mono' hboundInt (hGfun_meas θ hθS.1) ?_
    filter_upwards [hbnd_pt θ hθS] with q hq
    exact hq
  -- (9) the dominated convergence
  have hbnd_ev : ∀ᶠ θ in nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)),
      ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), ‖Gfun θ q‖ ≤ hI q.1 * gD q.1 * hI q.2 :=
    Filter.eventually_of_mem hS hbnd_pt
  have hmeas_ev : ∀ᶠ θ in nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)),
      AEStronglyMeasurable (Gfun θ) (volume : Measure (ℝ × ℝ)) :=
    Filter.eventually_of_mem hS (fun θ hθ => hGfun_meas θ hθ.1)
  have hlim : ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), Tendsto (fun θ => Gfun θ q)
      (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    have hae : ∀ᵐ q₁ ∂(volume : Measure ℝ), ∀ q₂ : ℝ,
        Tendsto (fun θ => Gfun θ (q₁, q₂)) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
      filter_upwards [hgood_q] with q₁ hq₁ q₂
      obtain ⟨htrq, -⟩ := hq₁
      have hshift : Tendsto (fun θ : ℝ => Work.FTS.StrongEps.thShift θ (ε * q₂))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) :=
        Real.tendsto_arctan_atTop.comp
          (Real.tendsto_tan_pi_div_two.atTop_mul_const (Real.exp_pos (-(ε * q₂))))
      have h1 : Tendsto (fun θ : ℝ => f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂)))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam (z * Real.exp (-(ε * q₁))))) :=
        htrq.comp hshift
      have h2 : Tendsto (fun θ : ℝ => f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
          - lam (z * Real.exp (-(ε * q₁)))) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
          (nhds (lam (z * Real.exp (-(ε * q₁))) - lam (z * Real.exp (-(ε * q₁))))) :=
        h1.sub tendsto_const_nhds
      have h3 : Tendsto (fun θ : ℝ => ρ (q₁, q₂) *
          (f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
            - lam (z * Real.exp (-(ε * q₁)))))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
        simpa [sub_self] using h2.const_mul (ρ (q₁, q₂))
      have h3' : Tendsto (fun θ : ℝ => ρ (q₁, q₂) *
          (f (z * Real.exp (-(ε * q₁))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q₂))))
            - lam (z * Real.exp (-(ε * q₁)))))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := h3
      simpa [Gfun] using h3'
    exact ae_prod_of_ae_fst hae
  have hDCT : Tendsto (fun θ => ∫ q, Gfun θ q) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (ℝ × ℝ))) (F := Gfun) (f := fun _ => (0 : ℝ))
      (bound := fun q => hI q.1 * gD q.1 * hI q.2) hmeas_ev hbnd_ev hboundInt hlim
    simpa using h
  -- (10) assemble
  set A : ℝ := ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) with hA
  have hKey : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ},
      Work.FTS.StrongEps.Jeps ρ ε f z θ = (∫ q, Gfun θ q) + A := by
    intro θ hθS
    rw [JepsRhoForm ρ ε f hε hz hθS.1]
    have h1 : Integrable (fun q : ℝ × ℝ => ρ q * (f (z * Real.exp (-(ε * q.1)))
        (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2)))) - lam (z * Real.exp (-(ε * q.1)))))
        (volume : Measure (ℝ × ℝ)) := hGint θ hθS
    have h2 : Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))
        (volume : Measure (ℝ × ℝ)) := hk
    have hpt : ∀ q : ℝ × ℝ, ρ q * f (z * Real.exp (-(ε * q.1))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2))))
        = ρ q * (f (z * Real.exp (-(ε * q.1))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2))))
            - lam (z * Real.exp (-(ε * q.1)))) + ρ q * lam (z * Real.exp (-(ε * q.1))) :=
      fun q => by ring
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall hpt), MeasureTheory.integral_add h1 h2]
  have hA0 : A = 0 := by
    have h1 : Tendsto (fun θ => (∫ q, Gfun θ q) + A) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) :=
      (hjtr z hz).congr' (Filter.eventually_of_mem hS hKey)
    have h2 : Tendsto (fun θ => (∫ q, Gfun θ q) + A) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
        (nhds (0 + A)) := hDCT.add tendsto_const_nhds
    have h3 := tendsto_nhds_unique h1 h2
    linarith
  rw [← RhoMargFubini hε hk]
  exact hA0

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JkerDomDensityIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Integrability of the dominating density of the trace transfer.**  For a smooth admissible
kernel `ρ` (`IsSmoothKernel`), `ε > 0`, `z > 0`, a measurable `lam` with integrable
log-coordinate trace, and an angular energy `Ibd α f` which is integrable on every compact
subinterval of `(0,∞)`, the density

  `p ↦ ‖Jker ρ ε p‖ * (|lam (z * exp (-p.1))| + Ibd α f (z * exp (-p.1)))`

is integrable on `ℝ²`.  This is the domination needed by the dominated-convergence computation of
the boundary trace of `Jeps`.

Route.  Split into the two summands.
* For `lam`: `‖Jker ρ ε p‖ ≤ ε⁻² ‖ρ‖_∞` and `Jker ρ ε p = 0` unless `|p.1| ≤ ε` and
  `|p.2| ≤ ε` (`Jker_ne_zero_support`, `Jker_integrable`); putting `u = log z - p₁` (translation
  invariance of Lebesgue measure) gives `z * exp (-p₁) = exp u` and hence
  `∫_{|p₁| ≤ ε} |lam (z exp (-p₁))| dp₁ = ∫_{log z - ε}^{log z + ε} |lam (exp u)| du ≤
  ∫_u |lam (exp u)| du < ∞` by `hint`, while the `p₂`-integral runs over a fixed bounded interval.
* For `Ibd`: the same substitution reduces `∫_{|p₁| ≤ ε} Ibd α f (z exp (-p₁)) dp₁` to
  `∫_{z' ∈ [z e^{-ε}, z e^{ε}]} Ibd α f z' / z' dz' ≤ (z e^{-ε})⁻¹ ∫_{z' ∈ [z e^{-ε}, z e^{ε}]} Ibd α f z'`,
  which is finite by `hIbd` with `a = z * exp (-ε) > 0` and `b = z * exp ε`; obtain the
  `1/z'`-weighted form from the plain interval integral by the monotone `C¹` substitution
  `z' = exp u` (`intervalIntegral.integral_comp_mul_deriv` or its `Real.exp` instance), and
  multiply by a bound for the `p₂`-marginal of `‖Jker ρ ε‖`.
The Fubini/Tonelli step is over `(volume : Measure ℝ).prod volume`; note that `p ↦ ‖Jker ρ ε p‖`
is integrable (`Jker_integrable`), so `MeasureTheory.Integrable.mul_prod` (or `Integrable.mono'`
against an explicit dominating density) applies.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem JkerDomDensityIntegrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {lam : ℝ → ℝ} (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hIbd : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z : ℝ => Ibd α f z) (Set.Icc a b)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
  classical
  -- a uniform bound for the kernel
  obtain ⟨M, hM0, hMle⟩ := JkerNormBound (ρ := ρ) hρ hε
  -- the slice interval of the `z`-coordinate and the square on which the density is supported
  set s : Set ℝ := Set.Icc (-ε) ε with hs_def
  have hs : MeasurableSet s := by rw [hs_def]; exact measurableSet_Icc
  have hsfin : (MeasureTheory.volume : Measure ℝ) s ≠ ⊤ := by
    rw [hs_def, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- the two one-dimensional integrability facts, on the slice interval
  have hlam1 : MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-x))|)
      (MeasureTheory.volume.restrict s) := by
    rw [hs_def]; exact AbsLamShiftIntegrableOn hint hz
  have hibd1 : MeasureTheory.Integrable (fun x : ℝ => Ibd α f (z * Real.exp (-x)))
      (MeasureTheory.volume.restrict s) := by
    rw [hs_def]; exact ExpShiftIntegrable (h := fun y => Ibd α f y) hε hz hIbd
  -- the dominating one-dimensional density
  set F : ℝ → ℝ := fun x => |lam (z * Real.exp (-x))| + |Ibd α f (z * Real.exp (-x))| with hF_def
  have hsum1 : MeasureTheory.Integrable F (MeasureTheory.volume.restrict s) := by
    rw [hF_def]; exact hlam1.add hibd1.norm
  -- its two indicator factors
  have hH1 : MeasureTheory.Integrable (s.indicator F) (MeasureTheory.volume : Measure ℝ) :=
    (MeasureTheory.integrable_indicator_iff hs).mpr hsum1
  have hH2 : MeasureTheory.Integrable (s.indicator (fun _ : ℝ => (1 : ℝ)))
      (MeasureTheory.volume : Measure ℝ) :=
    (MeasureTheory.integrable_indicator_iff hs).mpr
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hsfin)
  -- the dominating density on the plane, and its integrability (Fubini on the product)
  set D : ℝ × ℝ → ℝ :=
    fun p => M * ((s.indicator F) p.1 * (s.indicator (fun _ : ℝ => (1 : ℝ))) p.2) with hD_def
  have hD : MeasureTheory.Integrable D (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    have h := (hH1.const_mul M).mul_prod hH2
    simpa only [hD_def, mul_assoc] using h
  -- the kernel vanishes off the square
  have hzero : ∀ p : ℝ × ℝ, p ∉ s ×ˢ s → Work.FTS.StrongEps.Jker ρ ε p = 0 := by
    intro p hp
    refine JkerEqZeroOfAbsGt hρ hε ?_
    rcases not_and_or.mp hp with h | h
    · left
      have h' : p.1 < -ε ∨ ε < p.1 := by
        rw [hs_def, Set.mem_Icc] at h
        simpa only [not_le] using not_and_or.mp h
      rcases h' with h' | h'
      · rw [abs_of_neg (by linarith)]; linarith
      · rwa [abs_of_nonneg (by linarith)]
    · right
      have h' : p.2 < -ε ∨ ε < p.2 := by
        rw [hs_def, Set.mem_Icc] at h
        simpa only [not_le] using not_and_or.mp h
      rcases h' with h' | h'
      · rw [abs_of_neg (by linarith)]; linarith
      · rwa [abs_of_nonneg (by linarith)]
  -- the pointwise domination
  have hdom : ∀ᵐ p ∂(MeasureTheory.volume.restrict (s ×ˢ s)),
      ‖(fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))) p‖ ≤ D p := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    change ‖‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))‖ ≤ D p
    by_cases hp : p ∈ s ×ˢ s
    · obtain ⟨h1, h2⟩ := hp
      change ‖‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))‖
          ≤ M * ((s.indicator F) p.1 * (s.indicator (fun _ : ℝ => (1 : ℝ))) p.2)
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      calc ‖‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))‖
          = ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            |(|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))| := by
            rw [norm_mul, norm_norm]; rfl
        _ ≤ M * |(|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))| :=
            mul_le_mul_of_nonneg_right (hMle p) (abs_nonneg _)
        _ ≤ M * (|lam (z * Real.exp (-p.1))| + |Ibd α f (z * Real.exp (-p.1))|) := by
            refine mul_le_mul_of_nonneg_left ?_ hM0
            simpa only [abs_abs] using
              abs_add_le (|lam (z * Real.exp (-p.1))|) (Ibd α f (z * Real.exp (-p.1)))
        _ = M * (F p.1 * 1) := by simp only [hF_def, mul_one]
    · have hz0 : Work.FTS.StrongEps.Jker ρ ε p = 0 := hzero p hp
      simp only [hz0, norm_zero, zero_mul]
      change (0 : ℝ) ≤ M * ((s.indicator F) p.1 * (s.indicator (fun _ : ℝ => (1 : ℝ))) p.2)
      exact mul_nonneg hM0 (mul_nonneg
        (Set.indicator_nonneg (fun x _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) p.1)
        (Set.indicator_nonneg (fun x _ => zero_le_one) p.2))
  -- measurability of the density on the square
  have hdens_aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1))))
      (MeasureTheory.volume.restrict (s ×ˢ s)) := by
    have hker : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖)
        (MeasureTheory.volume.restrict (s ×ˢ s)) :=
      (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).norm.aestronglyMeasurable
    have hlam2 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => |lam (z * Real.exp (-p.1))|)
        (MeasureTheory.volume.restrict (s ×ˢ s)) :=
      ((hlamm.comp (by fun_prop)).norm).aestronglyMeasurable
    have hibd2 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Ibd α f (z * Real.exp (-p.1)))
        (MeasureTheory.volume.restrict (s ×ˢ s)) := by
      have h1 : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => Ibd α f (z * Real.exp (-x)))
          (MeasureTheory.volume.restrict s) := hibd1.aestronglyMeasurable
      have h2 := h1.comp_fst (ν := MeasureTheory.volume.restrict s)
      rwa [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod] at h2
    exact hker.mul (hlam2.add hibd2)
  have hOn : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))) (s ×ˢ s) :=
    (hD.mono_measure MeasureTheory.Measure.restrict_le_self).mono' hdens_aesm hdom
  -- extend from the square to the plane: the density vanishes off the square
  refine ((MeasureTheory.integrable_indicator_iff (hs.prod hs)).mpr hOn).congr ?_
  filter_upwards with p
  change (s ×ˢ s).indicator (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))) p = _
  by_cases hp : p ∈ s ×ˢ s
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp, hzero p hp]
    simp only [norm_zero, zero_mul]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ^0`-membership and the `ℋ^0`-bound along a pointwise convergent sequence

`hkMemOfJConv` is the `k = 0` instance of the Fatou step for the weighted Sobolev space
`ℋ^k` of the paper.  For `k = 0` the integrand `HkIntegrand α 0 f z θ` only involves the
*mixed slot* `D_z^0 D_θ^0 f = f` itself (the two sums carrying `D_θ` are empty: they are
guarded by `1 ≤ i` with `i + j ≤ 0`), so that plain pointwise convergence of `un n → u` on
the open quadrant -- rather than convergence of all the jets -- already suffices.

The proof is two nested Fatou arguments:

* **Fatou in `θ`**, for every fixed `z ∈ Iz`: the integrands converge a.e. in `θ`
  (`JConvAux.ae_tendsto_HkIntegrand_slice`, which reduces the integrand to the slots and
  handles the degenerate lines `z = 0`, `sin (2θ) = 0`, where both integrands vanish
  identically), and `JConvAux.ofReal_integral_le_liminf_ofReal_integral` converts the
  `ℝ≥0∞`-Fatou inequality into
  `ofReal (∫_θ F z) ≤ liminf_n ofReal (∫_θ F_n n z)`;
* **Fatou in `z`**, integrated against `volume.restrict Iz`: this bounds
  `∫⁻_z ofReal (∫_θ F z)` by `liminf_n ofReal (HkSq α 0 (un n)) ≤ ofReal C`.  The
  `z`-function `z ↦ ∫_θ F z` is a.e. measurable because `hmeas` gives the a.e.
  measurability of `z ↦ ∫⁻_θ ofReal (F z)` through `AEMeasurable.lintegral_prod_right`.

Finiteness of the resulting lintegral gives both halves at once: `HasFiniteIntegral` yields
the `z`-integrability of the slice integrals (the second half of `HkMem α 0 u`, the first
being the hypothesis `hslice`), and `integral_eq_lintegral_of_nonneg_ae` turns the bound into
`HkSq α 0 u ≤ C`.
-/

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000


end Work.FTS_EllLimOK.PkgJets
end
