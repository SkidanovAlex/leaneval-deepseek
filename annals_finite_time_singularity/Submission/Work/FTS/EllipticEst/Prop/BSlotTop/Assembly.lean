/-
Work module for the Elgindi finite-time singularity project.

# `BSlotTop/Assembly`: the `B`-half of the induction step of `prop:Hk`

This is the clean-cone copy of `Work.FTS.EllipticEst.remov.TopCoreB.B_slot_bound_clean`
(`Submission/Work/FTS/EllipticEst/remov/TopCoreB/BHalfClean.lean`), with the two `sorry`-carrying
inputs replaced by proved copies:

* `remov.TopCoreB.srcBound` ⟶ `BSlotTop.srcBoundFts` (through `Gsum_bound_fts`);
* `remov.TopCoreB.slice_ang_far` ⟶ `BSlotTop.sliceAngGenFts` (through `oneDFts`), the
  one-dimensional angular estimate, which rests on the proved `remov.slice_ang_v_outer`, the
  proved far-half chain `remov.slice_ang_v_far_live_of_top` + `remov.farTopXAuxLive_of_top` +
  `remov.EllFarTopDiv.sinWeight_xDivX_top_le'`, and the proved `BSlotTop.sliceAngGenFinalFts`.

All the remaining inputs are proved declarations with clean import cones:
`TT.ESW.Tk_B_le_chain_uniform`, `TT.ESW.Main.E_le_HkSq`, `TT.ESW.eta_slot_le`,
`TT.ESW.low_order_split`, `remov.high_slice_chain_slots`, `TT.ESW.U_le_of_1d`,
`remov.A_top_slot_bound` (`remov.TopCoreB.ATopClean`) and `BSlotTop.Gsum_bound_fts`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.ESW.Main
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_split
import Submission.Work.FTS.EllipticEst.TT.ESW.U_le_of_1d
import Submission.Work.FTS.EllipticEst.remov.high_slice_chain_slots
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.ATopClean
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.GsumBound
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.Defs
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.SliceAngGenFts

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

/-- The one-dimensional angular estimate `OneD k` of `TT.ESW`, supplied by the proved
`sliceAngGenFts`. -/
theorem oneDFts (k : ℕ) (hk : 2 ≤ k) : Work.FTS.EllipticEst.TT.ESW.OneD k := by
  obtain ⟨C, hCpos, hC⟩ := sliceAngGenFts k hk
  refine ⟨C, hCpos, ?_⟩
  intro γ u g hγ1 hγ2 hu hc h0 hpi hg hI1 hI2 hI3 hI4 hI5 hI6
  exact hC γ u g hγ1 hγ2 hu hc h0 hpi hg hI1 hI2 hI3 hI4 hI5 hI6

/-- **The `B`-half of the induction step of `prop:Hk`**: the top angular slot of `∂_θθΨ` is
controlled by `|F|_k`. -/
theorem B_slot_bound_fts (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  intro k hk
  obtain ⟨Cc, hCcpos, hchain⟩ :=
    Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform k (by omega)
  obtain ⟨CE, hCEpos, hE⟩ := Work.FTS.EllipticEst.TT.ESW.E_le_HkSq k (by omega)
  obtain ⟨Cj, hCjpos, hJ⟩ :=
    Work.FTS.EllipticEst.remov.high_slice_chain_slots D hD k (by omega)
  obtain ⟨Cs, hCspos, hsrc⟩ := Gsum_bound_fts D hD k hk
  obtain ⟨CU, hCUpos, hU⟩ :=
    Work.FTS.EllipticEst.TT.ESW.U_le_of_1d D hD k hk (oneDFts k (by omega))
  refine ⟨Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) + 1,
    by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hsmB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (hsm.pth).pth
  have memB : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := hwk.memB
  have memB' : Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
      (by omega) (Work.FTS.EllipticEst.SmoothOpen.forall hsmB) memB
  have hb : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ D * Work.Spaces.HkNorm α k F := by
    have h0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α (k - 1) _)
    linarith [h1]
  have hE' : EsumrC α k Ψ ≤ CE * Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
    hE α Ψ hα hsm memB'
  have hJ' : EjsumC α k Ψ ≤ Cj * Work.Spaces.HkSq α k F := hJ α F Ψ hα hα4 hwk hb h2
  have hsrc' : GsumC α k F Ψ ≤ Cs * Work.Spaces.HkSq α k F := hsrc α F Ψ hα hα4 hwk h1 h2
  have hη : EtaslC α Ψ ≤ Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.ESW.eta_slot_le memB'
  have hsplit : LoslC α Ψ ≤ 20 * EtaslC α Ψ :=
    Work.FTS.EllipticEst.TT.ESW.low_order_split hwk
  have hU' : UslC α k Ψ ≤ CU * (GsumC α k F Ψ + EjsumC α k Ψ + EtaslC α Ψ + LoslC α Ψ) := by
    simp only [UslC, GsumC, EjsumC, EtaslC, LoslC]
    have h := hU α F Ψ hα hα4 hwk h1 h2
    linarith [h]
  have hchain' : Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ) ≤
      Cc * (EsumrC α k Ψ + UslC α k Ψ) := hchain α Ψ hsm memB
  have hcase : Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hsq : Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        = (Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) _)]
    have hsq2 : Work.Spaces.HkSq α k F = (Work.Spaces.HkNorm α k F) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
    rw [hsq, hsq2]
    calc (Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)) ^ 2
        ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1) _) hb 2
      _ = D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 := by ring
  have hkey : Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ) ≤
      (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) * Work.Spaces.HkSq α k F := by
    have hE2 : EsumrC α k Ψ ≤ CE * (D ^ 2 * Work.Spaces.HkSq α k F) :=
      le_trans hE' (mul_le_mul_of_nonneg_left hcase hCEpos.le)
    have hU2 : UslC α k Ψ ≤ CU * (Cs * Work.Spaces.HkSq α k F
        + Cj * Work.Spaces.HkSq α k F + 21 * (Work.Spaces.HkSq α (k - 1)
            (Work.Spaces.pthIter 2 Ψ))) := by
      refine le_trans hU' ?_
      refine mul_le_mul_of_nonneg_left ?_ hCUpos.le
      linarith [hsrc', hJ', hη, hsplit]
    have hU3 : UslC α k Ψ ≤ CU * (Cs * Work.Spaces.HkSq α k F
        + Cj * Work.Spaces.HkSq α k F + 21 * (D ^ 2 * Work.Spaces.HkSq α k F)) := by
      refine le_trans hU2 ?_
      refine mul_le_mul_of_nonneg_left ?_ hCUpos.le
      linarith [hcase]
    refine le_trans hchain' ?_
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hE2 hU3) hCcpos.le) (le_of_eq ?_)
    ring
  have hfin : Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
      ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2)))
        * Work.Spaces.HkNorm α k F := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hkey) ?_
    rw [Real.sqrt_mul (by positivity)]
  have hnn : 0 ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) :=
    Real.sqrt_nonneg _
  calc Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
      ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2)))
        * Work.Spaces.HkNorm α k F := hfin
    _ ≤ (Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) + 1)
        * Work.Spaces.HkNorm α k F := by
        have := Work.Spaces.HkNorm_nonneg α k F
        nlinarith [hnn, this]

end Work.FTS.EllipticEst.Prop.BSlotTop
