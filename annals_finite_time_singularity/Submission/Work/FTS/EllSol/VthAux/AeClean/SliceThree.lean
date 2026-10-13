/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeClean.SliceThree` — the pointwise `j ≤ 3` slices of `ellShift α g Ψ`, clean cone

Part of the clean re-proof of `Work.FTS.EllSol.VthAux.ellShift_slice_continuous_ae_clean`
(see that file's header for why the module `VthAux.ellWeakPos4_rightTendsto` has to be avoided):
the pointwise `j ≤ 3` instances of the slice continuity, copied from the proved lemmas of
`VthAux/ellShift_slice_continuous.lean` — the module carrying them also carries the refuted
pointwise `j = 4` statement, so they are reproduced here.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.AeClean

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "SmoothOpen" => Work.FTS.EllipticEst.SmoothOpen

/-- `∂_θ^i f` is `C^∞` on the open quadrant whenever `f` is.

Verbatim copy of `Work.FTS.EllSol.smoothOpen_pthIter`
(`Submission/Work/FTS/EllSol/removingL12ClassO.lean`), the only declaration of that module used by
the right-endpoint argument of the sibling module. -/
theorem pthIter_smoothOpen_fts {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (i : ℕ) :
    SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Slice regularity of the weak class (the `ContinuousOn` conjunct of
`remov.weakSliceRegular`, whose `α ≤ 1/4` hypothesis is never used). -/
theorem sliceContinuous_of_weakPos_fts (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ContinuousOn (fun θ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  intro z hz
  have hΨ : SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hsm : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hΨ hz
  have h7 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice (hΨ.pth).pth h.memB 0 (by omega) hz
  obtain ⟨C, _hCpos, hC⟩ :=
    Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm (by simpa using h7)
  have h5 : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Iθ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := C ^ 2)
        (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz).pow 2) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : 0 ≤ (C - Ψ z θ) * (C + Ψ z θ) :=
      mul_nonneg (by linarith [le_abs_self (Ψ z θ), (hC θ hθ).2])
        (by linarith [neg_le_abs (Ψ z θ), (hC θ hθ).2])
    nlinarith [h1]
  have hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_Lzero1_energy_integrable hα hk h hz
  have hmom : (∫ θ in Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ) = 0 :=
    (Work.FTS.EllipticEst.remov.wsMomentIdentity h hk
      (Work.FTS.EllipticEst.remov.wsMomentChain α k F Ψ hα hk h)
      (fun z' hz' => by
        have hpz := Work.FTS.EllipticEst.remov.ws_pz_energy_integrable
          (α := α) (k := k) (F := F) hk h hz'
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Work.Spaces.pz Ψ z' θ * Work.Elliptic.sinCos2 θ) Iθ :=
          (Work.FTS.EllipticEst.remov.ws_absMoment
            (Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pz) hz') hpz).1
        exact (h1.const_mul z').congr
          (Filter.Eventually.of_forall (fun θ => by
            simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
            ring)))
      (fun z' hz' θ hθ' => Work.FTS.EllipticEst.remov.DzIter_two_eq hΨ hz' hθ'))
      z hz
  exact Work.FTS.EllipticEst.remov.ws_continuousOn_Icc hsm.continuousOn (h.zero z) (h.pi_half z)
    (Work.FTS.EllipticEst.remov.wsSliceLeft hsm h7 hL hmom)
    (Work.FTS.EllipticEst.remov.sliceTendstoRight_fts hsm h7 hL h5)

/-- The derivable part of the slice-continuity statement: the pointwise `j ≤ 3` instances. -/
theorem ellShift_slice_le_three_clean (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn)
    (hα : 0 < α) (hg : Work.FTS.Nonlin.GalClass α g) (hO : Work.FTS.EllSol.EllClassO α g Ψ)
    (j : ℕ) (hj : j ≤ 3) (z : ℝ) (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Ψ) z θ)
      Work.Spaces.Iθ := by
  have hwk4 : Work.FTS.EllipticEst.TT.EllWeakPos α 4
      (Work.Elliptic.orthSource g) (Work.FTS.EllSol.ellShift α g Ψ) := hO.weakPos'
  have hwk3 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 4) (by norm_num) hwk4
  have hwk2 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 3) (by norm_num) hwk3
  have hwk1 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 2) (by norm_num) hwk2
  interval_cases j
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_zero] using
      (sliceContinuous_of_weakPos_fts 4 (by norm_num) α _ _ hα hwk4 z hz)
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      (sliceContinuous_of_weakPos_fts 3 (by norm_num) α _ _ hα hwk3 z hz)
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      (sliceContinuous_of_weakPos_fts 2 (by norm_num) α _ _ hα hwk2 z hz)
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      (sliceContinuous_of_weakPos_fts 1 (by norm_num) α _ _ hα hwk1 z hz)

end

end Work.FTS.EllSol.VthAux.AeClean
