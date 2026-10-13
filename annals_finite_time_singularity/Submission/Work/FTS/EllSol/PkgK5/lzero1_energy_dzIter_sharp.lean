import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.tracesK5Aux2
import Submission.Work.FTS.EllSol.PkgK5.SharpAux
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "Lzero1" => Work.FTS.EllipticEst.Lzero1

theorem lzero1_energy_dzIter_sharp {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 2)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ))
    (hFmem : Work.Spaces.HkMem α (k + 2) F)
    (j : ℕ) (hj : j ≤ k + 1) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.Lzero1
          (fun t => Work.Spaces.DzIter j X z t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F := Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hXsm
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j F z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hFsm hFmem j (by omega) hz
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hAsm hAh j (by omega) hz
  have hI3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) X z θ) ^ 2 * sEta θ) Iθ :=
    slotEnergy_dzIter_sharp hk h hAh (j + 1) (by omega) z hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * ((α ^ 2 * Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 * sEta θ)) Iθ :=
    ((hI2.const_mul (α ^ 4)).const_mul 3).congr
      (Filter.Eventually.of_forall (fun θ => by ring))
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * (((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) ^ 2
        * sEta θ)) Iθ :=
    ((hI3.const_mul ((α * (5 + α)) ^ 2)).const_mul 3).congr
      (Filter.Eventually.of_forall (fun θ => by ring))
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * ((Work.Spaces.DzIter j F z θ) ^ 2 * sEta θ)) Iθ := hI1.const_mul 3
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * ((Work.Spaces.DzIter j F z θ) ^ 2
        + (α ^ 2 * Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2
        + ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) ^ 2) * sEta θ) Iθ :=
    ((h1.add h2).add h3).congr (Filter.Eventually.of_forall (fun θ => by
      simp only [Pi.add_apply]; ring))
  have hLm : AEStronglyMeasurable
      (fun θ : ℝ => Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ) (volume.restrict Iθ) := by
    have hslice := aesm_slice_dzIter hXsm j hz
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => deriv (fun t => deriv (fun t' => Work.Spaces.DzIter j X z t') t) θ)
        (volume.restrict Iθ) := (measurable_deriv _).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun θ : ℝ => deriv (fun t => Real.tan t * Work.Spaces.DzIter j X z t) θ)
        (volume.restrict Iθ) := (measurable_deriv _).aestronglyMeasurable
    have hfun : (fun θ : ℝ => Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ)
        = fun θ : ℝ => -(deriv (fun t => deriv (fun t' => Work.Spaces.DzIter j X z t') t) θ)
            + deriv (fun t => Real.tan t * Work.Spaces.DzIter j X z t) θ
            - 6 * Work.Spaces.DzIter j X z θ := rfl
    rw [hfun]
    exact ((h1.neg).add h2).sub (hslice.const_mul 6)
  refine MeasureTheory.Integrable.mono' hdom ((hLm.pow 2).mul aesm_sEta_Iθ) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hS0 : 0 ≤ sEta θ :=
    Work.FTS.EllipticEst.remov.ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hS0)]
  rw [sliceEq_dzIter h j hz hθ]
  nlinarith [sq_nonneg (Work.Spaces.DzIter j F z θ
      - α ^ 2 * Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ),
    sq_nonneg (α ^ 2 * Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ
      - (α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ),
    sq_nonneg ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ - Work.Spaces.DzIter j F z θ)]

end Work.FTS.EllSol.PkgK5
