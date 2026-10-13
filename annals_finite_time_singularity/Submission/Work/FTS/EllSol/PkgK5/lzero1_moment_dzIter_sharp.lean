import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

theorem lzero1_moment_dzIter_sharp {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 2)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ))
    (hFmem : Work.Spaces.HkMem α (k + 2) F)
    (hmom : ∀ i : ℕ, i ≤ k + 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i X) z = 0)
    (hmomF : ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i F) z = 0)
    (j : ℕ) (hj : j ≤ k + 1) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1
        (fun t => Work.Spaces.DzIter j X z t) θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F := Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hXsm
  -- the four slot energies
  have hE1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j F z θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hFsm hFmem j (by omega) hz
  have hE2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hAsm hAh j (by omega) hz
  have hE3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) X z θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    slotEnergy_dzIter_sharp hk h hAh (j + 1) (by omega) z hz
  have hE4 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter (j + 2) X z θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    slotEnergy_dzIter_sharp hk h hAh (j + 2) (by omega) z hz
  obtain ⟨hF1, _⟩ :=
    Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hFsm j hz) hE1
  obtain ⟨hA1, _⟩ :=
    Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hAsm j hz) hE2
  obtain ⟨hX1, _⟩ :=
    Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hXsm (j + 1) hz) hE3
  obtain ⟨hX2, _⟩ :=
    Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hXsm (j + 2) hz) hE4
  -- the corresponding integrabilities in the distributed shape
  have hA1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α ^ 2 * Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) *
        Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (hA1.const_mul (α ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hX1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) *
        Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (hX1.const_mul (α * (5 + α))).congr (Filter.Eventually.of_forall (fun θ => by ring))
  -- split the integral through the slice equation
  have key : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1
        (fun t => Work.Spaces.DzIter j X z t) θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ)
        + (∫ θ in Work.Spaces.Iθ, (α ^ 2 * Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) *
              Work.Elliptic.sinCos2 θ)
        + (∫ θ in Work.Spaces.Iθ, ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) *
            Work.Elliptic.sinCos2 θ) := by
    have hfun : (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1
          (fun t => Work.Spaces.DzIter j X z t) θ * Work.Elliptic.sinCos2 θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ
          + (α ^ 2 * Work.Spaces.DzIter j
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) *
                Work.Elliptic.sinCos2 θ
          + ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) *
                Work.Elliptic.sinCos2 θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [sliceEq_dzIter h j hz hθ]
      ring
    rw [MeasureTheory.integral_congr_ae hfun]
    exact integral_Iθ_add_three hF1 hA1' hX1'
  have e2 : (∫ θ in Work.Spaces.Iθ, (α ^ 2 * Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) *
          Work.Elliptic.sinCos2 θ)
      = α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) z := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun θ => by ring : ∀ θ : ℝ,
        (α ^ 2 * Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) *
            Work.Elliptic.sinCos2 θ
          = α ^ 2 * (Work.Spaces.DzIter j
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ *
                Work.Elliptic.sinCos2 θ))),
      MeasureTheory.integral_const_mul]
    rfl
  have e3 : (∫ θ in Work.Spaces.Iθ, ((α * (5 + α)) *
        Work.Spaces.DzIter (j + 1) X z θ) * Work.Elliptic.sinCos2 θ)
      = (α * (5 + α)) * Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) X) z := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun θ => by ring : ∀ θ : ℝ,
        ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) * Work.Elliptic.sinCos2 θ
          = (α * (5 + α)) * (Work.Spaces.DzIter (j + 1) X z θ *
              Work.Elliptic.sinCos2 θ))),
      MeasureTheory.integral_const_mul]
    rfl
  -- the middle moment via the `A`-identity
  have hAeq : Work.Elliptic.Fstar (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 2) X) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) X) z := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
    have hcongr2 : (fun θ : ℝ => Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ *
            Work.Elliptic.sinCos2 θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Work.Spaces.DzIter (j + 2) X z θ
          - Work.Spaces.DzIter (j + 1) X z θ) * Work.Elliptic.sinCos2 θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hXsm j hz hθ]
    rw [MeasureTheory.integral_congr_ae hcongr2,
      show (fun θ : ℝ => (Work.Spaces.DzIter (j + 2) X z θ
          - Work.Spaces.DzIter (j + 1) X z θ) * Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => Work.Spaces.DzIter (j + 2) X z θ * Work.Elliptic.sinCos2 θ
            - Work.Spaces.DzIter (j + 1) X z θ * Work.Elliptic.sinCos2 θ
          from funext fun θ => by ring,
      MeasureTheory.integral_sub hX2 hX1]
  rw [key, e2, e3, hAeq,
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z from rfl,
    hmomF j (by omega) z hz, hmom (j + 1) (by omega) z hz, hmom (j + 2) (by omega) z hz]
  ring

end Work.FTS.EllSol.PkgK5
