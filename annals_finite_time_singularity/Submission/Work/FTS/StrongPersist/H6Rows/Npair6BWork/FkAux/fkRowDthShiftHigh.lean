import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.topSlotZLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPairCS
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkMomentAe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux
import Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_absCS
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-- **The final arithmetic of the high-shift row.**  From the two weighted energies
`∫_μ g²ρA² ≤ C₁·S₄·(1+S)` and `∫_μ ρB² ≤ S` and the size `√S₄ ≤ M` of the datum, the
two-variable Cauchy–Schwarz price `√(C₁ S₄ (1+S))·√S` is dominated by
`(√C₁+1)(1+M)²(1+S)`.

(`√((1+S)S) ≤ 1+S`, `M ≤ (1+M)²` and `√C₁ ≤ √C₁+1` are the only inequalities used.) -/
private lemma fkShiftHigh_arith {C S₄ S M : ℝ} (hC : 0 < C) (hS₄ : 0 ≤ S₄) (hS : 0 ≤ S)
    (hM : 0 ≤ M) (h4 : Real.sqrt S₄ ≤ M) :
    Real.sqrt (C * S₄ * (1 + S)) * Real.sqrt S
      ≤ (Real.sqrt C + 1) * (1 + M) * (1 + M) * (1 + S) := by
  have hCs : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have h1S : 0 ≤ 1 + S := by linarith
  have hfac : Real.sqrt (C * S₄ * (1 + S))
      = Real.sqrt C * Real.sqrt S₄ * Real.sqrt (1 + S) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ C * S₄), Real.sqrt_mul hC.le]
  have hkey : Real.sqrt (C * S₄ * (1 + S)) * Real.sqrt S ≤ Real.sqrt C * M * (1 + S) := by
    have h1 : Real.sqrt (1 + S) * Real.sqrt S ≤ 1 + S := by
      have h2 : (1 + S) * S ≤ (1 + S) * (1 + S) := by nlinarith
      calc Real.sqrt (1 + S) * Real.sqrt S = Real.sqrt ((1 + S) * S) :=
            (Real.sqrt_mul h1S S).symm
        _ ≤ Real.sqrt ((1 + S) * (1 + S)) := Real.sqrt_le_sqrt h2
        _ = 1 + S := Real.sqrt_mul_self h1S
    rw [hfac]
    calc Real.sqrt C * Real.sqrt S₄ * Real.sqrt (1 + S) * Real.sqrt S
        = Real.sqrt C * Real.sqrt S₄ * (Real.sqrt (1 + S) * Real.sqrt S) := by ring
      _ ≤ Real.sqrt C * Real.sqrt S₄ * (1 + S) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.sqrt C * M * (1 + S) := by
          have h3 : Real.sqrt S₄ * (1 + S) ≤ M * (1 + S) :=
            mul_le_mul_of_nonneg_right h4 h1S
          calc Real.sqrt C * Real.sqrt S₄ * (1 + S)
              = Real.sqrt C * (Real.sqrt S₄ * (1 + S)) := by ring
            _ ≤ Real.sqrt C * (M * (1 + S)) := mul_le_mul_of_nonneg_left h3 hCs
            _ = Real.sqrt C * M * (1 + S) := by ring
  have hfin : Real.sqrt C * M * (1 + S)
      ≤ (Real.sqrt C + 1) * (1 + M) * (1 + M) * (1 + S) := by
    have hM2 : M ≤ (1 + M) * (1 + M) := by nlinarith
    have hX : 0 ≤ (1 + M) * (1 + M) := by positivity
    have h1 : Real.sqrt C * M * (1 + S)
        ≤ Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S) := by
      have h := mul_le_mul_of_nonneg_right hM2 h1S
      calc Real.sqrt C * M * (1 + S) = Real.sqrt C * (M * (1 + S)) := by ring
        _ ≤ Real.sqrt C * ((1 + M) * (1 + M) * (1 + S)) :=
            mul_le_mul_of_nonneg_left h hCs
        _ = Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S) := by ring
    have h2 : Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S)
        ≤ (Real.sqrt C + 1) * ((1 + M) * (1 + M)) * (1 + S) := by
      have h3 : Real.sqrt C * ((1 + M) * (1 + M))
          ≤ (Real.sqrt C + 1) * ((1 + M) * (1 + M)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
      exact mul_le_mul_of_nonneg_right h3 h1S
    refine le_trans h1 ?_
    calc Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S)
        ≤ (Real.sqrt C + 1) * ((1 + M) * (1 + M)) * (1 + S) := h2
      _ = (Real.sqrt C + 1) * (1 + M) * (1 + M) * (1 + S) := by ring
  exact le_trans hkey hfin

/-- **The assembly of the high-shift row.**  Abstract form: the two-variable
Cauchy–Schwarz `FkAux.fkShiftHigh_absCS` applied to the two weighted energies, followed by
`fkShiftHigh_arith`. -/
private lemma fkShiftHigh_assembly {μ : MeasureTheory.Measure (ℝ × ℝ)} {g : ℝ → ℝ}
    {A B ρ : ℝ → ℝ → ℝ} {C₁ S₄ S M : ℝ}
    (hC₁ : 0 < C₁) (hS₄ : 0 ≤ S₄) (hS : 0 ≤ S) (hM : 0 ≤ M) (hsqrt : Real.sqrt S₄ ≤ M)
    (hρ : ∀ᵐ p ∂μ, 0 ≤ ρ p.1 p.2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ)
    (hFint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2) μ)
    (hFbd : (∫ p, (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂μ) ≤ C₁ * S₄ * (1 + S))
    (hGint : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) μ)
    (hGbd : (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂μ) ≤ S) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ ∧
      |∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ|
        ≤ (Real.sqrt C₁ + 1) * (1 + M) * (1 + M) * (1 + S) := by
  obtain ⟨hint, hbd⟩ := fkShiftHigh_absCS (μ := μ) hρ haesm hFint hGint
  refine ⟨hint, ?_⟩
  refine hbd.trans ?_
  refine (mul_le_mul (Real.sqrt_le_sqrt hFbd) (Real.sqrt_le_sqrt hGbd)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans ?_
  exact fkShiftHigh_arith hC₁ hS₄ hS hM hsqrt

theorem fkRowDthShiftHigh : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      4 ≤ b₁ → b₁ ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fkShiftHigh_shiftF
  refine ⟨Real.sqrt C₁ + 1, by positivity, ?_⟩
  intro α hαmem f M ρ b₁ hDat hb₁4 hb₁6 hρ
  have hα0 : 0 < α := hαmem.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hDat.sm
  have h6 : Work.Spaces.HkMem α 6 f := hDat.h6
  have hS6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hS4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hsqrt4 : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ M := by
    simpa only [Work.Spaces.HkNorm] using hDat.bdd
  -- the `F²`-energy (the shift slot against the angular slot) and the `G²`-energy
  obtain ⟨hFint, hFbd⟩ := hC₁ α hαmem f M b₁ ρ hDat hb₁4 hb₁6 hρ
  obtain ⟨hGint, hGbd⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt (α := α) (f := f)
      (a := 0) (j := 6) (ρ := ρ) hα0 (by norm_num) hρ hsm h6
  -- the leaf weight is nonnegative a.e. on the product measure
  have hρae : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM, 0 ≤ ρ p.1 p.2 := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_PM_Q0] with p hp
    exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_nonneg (α := α) (a := 0) (ρ := ρ)
      hρ p.1 p.2 hp.1 hp.2.1 hp.2.2
  -- a.e. strong measurability of the pairing
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
            * Work.Spaces.mixed 6 0 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkMomentAe α f b₁ hsm h6 hb₁6
    have h2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_leafW (α := α) (a := 0) (ρ := ρ) hρ
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed hsm (6 - b₁) 1
    have h4 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.mixed 6 0 f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed hsm 6 0
    exact (h1.mul (h2.mul (h3.mul h4))).congr
      (Filter.Eventually.of_forall fun p => by simp only [Pi.mul_apply]; ring)
  exact fkShiftHigh_assembly hC₁pos hS4 hS6 hM0 hsqrt4 hρae haesm hFint hFbd hGint hGbd

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
