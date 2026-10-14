import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Common
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPieceBound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leafSlotSliceIntegrable
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.row_l12_dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem row_l12_dz : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
            * Work.Spaces.Dz f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cc, hCcpos, hCcsm, hCcbd, hCcg⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨C0, hC0pos, hC0bnd⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroTerm
  obtain ⟨C4, hC4pos, hsup4raw⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨C6, hC6pos, hsup6raw⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  refine ⟨49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ (4096 * 4096) * 49 * Cc * (2 * C4 + C6) := by positivity
    linarith [hC0pos]
  intro α hα f a b ρ hso hm6 hm7 hvan haxis hl12 hab hleaf
  have hα0 : (0 : ℝ) < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the `L₁₂`-jet bounds
  have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα0 hα1 hso hm7 (by norm_num)
    exact (h.of_le (by norm_num)).congr
      (fun z _ => (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm)
  have hsup4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hsup4raw α f hα0 hα1 hso hm6 hl12 k hk z hz
  have hsup6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun k hk z hz => hsup6raw α f hα0 hα1 hso hm6 hm7 hl12 k hk z hz
  -- ## the coefficient function
  set V : ℝ → ℝ → ℝ := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
    * Work.Spaces.Dz f z θ with hV
  -- ## the a.e. expansion of the paired integrand
  have hpt : (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      =ᵐ[((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i p) := by
    refine ae_prod_Ioo (p := fun z θ => ρ z θ * Work.Spaces.mixed b a V z θ
        * Work.Spaces.mixed b a f z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i (z, θ)) ?_
    intro θ hθ z hz
    have h := t5bPairExpand (ρ := ρ) hso hCcsm hXsm hab z θ hz hθ.1 hθ.2
    rwa [← hV] at h
  -- ## integrability of the individual summands
  have hIntPiece : ∀ k ∈ Finset.range (b + 1), ∀ i ∈ Finset.range (a + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => t5bPiece f ρ a b k i p)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro k hk i hi
    exact (Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable hα0 hα1 hso hCcsm
      hm6 hm7 hab hleaf hC4pos.le hC6pos.le hCcpos.le hsup4 hsup6 hCcbd hCcg
      (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2
  -- ## integrability of the sum and of the total integrand
  have hIntSum : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i p)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integrable_finsetSum _ fun k hk => ?_
    refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
    exact (hIntPiece k hk i hi).const_mul _
  have hIntTot : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hIntSum.congr hpt.symm
  -- ## the pairing as a product integral
  have hbridge : Work.FTS.TransportS.slotPairing ρ a b V f
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.TransportS.slotPairing]
    exact (MeasureTheory.integral_prod _ hIntTot).symm
  -- ## the expansion of the product integral
  have hlin : (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
          ((b.choose k : ℝ) * (a.choose i : ℝ))
            * (∫ p, t5bPiece f ρ a b k i p
                ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_congr_ae hpt]
    rw [MeasureTheory.integral_finsetSum _ (fun k hk =>
      MeasureTheory.integrable_finsetSum _ fun i hi => (hIntPiece k hk i hi).const_mul _)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun i hi => (hIntPiece k hk i hi).const_mul _)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_const_mul]
  -- ## the per-term bounds
  have hterm : ∀ k ∈ Finset.range (b + 1), ∀ i ∈ Finset.range (a + 1),
      |∫ p, t5bPiece f ρ a b k i p
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
        ≤ (if k = 0 ∧ i = 0
           then C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
           else ((b.choose k : ℝ) * (a.choose i : ℝ)) * Cc *
             (if k ≤ 4
              then C4 * Work.Spaces.HkNorm α 4 f
                   * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                      + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
              else C6 * Work.Spaces.HkNorm α 6 f
                   * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) := by
    intro k hk i hi
    have hkb : k ≤ b := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hia : i ≤ a := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hiter : (∫ p, t5bPiece f ρ a b k i p
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t5bPiece f ρ a b k i (z, θ) :=
      MeasureTheory.integral_prod _ (hIntPiece k hk i hi)
    rw [hiter]
    by_cases h00 : k = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [if_pos ⟨rfl, rfl⟩]
      have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t5bPiece f ρ a b 0 0 (z, θ))
          = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
              * (Work.Construction.c2m θ * Work.Construction.L12 f z)
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only [t5bPiece, Work.Elliptic.DzdIter_zero, Work.Spaces.DthIter_zero,
          Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
        ring
      rw [hcongr]
      exact hC0bnd α hα f a b ρ hso hm6 hm7 hvan haxis hl12 hab hleaf
    · rw [if_neg h00]
      exact Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPieceBound hα0 hα1 hso hm6 hab
        hleaf hC4pos.le hC6pos.le hCcpos.le hsup4 hsup6 hCcbd hCcg hkb hia h00
  -- ## normal form of the per-term bounds
  have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hZnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN6sq : Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f
      = Work.Spaces.HkSq α 6 f := by
    rw [Work.Spaces.HkNorm, ← pow_two, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
  have hS2 : (1 + Work.Spaces.HkNorm α 6 f ^ 2) = (1 + Work.Spaces.HkSq α 6 f) := by
    rw [pow_two, hN6sq]
  -- ## the sum of the per-term bounds
  have hmain : (∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ((b.choose k : ℝ) * (a.choose i : ℝ))
          * |∫ p, t5bPiece f ρ a b k i p
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|)
      ≤ 49 * (C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkNorm α 6 f ^ 2)
          + 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)))) := by
    refine le_trans (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => ?_)
      (t5bSumBound hC0pos.le hCcpos.le hC4pos.le hC6pos.le hXnn hZnn hab)
    by_cases h00 : k = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [if_pos ⟨rfl, rfl⟩, hS2]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
      have h := hterm 0 hk 0 hi
      rwa [if_pos ⟨rfl, rfl⟩] at h
    · rw [if_neg h00]
      have h := hterm k hk i hi
      rw [if_neg h00] at h
      have hb : b ≤ 6 := by omega
      have ha : a ≤ 6 := by omega
      have hc1 : ((b.choose k : ℕ) : ℝ) ≤ 64 := by
        have h2 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
        have h3 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb
        exact_mod_cast (le_trans h2 (le_trans h3 (by norm_num)))
      have hc2 : ((a.choose i : ℕ) : ℝ) ≤ 64 := by
        have h2 : a.choose i ≤ 2 ^ a := Nat.choose_le_two_pow a i
        have h3 : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) ha
        exact_mod_cast (le_trans h2 (le_trans h3 (by norm_num)))
      have hcf0 : (0 : ℝ) ≤ (b.choose k : ℝ) * (a.choose i : ℝ) := by positivity
      have hcf : ((b.choose k : ℝ) * (a.choose i : ℝ)) ≤ 4096 := by nlinarith
      have hcf2 : ((b.choose k : ℝ) * (a.choose i : ℝ))
            * ((b.choose k : ℝ) * (a.choose i : ℝ)) ≤ 4096 * 4096 := by
        nlinarith [hcf0, hcf]
      have hAnn : (0 : ℝ) ≤ C4 * Work.Spaces.HkNorm α 4 f
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
               + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f) := by positivity
      have hBnn : (0 : ℝ) ≤ C6 * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by positivity
      have hE : (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            else C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))
          ≤ C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by
        by_cases hk4 : k ≤ 4
        · rw [if_pos hk4]; linarith
        · rw [if_neg hk4]; linarith
      have hCE : Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            else C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))
          ≤ Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) :=
        mul_le_mul_of_nonneg_left hE hCcpos.le
      calc ((b.choose k : ℝ) * (a.choose i : ℝ))
            * |∫ p, t5bPiece f ρ a b k i p
                ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
          ≤ ((b.choose k : ℝ) * (a.choose i : ℝ))
              * (((b.choose k : ℝ) * (a.choose i : ℝ)) * Cc
                * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                    * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                       + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
                  else C6 * Work.Spaces.HkNorm α 6 f
                    * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) :=
            mul_le_mul_of_nonneg_left h hcf0
        _ = (((b.choose k : ℝ) * (a.choose i : ℝ))
              * ((b.choose k : ℝ) * (a.choose i : ℝ)))
              * (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                  * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                     + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
                else C6 * Work.Spaces.HkNorm α 6 f
                  * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) := by ring
        _ ≤ (4096 * 4096) * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) :=
            mul_le_mul hcf2 hCE (by positivity) (by norm_num)
        _ = 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) := by ring
  -- ## the bound on the pairing
  have hbound : |Work.FTS.TransportS.slotPairing ρ a b V f|
      ≤ 49 * (C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkNorm α 6 f ^ 2)
          + 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)))) := by
    rw [hbridge, hlin]
    refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun k hk => Finset.abs_sum_le_sum_abs _ _)) ?_
    refine le_trans (le_of_eq ?_) hmain
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun i hi => ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  -- ## the final bound
  have hfin := t5bFinalArith (X := Work.Spaces.HkNorm α 4 f)
    (Y := Work.Spaces.HkNorm α 6 f) (α := α)
    hC0pos.le hCcpos.le hC4pos.le hC6pos.le hXnn hZnn hα0 hα1
  have hXn : Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f := rfl
  calc |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
          * Work.Spaces.Dz f z θ) f|
      = |Work.FTS.TransportS.slotPairing ρ a b V f| := by rw [hV]
    _ ≤ 49 * (C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkNorm α 6 f ^ 2)
          + 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)))) := hbound
    _ ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkNorm α 6 f ^ 2) := hfin
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          rw [hS2]
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          rw [hXn]

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45aRow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `T45aRow` — the level-six transport row with the coefficient `L₁₂(f)·A`

The pairing `slotPairing ρ a b (fun z θ => L₁₂(f)(z)·A(z,θ)) f` is a slot of the transport term
of the modulated equation in which the *coefficient* is the product of the radial primitive
`L₁₂(f)` of the datum and an independent `𝒲^{6,∞}`-bounded perturbation `A`.

**Route.**  `L₁₂(f)` is θ-independent, so the Leibniz rule for a radial factor
(`leibniz_radial_mul`) expands the slot into
`∑_{k ≤ b} C(b,k)·(D_z^k L₁₂ f)(z)·(D_z^{b-k}D_θ^a A)(z,θ)`, and each `A`-slot is bounded
pointwise by `C·K·Abnd α a θ` (`T45AslotLe`).  The angular factor `Abnd` is what makes the
leftover angular weight integrable against the leaf weight of the slot: for `a = 0` it is `1`
and the leaf weight is `w²·sin(2θ)^{-η}`, while for `a ≥ 1` the exponent
`-γ(α) + 2α/5 = -1 + 3α/10 > -1` keeps `∫ sin(2θ)^{-γ}·Abnd²` finite and `≤ D/α`
(`T45AbndInts`).  Cauchy–Schwarz on the angular slice produces `√(∫_θ σ·V²)`, which is
`Λ/w`, and the weighted slot bound `∫_z (D_z^k L₁₂ f)² w² ≤ C_L·|f|²_{ℋ⁶}` (`L12slotLe7`)
together with an AM–GM in `z` closes the estimate (`T45Common`).  The `α^{-1/2}` accumulated
from `D/α` is absorbed into the `α^{-3}` of the statement.
-/

/-- **The level-six transport row with the coefficient `L₁₂(f)·A`.** -/
theorem T45aRow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => Work.Construction.L12 f z * A z θ) f|
        ≤ C * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CL, hCLpos, hL12⟩ := L12slotLe7
  obtain ⟨CA, hCApos, hAslot⟩ := T45AslotLe
  obtain ⟨D, hDpos, hD⟩ := T45AbndInts
  refine ⟨CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1, by positivity, ?_⟩
  intro α hα f A a b ρ K hso hm6 hm7 hvanish haxis hl12 hAso hAmem hAle hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hb : b ≤ 6 := by omega
  have hCA0 : 0 ≤ CA := le_of_lt hCApos
  have hD0 : 0 ≤ D := le_of_lt hDpos
  have hCL0 : 0 ≤ CL := le_of_lt hCLpos
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ Work.Spaces.WlInf α 6 A := by
      rw [Work.Spaces.WlInf]
      exact add_nonneg (Work.Spaces.wlZSum_nonneg α 6 A hAmem)
        (Work.Spaces.wlThSum_nonneg α 6 A hAmem)
    linarith
  have hAop : ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CA * K * Abnd α i θ :=
    fun j i hji z θ hz h1 h2 => hAslot α hα A K hAso hAmem hAle j i hji z θ hz h1 h2
  have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
      (by norm_num : 2 ≤ 7)).1
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h
  have hXint : ∀ k : ℕ, k ≤ 6 → MeasureTheory.IntegrableOn (fun z =>
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := fun k hk =>
    (hL12 α f hα0 hα1 hso hm6 hm7 hl12 k (le_trans hk (by norm_num))).1
  have hXbd : ∀ k : ℕ, k ≤ 6 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ CL * Work.Spaces.HkSq α 6 f := fun k hk =>
    (hL12 α f hα0 hα1 hso hm6 hm7 hl12 k (le_trans hk (by norm_num))).2
  have hXaesm : ∀ k : ℕ, k ≤ 6 → AEStronglyMeasurable (fun z =>
      Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      (volume.restrict Work.Spaces.Iz) := by
    intro k hk
    have hcont : ContinuousOn (fun z => Work.Elliptic.DzdIter k
        (fun z => Work.Construction.L12 f z) z) (Set.Ioi 0) :=
      (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial
        (r := fun z => Work.Construction.L12 f z) (n := 6)
        (fun m hm => hXsm.of_le (by exact_mod_cast hm)) (a := k) (t := 0)
        (by omega)).continuousOn
    have h1 : AEStronglyMeasurable (fun z => Work.Elliptic.DzdIter k
        (fun z => Work.Construction.L12 f z) z) (volume.restrict (Set.Ioi 0)) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    rw [restrict_Ioi_eq_restrict_Iz] at h1
    exact h1
  have hfin : CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
        * (1 + Work.Spaces.HkSq α 6 f)
      ≤ (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * K * α ^ (-(3 : ℝ))
        * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
    have hCfin0 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 := by positivity
    have h3 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K := mul_nonneg hCfin0 hK0
    have h4 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith [hHknn]
    have h5 : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα0.le _
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have hpow : (1 : ℝ) ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 :=
      one_le_pow₀ (by linarith)
    have hαp : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
    have hst1 : CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f) := by
      refine mul_le_mul_of_nonneg_right ?_ h4
      exact mul_le_mul_of_nonneg_left hαp h3
    have hst2 : CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * K * α ^ (-(3 : ℝ))
          * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
      have h6 : (1 + Work.Spaces.HkSq α 6 f)
          ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
        calc (1 + Work.Spaces.HkSq α 6 f) = 1 * (1 + Work.Spaces.HkSq α 6 f) := by ring
          _ ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
              mul_le_mul_of_nonneg_right hpow h4
      have h7 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ)) :=
        mul_nonneg h3 h5
      refine (mul_le_mul_of_nonneg_left h6 h7).trans ?_
      have h8 : CA * Real.sqrt D * (10000000 * CL + 1) / 2
          ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1 := by linarith
      have h9 : 0 ≤ K * α ^ (-(3 : ℝ))
          * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_nonneg (mul_nonneg hK0 h5) (mul_nonneg (pow_nonneg (by linarith) 4) h4)
      calc CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ))
              * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
          = (CA * Real.sqrt D * (10000000 * CL + 1) / 2) * (K * α ^ (-(3 : ℝ))
              * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) := by ring
        _ ≤ (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * (K * α ^ (-(3 : ℝ))
              * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) :=
            mul_le_mul_of_nonneg_right h8 h9
        _ = (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * K * α ^ (-(3 : ℝ))
              * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring
    exact hst1.trans hst2
  rcases hleaf with rfl | rfl | ⟨ha1, rfl⟩
  · exact (T45common hα0 hα1 hso hAso hm6 hCL0 hCA0 hD0 hK0 hHknn hAop (fun z θ => rfl)
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
      ((hD α hα).1 a).1 ((hD α hα).1 a).2 (Or.inl rfl) hab hb hXsm hXint hXbd hXaesm).trans hfin
  · refine (T45common hα0 hα1 hso hAso hm6 hCL0 hCA0 hD0 hK0 hHknn hAop
      (fun z θ => by simp [Work.FTS.TransportS.leafOne]) (fun θ hθ => zero_le_one)
      ?_ ?_ (Or.inr (Or.inl rfl)) hab hb hXsm hXint hXbd hXaesm).trans hfin
    · simpa only [one_mul] using ((hD α hα).2.1 a).1
    · simpa only [one_mul] using ((hD α hα).2.1 a).2
  · exact (T45common hα0 hα1 hso hAso hm6 hCL0 hCA0 hD0 hK0 hHknn hAop (fun z θ => rfl)
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
      ((hD α hα).2.2 a ha1).1 ((hD α hα).2.2 a ha1).2 (Or.inr (Or.inr ⟨ha1, rfl⟩)) hab hb
      hXsm hXint hXbd hXaesm).trans hfin

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
