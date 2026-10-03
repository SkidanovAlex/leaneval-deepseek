/-
# Area A5: the gain endpoints with the improvement bound as an explicit hypothesis

`gainEndpoint_explicit` is `gainEndpoint₁ ∧ gainEndpoint₂` of `Endpoints.lean` with the
`ImprovKMT` hypothesis replaced by the *explicit* improvement bound `hbound`: a fixed decay rate
`c`, a fixed constant `Cimp`, and the `ℓ² ⊗ ℓ² → ℓ¹` bound with weight
`2^{-c l} + (Log N)^{-c/ρ}` for every pair of `ℓ²` functions one of which is killed by the
corresponding projection.  The proof is the same computation as in `gainEndpoint₁`/`gainEndpoint₂`
(the loss of the inputs relative to `u`, `v` at constants `1 + C₂₂`, `1 + C₂₃` folded into
`Cimp + 1`), with two bookkeeping points:

* the exponent `l = L - 1` of the improvement bound gives `2^{-c(L-1)}`, matching the weight
  `improvWeight c ρ L N`;
* the middle constant of the second bound is `C₂₂ · ((Cimp + 1)(1 + C₂₃))`, which *vanishes* when
  `C₂₂ = 0`; in that case the projection bound `hproj₂` forces `kmtProj ρ L K u = 0`, hence
  `minorArc₂ = 0`, and the estimate is trivial.  (`endpoint_trivial` requires a non-zero
  constant, so this case is split off.)
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Endpoints

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Submission.PointwiseErgodicTheorems

theorem gainEndpoint_explicit {P : Polynomial ℤ} {ρ c : ℝ} (hc : 0 < c) {Cimp : NNReal}
    (hbound : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      (Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) f = 0 ∨
        Work.KMTContract.kmtProj ρ l
          ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) g = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ =>
          Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ
            (N : NNReal) Polynomial.X P f g x) 1 MeasureTheory.Measure.count
        ≤ (Cimp : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))
            + (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c / ρ)))
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
    {N : ℕ} (hN : 1 ≤ N) {L : ℕ} (hL : 1 ≤ L) {K K₂ : ℤ}
    (hLK : K = -(Work.Analysis.EndVar.logN N) + (L : ℤ))
    (hLK₂ : K₂ = -(((P.natDegree : ℕ) : ℤ) * Work.Analysis.EndVar.logN N)
        + ((P.natDegree : ℕ) : ℤ) * (L : ℤ))
    (hcomp₁ : ∀ u : ℤ → ℂ, Work.KMTAreas.A5.BoundedZ u →
      Work.KMTContract.kmtProj ρ (L - 1) (K - 1) (u - Work.KMTContract.kmtProj ρ L K u) = 0)
    (hcomp₂ : ∀ u : ℤ → ℂ, Work.KMTAreas.A5.BoundedZ u →
      Work.KMTContract.kmtProj ρ (L - 1) (K₂ - ((P.natDegree : ℕ) : ℤ))
        (u - Work.KMTContract.kmtProj ρ L K₂ u) = 0)
    {C₂₂ : NNReal} (hproj₂ : ∀ u : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ L K u) 2 MeasureTheory.Measure.count
        ≤ (C₂₂ : ENNReal) * MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count)
    {C₂₃ : NNReal} (hproj₃ : ∀ u : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ L K₂ u) 2 MeasureTheory.Measure.count
        ≤ (C₂₃ : ENNReal) * MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count) :
    (∀ u v : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTAreas.A5.minorArc₁ ρ L K (N : NNReal) P u v) 1
          MeasureTheory.Measure.count
        ≤ (((Cimp + 1) * (1 + C₂₂) : NNReal) : ENNReal)
            * (Work.KMTAreas.A5.improvWeight c ρ L N : ENNReal)
            * MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm v 2 MeasureTheory.Measure.count) ∧
    (∀ u v : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTAreas.A5.minorArc₂ ρ L K K₂ (N : NNReal) P u v) 1
          MeasureTheory.Measure.count
        ≤ ((C₂₂ * ((Cimp + 1) * (1 + C₂₃)) : NNReal) : ENNReal)
            * (Work.KMTAreas.A5.improvWeight c ρ L N : ENNReal)
            * MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm v 2 MeasureTheory.Measure.count) := by
  constructor
  · -- the gain estimate for the first minor-arc part
    have hcoef : ((Cimp + 1) * (1 + C₂₂) : ℝ≥0) ≠ 0 :=
      (by positivity : (0 : ℝ≥0) < (Cimp + 1) * (1 + C₂₂)).ne'
    have hMne : ((((Cimp + 1) * (1 + C₂₂) : ℝ≥0)) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
        ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.mpr hcoef)
        (ENNReal.coe_ne_zero.mpr (improvWeight_pos c ρ L N).ne')
    refine endpoint_trivial (fun u v => minorArc₁ ρ L K (N : ℝ≥0) P u v)
      (p := 2) (q := 2) (r := 1)
      (M := ((((Cimp + 1) * (1 + C₂₂) : ℝ≥0)) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞))
      hMne (by norm_num) (by norm_num)
      (by intro v; exact minorArc₁_zero_left ρ L K (N : ℝ≥0) P v)
      (by intro u; exact minorArc₁_zero_right ρ L K (N : ℝ≥0) P u) ?_
    intro u v hu hv
    have hmu : MemLp u 2 Measure.count :=
      MeasureTheory.memLp_iff.mpr hu
    have hmv : MemLp v 2 Measure.count :=
      MeasureTheory.memLp_iff.mpr hv
    have hbu : BoundedZ u := boundedZ_of_memLp (by norm_num) hmu
    have hPilt : eLpNorm (kmtProj ρ L K u) 2 Measure.count < ⊤ :=
      lt_of_le_of_lt (hproj₂ u) (ENNReal.mul_lt_top ENNReal.coe_lt_top hu)
    have hPimem : MemLp (kmtProj ρ L K u) 2 Measure.count :=
      MeasureTheory.memLp_iff.mpr hPilt
    have hPbdd : BoundedZ (kmtProj ρ L K u) := boundedZ_of_memLp (by norm_num) hPimem
    have hwmem : MemLp (u - kmtProj ρ L K u) 2 Measure.count := hmu.sub hPimem
    have hzero : kmtProj ρ (L - 1) (-(logN N) + ((L - 1 : ℕ) : ℤ))
        (u - kmtProj ρ L K u) = 0 := by
      have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by
        push_cast [Nat.cast_sub hL]
        ring
      have : (-(logN N) + ((L - 1 : ℕ) : ℤ) : ℤ) = K - 1 := by
        rw [hcast, hLK]; ring
      rw [this]
      exact hcomp₁ u hbu
    have hgain := hbound N (L - 1) (u - kmtProj ρ L K u) v hN hwmem hmv (Or.inl hzero)
    have hW : ((2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ)))
        = ((2 : ℝ) ^ (-(c * (((L - 1 : ℕ) : ℝ)))) + ((logN N : ℝ)) ^ (-(c / ρ))) := by
      have hcast : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
        push_cast [Nat.cast_sub hL]
        ring
      rw [hcast]
    have hsub : eLpNorm (u - kmtProj ρ L K u) 2 Measure.count
        ≤ (((1 : ℝ≥0) + C₂₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count := by
      refine (eLpNorm_sub_le
        (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).trans ?_
      calc eLpNorm u 2 Measure.count + eLpNorm (kmtProj ρ L K u) 2 Measure.count
          ≤ eLpNorm u 2 Measure.count + (C₂₂ : ℝ≥0∞) * eLpNorm u 2 Measure.count :=
            add_le_add_right (hproj₂ u) _
        _ = (((1 : ℝ≥0) + C₂₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count := by
            push_cast
            ring
    rw [minorArc₁]
    have hgain' : eLpNorm (AhalfR TZ (N : ℝ≥0) X P (u - kmtProj ρ L K u) v) 1 Measure.count
        ≤ (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
            * eLpNorm (u - kmtProj ρ L K u) 2 Measure.count * eLpNorm v 2 Measure.count := by
      rw [improvWeight_coe c ρ L N, hW]
      exact hgain
    have hAB : eLpNorm (u - kmtProj ρ L K u) 2 Measure.count
        ≤ ((((1 : ℝ≥0) + C₂₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count := hsub
    have hconst : (Cimp : ℝ≥0∞) * ((((1 : ℝ≥0) + C₂₂) : ℝ≥0) : ℝ≥0∞)
        ≤ ((((Cimp + 1) * ((1 : ℝ≥0) + C₂₂)) : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul]
      refine ENNReal.coe_le_coe.mpr ?_
      show Cimp * ((1 : ℝ≥0) + C₂₂) ≤ (Cimp + 1) * ((1 : ℝ≥0) + C₂₂)
      exact mul_le_mul_of_nonneg_right (by simp) (by positivity)
    refine hgain'.trans ?_
    calc (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
          * eLpNorm (u - kmtProj ρ L K u) 2 Measure.count * eLpNorm v 2 Measure.count
        ≤ (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
          * (((((1 : ℝ≥0) + C₂₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count)
          * eLpNorm v 2 Measure.count :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAB (by positivity)) (by positivity)
      _ ≤ (((Cimp + 1) * ((1 : ℝ≥0) + C₂₂) : ℝ≥0) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
          * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
          have h1 : (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
              * (((((1 : ℝ≥0) + C₂₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count)
              * eLpNorm v 2 Measure.count
              = ((Cimp : ℝ≥0∞) * ((((1 : ℝ≥0) + C₂₂) : ℝ≥0) : ℝ≥0∞))
                * (improvWeight c ρ L N : ℝ≥0∞) * eLpNorm u 2 Measure.count
                * eLpNorm v 2 Measure.count := by ring
          rw [h1]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (by positivity))
              (by positivity)) (by positivity)
  · by_cases hC0 : C₂₂ = 0
    · -- degenerate case: the first projection vanishes identically
      intro u v
      have hproj0 : kmtProj ρ L K u = 0 := by
        have h := hproj₂ u
        rw [hC0] at h
        simp only [ENNReal.coe_zero, zero_mul] at h
        exact eq_zero_of_eLpNorm_count_eq_zero (p := 2) (by norm_num) (le_antisymm h bot_le)
      have hz : minorArc₂ ρ L K K₂ (N : ℝ≥0) P u v = 0 := by
        rw [minorArc₂, hproj0, AhalfR_zero_left]
      rw [hz, eLpNorm_zero, hC0]
      simp
    · -- the gain estimate for the second minor-arc part
      have hcoef : (C₂₂ * ((Cimp + 1) * (1 + C₂₃)) : ℝ≥0) ≠ 0 :=
        mul_ne_zero hC0 (by positivity : (0 : ℝ≥0) < (Cimp + 1) * (1 + C₂₃)).ne'
      have hMne : (((C₂₂ * ((Cimp + 1) * (1 + C₂₃)) : ℝ≥0)) : ℝ≥0∞)
          * (improvWeight c ρ L N : ℝ≥0∞) ≠ 0 :=
        mul_ne_zero (ENNReal.coe_ne_zero.mpr hcoef)
          (ENNReal.coe_ne_zero.mpr (improvWeight_pos c ρ L N).ne')
      refine endpoint_trivial (fun u v => minorArc₂ ρ L K K₂ (N : ℝ≥0) P u v)
        (p := 2) (q := 2) (r := 1)
        (M := ((C₂₂ * ((Cimp + 1) * (1 + C₂₃)) : ℝ≥0) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞))
        hMne (by norm_num) (by norm_num)
        (by intro v; exact minorArc₂_zero_left ρ L K K₂ (N : ℝ≥0) P v)
        (by intro u; exact minorArc₂_zero_right ρ L K K₂ (N : ℝ≥0) P u) ?_
      intro u v hu hv
      have hmu : MemLp u 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr hu
      have hmv : MemLp v 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr hv
      have hPmem : MemLp (kmtProj ρ L K u) 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt (hproj₂ u) (ENNReal.mul_lt_top ENNReal.coe_lt_top hu))
      have hQmem : MemLp (kmtProj ρ L K₂ v) 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt (hproj₃ v) (ENNReal.mul_lt_top ENNReal.coe_lt_top hv))
      have hvsub : MemLp (v - kmtProj ρ L K₂ v) 2 Measure.count := hmv.sub hQmem
      have hzero : kmtProj ρ (L - 1) ((P.natDegree : ℤ) * (-(logN N) + ((L - 1 : ℕ) : ℤ)))
          (v - kmtProj ρ L K₂ v) = 0 := by
        have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by
          push_cast [Nat.cast_sub hL]
          ring
        have : ((P.natDegree : ℤ) * (-(logN N) + ((L - 1 : ℕ) : ℤ)))
            = K₂ - ((P.natDegree : ℕ) : ℤ) := by
          rw [hcast, hLK₂]; ring
        rw [this]
        exact hcomp₂ v (boundedZ_of_memLp (by norm_num) hmv)
      have hgain := hbound N (L - 1) (kmtProj ρ L K u) (v - kmtProj ρ L K₂ v) hN hPmem hvsub
        (Or.inr hzero)
      have hW : ((2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ)))
          = ((2 : ℝ) ^ (-(c * (((L - 1 : ℕ) : ℝ)))) + ((logN N : ℝ)) ^ (-(c / ρ))) := by
        have hcast : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
          push_cast [Nat.cast_sub hL]
          ring
        rw [hcast]
      have hQsub : eLpNorm (v - kmtProj ρ L K₂ v) 2 Measure.count
          ≤ ((((1 : ℝ≥0) + C₂₃) : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count := by
        refine (eLpNorm_sub_le
          (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).trans ?_
        calc eLpNorm v 2 Measure.count + eLpNorm (kmtProj ρ L K₂ v) 2 Measure.count
            ≤ eLpNorm v 2 Measure.count + (C₂₃ : ℝ≥0∞) * eLpNorm v 2 Measure.count :=
              add_le_add_right (hproj₃ v) _
          _ = (((1 : ℝ≥0) + C₂₃ : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count := by
              push_cast
              ring
      rw [minorArc₂]
      have hgain' : eLpNorm (AhalfR TZ (N : ℝ≥0) X P (kmtProj ρ L K u)
            (v - kmtProj ρ L K₂ v)) 1 Measure.count
          ≤ (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
              * eLpNorm (kmtProj ρ L K u) 2 Measure.count
              * eLpNorm (v - kmtProj ρ L K₂ v) 2 Measure.count := by
        rw [improvWeight_coe c ρ L N, hW]
        exact hgain
      refine hgain'.trans ?_
      calc (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
            * eLpNorm (kmtProj ρ L K u) 2 Measure.count
            * eLpNorm (v - kmtProj ρ L K₂ v) 2 Measure.count
          ≤ (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
            * ((C₂₂ : ℝ≥0∞) * eLpNorm u 2 Measure.count)
            * (((((1 : ℝ≥0) + C₂₃) : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hproj₂ u) (by positivity)) hQsub
              (by positivity) (by positivity)
        _ ≤ (((C₂₂ * ((Cimp + 1) * (1 + C₂₃)) : ℝ≥0)) : ℝ≥0∞)
            * (improvWeight c ρ L N : ℝ≥0∞) * eLpNorm u 2 Measure.count
            * eLpNorm v 2 Measure.count := by
            rw [show (Cimp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
                  * ((C₂₂ : ℝ≥0∞) * eLpNorm u 2 Measure.count)
                  * (((((1 : ℝ≥0) + C₂₃) : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count)
                = (C₂₂ : ℝ≥0∞) * ((Cimp : ℝ≥0∞) * ((((1 : ℝ≥0) + C₂₃) : ℝ≥0) : ℝ≥0∞))
                  * (improvWeight c ρ L N : ℝ≥0∞) * eLpNorm u 2 Measure.count
                  * eLpNorm v 2 Measure.count from by ring]
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)) (by positivity)
            rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
            refine ENNReal.coe_le_coe.mpr ?_
            show C₂₂ * (Cimp * ((1 : ℝ≥0) + C₂₃)) ≤ C₂₂ * ((Cimp + 1) * (1 + C₂₃))
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by simp) (by positivity)) (by positivity)

end

end Work.KMTAreas.A5
