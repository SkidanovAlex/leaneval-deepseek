/-
# `Work.KMTAreas.A7MixedG.FiberGuard` — the fibre (`form-1`/sampling) input of the mixed range

Target: `Work.KMTAreas.A7.FiberGuard P p₂ hdeg hp₂ htp₂` (defined in
`Submission/Work/KMTAreas/A7/MixedGSideAux.lean`): the residue `ℓ^{p₂}`-average over the fibres
`fiberOpP ρ P l₂ (GmixedKer …) n₀` of the guarded `g`-side family `GmixedFam` is bounded by the
variational norm of the family itself, with the loss `lossWeight A ρ 0 l₂ k₁ k₂`.

## The reduction performed here

* **Case 1, small scales** (`max l₂ (max k₁ k₂) ≤ B`).  The *crude Young bound* for the fibre,
  `Work.KMTAreas.A7.eLpNorm_residueLp_fiberOpP_le` (`A7/fiberVarSamplingCoreG.lean`, proved),
  bounds the residue average directly by
  `#(iwArithFreqsNew ρ l₂) · (∑' j, ‖cw (mStargF P.natDegree u) j‖) · ‖V^r(GmixedFam)‖`.
  In the bounded box of scales both finite factors are bounded (`exists_cw_mStargF_tsum_le` is
  uniform in `u`), and the bound is absorbed by the constant `C Λ`, which is chosen *after* `ρ` and
  may therefore depend on the threshold `B`.
* **Case 2, large scales** (`B < max l₂ (max k₁ k₂)`).  The per-residue estimate is the deep input,
  isolated as `Work.KMTAreas.A7MixedG.FiberLargeResidue`
  (`Submission/Work/KMTAreas/A7MixedG/FiberLargeResidue.lean`, KMT §8 `form-1` + quantitative
  Shannon/decimation transfer); the residue average over `n₀` is then free by
  `eLpNorm_residueLp_le_of_single` (`A7/fiberVarSamplingCoreG.lean`, proved).
* The exponent `A = max 4 A_crux` and the threshold `ρ₀ = min 1 ρ_crux` come from the crux, and the
  constants are combined with `lossWeight_mono_A` (`A7/fiberVarSamplingReduce.lean`, proved) and
  `one_le_lossWeight'` (`MixedGSideAux.lean`, proved).
-/
import Mathlib
import Submission.Work.KMTAreas.A7MixedG.FiberLargeResidue

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7MixedG

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- `p.toReal ≥ 1` for `p > 1`. -/
theorem toReal_ge_one {p : ENNReal} (hp : 1 < p) (hpt : p < ⊤) : (1 : ℝ) ≤ p.toReal := by
  have h := ENNReal.toReal_mono hpt.ne (le_of_lt hp)
  rwa [ENNReal.toReal_one] at h

/-- `p.toReal > 0` for `p > 1`. -/
theorem toReal_pos' {p : ENNReal} (hp : 1 < p) (hpt : p < ⊤) : (0 : ℝ) < p.toReal :=
  lt_of_lt_of_le zero_lt_one (toReal_ge_one hp hpt)

/-- The scale-localised cardinality bound of the small-scale case. -/
noncomputable def cardBound (ρ : ℝ) (B : ℕ) : ℕ :=
  (Finset.range (B + 1)).sup fun l => (iwArithFreqsNew ρ l).card

theorem card_le_cardBound {ρ : ℝ} {B l : ℕ} (hl : l ≤ B) :
    (iwArithFreqsNew ρ l).card ≤ cardBound ρ B :=
  Finset.le_sup (f := fun l => (iwArithFreqsNew ρ l).card)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

/-- The mass bound for the slope of the crude Young estimate: the `ℓ¹`-mass of the coefficients of
`mStargF d u` is uniform in `u`. -/
theorem exists_mass_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ MM : ℝ, 0 < MM ∧ ∀ u : ℕ, (∑' j : ℤ, ‖Work.KMTAreas.A7.cw
      (Work.KMTAreas.A7.mStargF d u) j‖) ≤ MM :=
  Work.A7.exists_cw_mStargF_tsum_le d hd

/-- Summability of the coefficient norms of `mStargF d u`. -/
theorem summable_cw_mStargF' (d : ℕ) (u : ℕ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖) := by
  obtain ⟨Cd, hdec⟩ := Work.KMTAreas.A7.cw_mStargF_decay d u
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left Cd)
  rw [Work.KMTAreas.A7.norm_kmtKernWeight, mul_one_div]
  exact hdec j

/-- `∑' j, ‖cw m j‖ₑ = ofReal (∑' j, ‖cw m j‖)`. -/
theorem tsum_enorm_cw_eq (d : ℕ) (u : ℕ) :
    (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖ₑ)
      = ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖) := by
  rw [tsum_congr (fun j => (ofReal_norm _).symm)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _)
    (summable_cw_mStargF' d u)).symm

theorem fiberGuard_of_largeResidue (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hlarge : FiberLargeResidue P p₂ hdeg hp₂ htp₂) :
    Work.KMTAreas.A7.FiberGuard P p₂ hdeg hp₂ htp₂ := by
  intro C₀ r hC₀ hr
  -- ### the deep large-scale input
  obtain ⟨Ac, hAc, ρc, hρc, B, hcrux⟩ := hlarge C₀ r hC₀ hr
  have hd : 1 ≤ P.natDegree := by omega
  obtain ⟨MM, hMMpos, hMM⟩ := exists_mass_bound P.natDegree hd
  -- ### the exponent and the threshold
  refine ⟨max 4 Ac, le_trans (by norm_num) (le_max_left _ _), min 1 ρc, lt_min one_pos hρc, ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_right _ _)
  obtain ⟨Cc, hCc⟩ := hcrux ρ hρ hρc'
  -- ### the constant (chosen after `ρ`)
  obtain ⟨Mnn, hMnn⟩ : ∃ Mnn : NNReal, (Mnn : ℝ) = MM := ⟨⟨MM, hMMpos.le⟩, rfl⟩
  obtain ⟨Knn, hKnn⟩ : ∃ Knn : NNReal,
      (Knn : ℝ) = (cardBound ρ B : ℝ) * MM + 1 :=
    ⟨⟨(cardBound ρ B : ℝ) * MM + 1, by positivity⟩, rfl⟩
  have hKnngt : (0 : ℝ) < (Knn : ℝ) := by rw [hKnn]; positivity
  refine ⟨fun Λ => max 1 (max Knn (Cc Λ)), ?_⟩
  intro a Λ l₂ k₁ k₂ t g hΛ hLac ha hl₂ ht hgb
  have hp2to : ENNReal.ofReal p₂.toReal = p₂ := ENNReal.ofReal_toReal (ne_of_lt htp₂)
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  have hp2r : (0 : ℝ) < p₂.toReal := toReal_pos' hp₂ htp₂
  have hp2r1 : (1 : ℝ) ≤ p₂.toReal := toReal_ge_one hp₂ htp₂
  have hlw : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂)
      ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 4 Ac) ρ 0 l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7.lossWeight_mono_A hAc (le_max_right _ _) ρ hρ.le 0 l₂ k₁ k₂)
  have hlw1 : (1 : ENNReal) ≤
      ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 4 Ac) ρ 0 l₂ k₁ k₂) :=
    ENNReal.one_le_ofReal.mpr
      (Work.KMTAreas.A7.one_le_lossWeight' (by norm_num) hρ.le 0 l₂ k₁ k₂)
  have hKnnenn : (Knn : ENNReal) = ENNReal.ofReal ((cardBound ρ B : ℝ) * MM + 1) := by
    rw [← hKnn]
    exact (ENNReal.ofReal_coe_nnreal).symm
  by_cases hsmall : max l₂ (max k₁ k₂) ≤ B
  · -- #### Case 1: the crude Young bound
    have hkey := Work.KMTAreas.A7.eLpNorm_residueLp_fiberOpP_le ρ P l₂ P.natDegree
      (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) (Work.KMTAreas.A7.arithQ ρ l₂)
      (Work.KMTAreas.A7.arithQ_pos ρ l₂) p₂.toReal hp2r1
      (Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g) r hr1
    rw [hp2to] at hkey
    have hkey' : MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedRes p₂ r ρ P C₀ a l₂ k₁ k₂ t g)
          p₂ MeasureTheory.Measure.count
        ≤ (((iwArithFreqsNew ρ l₂).card : ℝ≥0∞))
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖ₑ)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                MeasureTheory.Measure.count := by
      unfold Work.KMTAreas.A7.GmixedRes Work.KMTAreas.A7.GmixedFib Work.KMTAreas.A7.GmixedKer
        Work.KMTAreas.A7.GmixedVar
      exact hkey
    have hcard : (((iwArithFreqsNew ρ l₂).card : ℝ≥0∞)) ≤ (↑(cardBound ρ B) : ℝ≥0∞) := by
      exact_mod_cast card_le_cardBound (le_trans (le_max_left _ _) hsmall)
    have hmass : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖ₑ)
        ≤ ENNReal.ofReal MM := by
      rw [tsum_enorm_cw_eq P.natDegree]
      exact ENNReal.ofReal_le_ofReal (hMM _)
    have hconst : (((iwArithFreqsNew ρ l₂).card : ℝ≥0∞))
        * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖ₑ)
        ≤ (Knn : ENNReal) := by
      refine (mul_le_mul' hcard hmass).trans ?_
      rw [hKnnenn, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith [hMMpos]
    have hcoef : (Knn : ENNReal) ≤ ((max 1 (max Knn (Cc Λ)) : NNReal) : ENNReal)
        * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 4 Ac) ρ 0 l₂ k₁ k₂) := by
      calc (Knn : ENNReal)
          = (Knn : ENNReal) * 1 := (mul_one _).symm
        _ ≤ ((max 1 (max Knn (Cc Λ)) : NNReal) : ENNReal)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 4 Ac) ρ 0 l₂ k₁ k₂) :=
            mul_le_mul'
              (ENNReal.coe_le_coe.mpr
                (le_trans (le_max_left Knn (Cc Λ)) (le_max_right 1 (max Knn (Cc Λ))))) hlw1
    calc MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedRes p₂ r ρ P C₀ a l₂ k₁ k₂ t g)
          p₂ MeasureTheory.Measure.count
        ≤ (((iwArithFreqsNew ρ l₂).card : ℝ≥0∞))
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖ₑ)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                MeasureTheory.Measure.count := hkey'
      _ ≤ (Knn : ENNReal) * MeasureTheory.eLpNorm
            (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
            MeasureTheory.Measure.count := mul_le_mul' hconst le_rfl
      _ ≤ ((max 1 (max Knn (Cc Λ)) : NNReal) : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 4 Ac) ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                MeasureTheory.Measure.count := mul_le_mul' hcoef le_rfl
  · -- #### Case 2: the deep per-residue estimate, averaged over the residues
    have hper : ∀ n₀ : ℕ, MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
              (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) (n₀ : ℤ)
              (Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
          (ENNReal.ofReal p₂.toReal) MeasureTheory.Measure.count
        ≤ ((max 1 (Cc Λ) : NNReal) : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g)
                (ENNReal.ofReal p₂.toReal) MeasureTheory.Measure.count := by
      intro n₀
      have hc := hCc a Λ l₂ k₁ k₂ t g (n₀ : ℤ) hΛ hLac ha hl₂ ht hgb (Nat.lt_of_not_le hsmall)
      rw [← hp2to] at hc
      exact hc
    have hres := Work.KMTAreas.A7.eLpNorm_residueLp_le_of_single hp2r
      (Work.KMTAreas.A7.arithQ_pos ρ l₂) hper
    have hres' : MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedRes p₂ r ρ P C₀ a l₂ k₁ k₂ t g)
          p₂ MeasureTheory.Measure.count
        ≤ ((max 1 (Cc Λ) : NNReal) : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                MeasureTheory.Measure.count := by
      unfold Work.KMTAreas.A7.GmixedRes Work.KMTAreas.A7.GmixedFib Work.KMTAreas.A7.GmixedKer
        Work.KMTAreas.A7.GmixedVar
      rw [hp2to] at hres
      exact hres
    have hcoeff : ((max 1 (Cc Λ) : NNReal) : ENNReal)
        ≤ ((max 1 (max Knn (Cc Λ)) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (max_le (le_max_left 1 (max Knn (Cc Λ)))
        (le_trans (le_max_right Knn (Cc Λ)) (le_max_right 1 (max Knn (Cc Λ)))))
    refine hres'.trans ?_
    calc ((max 1 (Cc Λ) : NNReal) : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂)
          * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
              MeasureTheory.Measure.count
        = ((max 1 (Cc Λ) : NNReal) : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                MeasureTheory.Measure.count := rfl
      _ ≤ ((max 1 (max Knn (Cc Λ)) : NNReal) : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 4 Ac) ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                MeasureTheory.Measure.count := by
          exact mul_le_mul' (mul_le_mul' hcoeff hlw) le_rfl

/-- **The fibre (`form-1`/sampling) input of the mixed range.**

Complete reduction: the small-scale (Young) case and the residue average are proved in
`fiberGuard_of_largeResidue` above, which takes the large-scale per-residue estimate
(`Work.KMTAreas.A7MixedG.FiberLargeResidue`, KMT §8 `form-1` + quantitative Shannon/decimation
transfer) as its only input. -/
theorem FiberGuard (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Work.KMTAreas.A7.FiberGuard P p₂ hdeg hp₂ htp₂ :=
  fiberGuard_of_largeResidue P p₂ hdeg hp₂ htp₂ (fiberLargeResidue P p₂ hdeg hp₂ htp₂)

end Work.KMTAreas.A7MixedG
