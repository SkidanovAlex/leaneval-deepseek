import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.integrable_qLHSden_regime
import Submission.Work.BoseFixB1S.sectorPassageB1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.sbWordSliceRegime` — the REPAIRED word-level grouping step

The statement `Work.BoseFixB1S.sbWord_slice_superadd` (the word-level grouping of
`sbWord = sbKin + sbPot`) is **mis-stated**: its potential half needs the density
integrability of `Φ²·qLHSden{,1,2}`, which `Adm v ε₀ μ` with a *free* `ε₀` does not supply
(see `FINDING_sbWord_slice_superadd.md`, `FINDING_sbPot_slice_superadd.md`,
`FINDING_qLHSden_adm_integrable_missing_regime.md`, and the corpus's own
`FINDING_sbWordSectorAdditive_needs_integrable.md`).

This file provides the **repaired** statement, with the two localisation-regime inequalities
carried explicitly (the regime that every consumer in this area has, since the a-priori chain's
`ε₀`'s are chosen small before `μ` is instantiated):

    (regime)   R ≤ sideAt μ (a v) · d / 16 ,     R ≤ sideAt μ (a v) · chiR0 .

Under the regime the whole statement is provable, and the file proves it:

* the potential half `sbPot_slice_superadd_regime` (the honest cross-block-pair positivity
  `qLHSden = qLHSden1 + qLHSden2 + qLHSdenCross`, `qLHSdenCross ≥ 0`), with the density
  integrability supplied by `Work.BoseFixB1B.integrable_qLHSden_regime`;
* the slice integrability `sbPot_slice_integrable_regime` needed to *add* the two halves;
* the capstone `sbWord_slice_superadd_regime`, whose only non-local input is the kinetic
  half `Work.KinPSuperadd.SlotSplit` of the sliding kinetic word — the *true* structural fact
  (a sum of one-slot forms over the slots), delegated as
  `Work.BoseFixB1S.sbKin_slice_slotSplit` and taken here as the explicit hypothesis `hKin`
  (replace it by the import once that lemma is proved).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Weighted density integrability from the unweighted regime integrability -/

/-- If the (unweighted) diagonal density is integrable over the centred box and `Φ` is
continuous, then the weighted density `Φ²·qLHSden` is integrable: `Φ²` is bounded on the
compact box. -/
theorem weighted_qLHSden_integrable_regime {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d μ R : ℝ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hv1 : MeasureTheory.MemLp v 1) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hdR : R ≤ ℓ * d / 16) (hdRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {N : ℕ} {Φ : X N → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun x : X N =>
        (Φ x) ^ 2 * Submission.BoseGases.qLHSden N ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
      (Submission.BoseGases.abox N ℓ) volume := by
  have hD := Work.BoseFixB1B.integrable_qLHSden_regime (v := v) (h := h) (M := M) (ℓ := ℓ)
    (d := d) (μ := μ) (R0 := R) hM hℓ hd hv1 hR hv_supp hdR hdRχ u (k := N)
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦ.continuousOn
  have hBnn : 0 ≤ B := by
    have h0 : (0 : X N) ∈ Submission.BoseGases.abox N ℓ := by
      intro i m
      show ((0 : X N) i : E3) m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
      have hz : ((0 : X N) i : E3) m = 0 := rfl
      rw [hz]
      exact ⟨by linarith, by linarith⟩
    exact le_trans (norm_nonneg _) (hB 0 h0)
  refine Integrable.mono'
    (g := fun x : X N => B ^ 2 * ‖Submission.BoseGases.qLHSden N ℓ μ
      (Submission.BoseGases.wSmallPair M ℓ d u v)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u) x‖) ?_ ?_ ?_
  · exact hD.norm.const_mul (B ^ 2)
  · exact ((hΦ.pow 2).aestronglyMeasurable).mul hD.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
      with x hx
    have hΦle : ‖Φ x‖ ≤ B := hB x hx
    have hsq : (Φ x) ^ 2 ≤ B ^ 2 := by
      have habs : |Φ x| ≤ |B| := by simpa [Real.norm_eq_abs, abs_of_nonneg hBnn] using hΦle
      simpa [sq_abs] using sq_le_sq.mpr habs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
    calc (Φ x) ^ 2 * |Submission.BoseGases.qLHSden N ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x|
        ≤ B ^ 2 * |Submission.BoseGases.qLHSden N ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x| :=
          mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
      _ = B ^ 2 * ‖Submission.BoseGases.qLHSden N ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x‖ := by rw [Real.norm_eq_abs]

/-- The block-1 weighted density is integrable over the merged box under the regime: by
`qLHSden1_merge` it is the pulled-back *slice* density of a block-1 configuration, the push-forward
of the product through the measure-preserving block split. -/
theorem weighted_qLHSden1_integrable_regime {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d μ R : ℝ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hv1 : MeasureTheory.MemLp v 1) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hdR : R ≤ ℓ * d / 16) (hdRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {N₁ N₂ : ℕ} {Φ : X (N₁ + N₂) → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun x : X (N₁ + N₂) =>
        (Φ x) ^ 2 * Submission.BoseGases.qLHSden1 (N1 := N₁) (N2 := N₂) ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
      (Submission.BoseGases.abox (N₁ + N₂) ℓ) volume := by
  haveI : IsFiniteMeasure ((volume : Measure (X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact Submission.BoseGases.abox_lt_top N₂ ℓ hℓ.le⟩
  have hslice := Work.BoseFixB1B.integrable_qLHSden_regime (v := v) (h := h) (M := M) (ℓ := ℓ)
    (d := d) (μ := μ) (R0 := R) hM hℓ hd hv1 hR hv_supp hdR hdRχ u (k := N₁)
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (N₁ + N₂) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (N₁ + N₂) ℓ) (f := Φ) hΦ.continuousOn
  have hBnn : 0 ≤ B := by
    have h0 : (0 : X (N₁ + N₂)) ∈ Submission.BoseGases.abox (N₁ + N₂) ℓ := by
      intro i m
      show ((0 : X (N₁ + N₂)) i : E3) m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
      have hz : ((0 : X (N₁ + N₂)) i : E3) m = 0 := rfl
      rw [hz]
      exact ⟨by linarith, by linarith⟩
    exact le_trans (norm_nonneg _) (hB 0 h0)
  have hae : ∀ᵐ q ∂((volume : Measure (X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)).prod
      ((volume : Measure (X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ)),
      q ∈ (Submission.BoseGases.abox N₁ ℓ) ×ˢ (Submission.BoseGases.abox N₂ ℓ) := by
    rw [Measure.prod_restrict]
    exact MeasureTheory.ae_restrict_mem
      ((Submission.BoseGases.abox_measurable N₁ ℓ).prod (Submission.BoseGases.abox_measurable N₂ ℓ))
  have hprod : Integrable (fun q : X N₁ × X N₂ =>
      (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
        Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1)
      (((volume : Measure (X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)).prod
        ((volume : Measure (X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ))) := by
    refine Integrable.mono'
      (g := fun q : X N₁ × X N₂ => B ^ 2 * ‖Submission.BoseGases.qLHSden N₁ ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1‖) ?_ ?_ ?_
    · exact (hslice.norm.const_mul (B ^ 2)).comp_fst _
    · exact (((hΦ.comp (Work.KinPSuperadd.continuous_mergeBlock N₁ N₂)).pow 2).aestronglyMeasurable).mul
        hslice.aestronglyMeasurable.comp_fst
    · filter_upwards [hae] with q hq
      have hq' : q.1 ∈ Submission.BoseGases.abox N₁ ℓ ∧ q.2 ∈ Submission.BoseGases.abox N₂ ℓ :=
        Set.mem_prod.mp hq
      have hq'' : Submission.BoseGases.firstBlock N₁ N₂ (Submission.BoseGases.mergeBlock N₁ N₂ q)
            ∈ Submission.BoseGases.abox N₁ ℓ ∧
          Submission.BoseGases.lastBlock N₁ N₂ (Submission.BoseGases.mergeBlock N₁ N₂ q)
            ∈ Submission.BoseGases.abox N₂ ℓ := by
        rw [Submission.BoseGases.mergeBlock_first, Submission.BoseGases.mergeBlock_last]
        exact hq'
      have hmq : Submission.BoseGases.mergeBlock N₁ N₂ q ∈ Submission.BoseGases.abox (N₁ + N₂) ℓ :=
        (Submission.BoseGases.mem_abox_split N₁ N₂ ℓ _).mpr hq''
      have hΦle : ‖Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)‖ ≤ B := hB _ hmq
      have hsq : (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 ≤ B ^ 2 := by
        have habs : |Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)| ≤ |B| := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hBnn] using hΦle
        simpa [sq_abs] using sq_le_sq.mpr habs
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)))]
      calc (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
            |Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1|
          ≤ B ^ 2 * |Submission.BoseGases.qLHSden N₁ ℓ μ
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1| :=
            mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
        _ = B ^ 2 * ‖Submission.BoseGases.qLHSden N₁ ℓ μ
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1‖ := by rw [Real.norm_eq_abs]
  have hcomp := (Submission.BoseGases.aboxSplit_measurePreserving_restrict N₁ N₂ ℓ).integrable_comp_emb
    (Submission.BoseGases.blockSplitEquiv N₁ N₂).measurableEmbedding
    (g := fun q : X N₁ × X N₂ =>
      (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
        Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1)
  refine hcomp.mpr hprod |>.congr (Filter.Eventually.of_forall fun x => ?_)
  have hbs : Submission.BoseGases.blockSplitEquiv N₁ N₂ x
      = (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) :=
    Submission.BoseGases.blockSplitEquiv_apply N₁ N₂ x
  have hm : Submission.BoseGases.mergeBlock N₁ N₂
      (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) = x :=
    Submission.BoseGases.mergeBlock_eq N₁ N₂ x
  have hd1 : Submission.BoseGases.qLHSden1 (N1 := N₁) (N2 := N₂) ℓ μ
      (Submission.BoseGases.wSmallPair M ℓ d u v) (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
      = Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) (Submission.BoseGases.firstBlock N₁ N₂ x) := by
    conv_lhs => rw [← hm]
    exact Submission.BoseGases.qLHSden1_merge ℓ μ _ _ _ _
  simp only [Function.comp_apply, hbs, hm, hd1]

/-- Block-2 mirror of `weighted_qLHSden1_integrable_regime`. -/
theorem weighted_qLHSden2_integrable_regime {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d μ R : ℝ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hv1 : MeasureTheory.MemLp v 1) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hdR : R ≤ ℓ * d / 16) (hdRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {N₁ N₂ : ℕ} {Φ : X (N₁ + N₂) → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun x : X (N₁ + N₂) =>
        (Φ x) ^ 2 * Submission.BoseGases.qLHSden2 (N1 := N₁) (N2 := N₂) ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
      (Submission.BoseGases.abox (N₁ + N₂) ℓ) volume := by
  haveI : IsFiniteMeasure ((volume : Measure (X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact Submission.BoseGases.abox_lt_top N₁ ℓ hℓ.le⟩
  have hslice := Work.BoseFixB1B.integrable_qLHSden_regime (v := v) (h := h) (M := M) (ℓ := ℓ)
    (d := d) (μ := μ) (R0 := R) hM hℓ hd hv1 hR hv_supp hdR hdRχ u (k := N₂)
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (N₁ + N₂) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (N₁ + N₂) ℓ) (f := Φ) hΦ.continuousOn
  have hBnn : 0 ≤ B := by
    have h0 : (0 : X (N₁ + N₂)) ∈ Submission.BoseGases.abox (N₁ + N₂) ℓ := by
      intro i m
      show ((0 : X (N₁ + N₂)) i : E3) m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
      have hz : ((0 : X (N₁ + N₂)) i : E3) m = 0 := rfl
      rw [hz]
      exact ⟨by linarith, by linarith⟩
    exact le_trans (norm_nonneg _) (hB 0 h0)
  have hae : ∀ᵐ q ∂((volume : Measure (X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)).prod
      ((volume : Measure (X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ)),
      q ∈ (Submission.BoseGases.abox N₁ ℓ) ×ˢ (Submission.BoseGases.abox N₂ ℓ) := by
    rw [Measure.prod_restrict]
    exact MeasureTheory.ae_restrict_mem
      ((Submission.BoseGases.abox_measurable N₁ ℓ).prod (Submission.BoseGases.abox_measurable N₂ ℓ))
  have hprod : Integrable (fun q : X N₁ × X N₂ =>
      (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
        Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2)
      (((volume : Measure (X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)).prod
        ((volume : Measure (X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ))) := by
    refine Integrable.mono'
      (g := fun q : X N₁ × X N₂ => B ^ 2 * ‖Submission.BoseGases.qLHSden N₂ ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2‖) ?_ ?_ ?_
    · exact (hslice.norm.const_mul (B ^ 2)).comp_snd _
    · exact (((hΦ.comp (Work.KinPSuperadd.continuous_mergeBlock N₁ N₂)).pow 2).aestronglyMeasurable).mul
        hslice.aestronglyMeasurable.comp_snd
    · filter_upwards [hae] with q hq
      have hq' : q.1 ∈ Submission.BoseGases.abox N₁ ℓ ∧ q.2 ∈ Submission.BoseGases.abox N₂ ℓ :=
        Set.mem_prod.mp hq
      have hq'' : Submission.BoseGases.firstBlock N₁ N₂ (Submission.BoseGases.mergeBlock N₁ N₂ q)
            ∈ Submission.BoseGases.abox N₁ ℓ ∧
          Submission.BoseGases.lastBlock N₁ N₂ (Submission.BoseGases.mergeBlock N₁ N₂ q)
            ∈ Submission.BoseGases.abox N₂ ℓ := by
        rw [Submission.BoseGases.mergeBlock_first, Submission.BoseGases.mergeBlock_last]
        exact hq'
      have hmq : Submission.BoseGases.mergeBlock N₁ N₂ q ∈ Submission.BoseGases.abox (N₁ + N₂) ℓ :=
        (Submission.BoseGases.mem_abox_split N₁ N₂ ℓ _).mpr hq''
      have hΦle : ‖Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)‖ ≤ B := hB _ hmq
      have hsq : (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 ≤ B ^ 2 := by
        have habs : |Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)| ≤ |B| := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hBnn] using hΦle
        simpa [sq_abs] using sq_le_sq.mpr habs
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)))]
      calc (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
            |Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2|
          ≤ B ^ 2 * |Submission.BoseGases.qLHSden N₂ ℓ μ
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2| :=
            mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
        _ = B ^ 2 * ‖Submission.BoseGases.qLHSden N₂ ℓ μ
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2‖ := by rw [Real.norm_eq_abs]
  have hcomp := (Submission.BoseGases.aboxSplit_measurePreserving_restrict N₁ N₂ ℓ).integrable_comp_emb
    (Submission.BoseGases.blockSplitEquiv N₁ N₂).measurableEmbedding
    (g := fun q : X N₁ × X N₂ =>
      (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
        Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2)
  refine hcomp.mpr hprod |>.congr (Filter.Eventually.of_forall fun x => ?_)
  have hbs : Submission.BoseGases.blockSplitEquiv N₁ N₂ x
      = (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) :=
    Submission.BoseGases.blockSplitEquiv_apply N₁ N₂ x
  have hm : Submission.BoseGases.mergeBlock N₁ N₂
      (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) = x :=
    Submission.BoseGases.mergeBlock_eq N₁ N₂ x
  have hd2 : Submission.BoseGases.qLHSden2 (N1 := N₁) (N2 := N₂) ℓ μ
      (Submission.BoseGases.wSmallPair M ℓ d u v) (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
      = Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) (Submission.BoseGases.lastBlock N₁ N₂ x) := by
    conv_lhs => rw [← hm]
    exact Submission.BoseGases.qLHSden2_merge ℓ μ _ _ _ _
  simp only [Function.comp_apply, hbs, hm, hd2]

/-- **The potential half of the grouping step, under the localisation regime.** -/
theorem sbPot_slice_superadd_regime {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : E3) {N₁ N₂ : ℕ}
    {Φ : Submission.BoseGases.X (N₁ + N₂) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseFixB1.sbPot h μ u Φ
      ≥ (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbPot h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbPot h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < d := by rw [hddef]; exact Work.BoseFixB1.adm_d_pos hAdm
  have hMone : 1 ≤ M := by
    rw [hMdef, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hD1 := weighted_qLHSden1_integrable_regime (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d)
    (μ := μ) (R := R) hMone hℓpos hdpos hv1 hR hv_supp hR16 hRχ u hΦ.continuous
  have hD2 := weighted_qLHSden2_integrable_regime (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d)
    (μ := μ) (R := R) hMone hℓpos hdpos hv1 hR hv_supp hR16 hRχ u hΦ.continuous
  have hD := weighted_qLHSden_integrable_regime (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d)
    (μ := μ) (R := R) hMone hℓpos hdpos hv1 hR hv_supp hR16 hRχ u hΦ.continuous
  have hw : ∀ x y : E3, 0 ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y :=
    fun x y => wSmallPair_nonneg_B1S u x y (hv (x - y))
  have hle := pot_blocks_le_full (N1 := N₁) (N2 := N₂) (s := ℓ) (μ := μ)
    (w := Submission.BoseGases.wSmallPair M ℓ d u v)
    (w1 := Submission.BoseGases.wSmall1Pair h M ℓ d u) hw hD1 hD2 hD
  have h1 := qLHSden1_expect_eq_slice (N1 := N₁) (N2 := N₂) (s := ℓ) (μ := μ)
    (w := Submission.BoseGases.wSmallPair M ℓ d u v)
    (w1 := Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ hD1
  have h2 := qLHSden2_expect_eq_slice (N1 := N₁) (N2 := N₂) (s := ℓ) (μ := μ)
    (w := Submission.BoseGases.wSmallPair M ℓ d u v)
    (w1 := Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ hD2
  have hB1' : (∫ w in Submission.BoseGases.abox N₂ ℓ, Work.BoseFixB1.sbPot h μ u
        (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = ∫ wv in Submission.BoseGases.abox N₂ ℓ,
          Submission.BoseGases.qLHSword (N := N₁) ℓ μ
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            (Submission.BoseGases.sbs_slice Φ wv) := by
    apply integral_congr_ae
    filter_upwards with wv
    rw [Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
    rw [← hℓdef, ← hddef, ← hMdef]
    rfl
  have hB2' : (∫ y in Submission.BoseGases.abox N₁ ℓ, Work.BoseFixB1.sbPot h μ u
        (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = ∫ yv in Submission.BoseGases.abox N₁ ℓ,
          Submission.BoseGases.qLHSword (N := N₂) ℓ μ
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            (Submission.BoseGases.sbs_slice2 Φ yv) := by
    apply integral_congr_ae
    filter_upwards with yv
    rw [Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
    rw [← hℓdef, ← hddef, ← hMdef]
    rfl
  have hB1 : (∫ w in Submission.BoseGases.abox N₂ ℓ, Work.BoseFixB1.sbPot h μ u
        (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = ∫ x in Submission.BoseGases.abox (N₁ + N₂) ℓ, (Φ x) ^ 2 *
          Submission.BoseGases.qLHSden1 (N1 := N₁) (N2 := N₂) ℓ μ
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) x :=
    hB1'.trans h1.symm
  have hB2 : (∫ y in Submission.BoseGases.abox N₁ ℓ, Work.BoseFixB1.sbPot h μ u
        (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = ∫ x in Submission.BoseGases.abox (N₁ + N₂) ℓ, (Φ x) ^ 2 *
          Submission.BoseGases.qLHSden2 (N1 := N₁) (N2 := N₂) ℓ μ
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) x :=
    hB2'.trans h2.symm
  have hL : Work.BoseFixB1.sbPot h μ u Φ
      = ∫ x in Submission.BoseGases.abox (N₁ + N₂) ℓ, (Φ x) ^ 2 *
          Submission.BoseGases.qLHSden (N₁ + N₂) ℓ μ
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) x := rfl
  rw [hB1, hB2, hL]
  linarith

/-- **The potential slices are integrable in the frozen variable** (under the regime). -/
theorem sbPot_slice_integrable_regime {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : E3) {N₁ N₂ : ℕ}
    {Φ : Submission.BoseGases.X (N₁ + N₂) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.IntegrableOn (fun w : Submission.BoseGases.X N₂ =>
        Work.BoseFixB1.sbPot h μ u
          (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      (Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) volume
    ∧ MeasureTheory.IntegrableOn (fun y : Submission.BoseGases.X N₁ =>
        Work.BoseFixB1.sbPot h μ u
          (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      (Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) volume := by
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < d := by rw [hddef]; exact Work.BoseFixB1.adm_d_pos hAdm
  have hMone : 1 ≤ M := by
    rw [hMdef, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hD1 := weighted_qLHSden1_integrable_regime (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d)
    (μ := μ) (R := R) hMone hℓpos hdpos hv1 hR hv_supp hR16 hRχ u hΦ.continuous
  have hD2 := weighted_qLHSden2_integrable_regime (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d)
    (μ := μ) (R := R) hMone hℓpos hdpos hv1 hR hv_supp hR16 hRχ u hΦ.continuous
  have hsbPot : ∀ {n : ℕ} (Ψ : Submission.BoseGases.X n → ℝ), Work.BoseFixB1.sbPot h μ u Ψ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 * Submission.BoseGases.qLHSden n ℓ μ
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x := fun Ψ => rfl
  -- the two product integrabilities, pushed forward from `hD1`/`hD2`
  have hG1 : Integrable (fun q : Submission.BoseGases.X N₁ × Submission.BoseGases.X N₂ =>
      (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
        Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1)
      (((volume : Measure (Submission.BoseGases.X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ))) := by
    refine (Submission.BoseGases.aboxSplit_measurePreserving_restrict N₁ N₂ ℓ).integrable_comp_emb
      (Submission.BoseGases.blockSplitEquiv N₁ N₂).measurableEmbedding
      (g := fun q : Submission.BoseGases.X N₁ × Submission.BoseGases.X N₂ =>
        (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
          Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.1) |>.mp ?_
    refine hD1.congr (Filter.Eventually.of_forall fun x => ?_)
    have hbs : Submission.BoseGases.blockSplitEquiv N₁ N₂ x
        = (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) :=
      Submission.BoseGases.blockSplitEquiv_apply N₁ N₂ x
    have hm : Submission.BoseGases.mergeBlock N₁ N₂
        (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) = x :=
      Submission.BoseGases.mergeBlock_eq N₁ N₂ x
    have hd1 : Submission.BoseGases.qLHSden1 (N1 := N₁) (N2 := N₂) ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v) (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
        = Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) (Submission.BoseGases.firstBlock N₁ N₂ x) := by
      conv_lhs => rw [← hm]
      exact Submission.BoseGases.qLHSden1_merge ℓ μ _ _ _ _
    simp only [Function.comp_apply, hbs, hm, hd1]
  have hG2 : Integrable (fun q : Submission.BoseGases.X N₁ × Submission.BoseGases.X N₂ =>
      (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
        Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2)
      (((volume : Measure (Submission.BoseGases.X N₁)).restrict (Submission.BoseGases.abox N₁ ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X N₂)).restrict (Submission.BoseGases.abox N₂ ℓ))) := by
    refine (Submission.BoseGases.aboxSplit_measurePreserving_restrict N₁ N₂ ℓ).integrable_comp_emb
      (Submission.BoseGases.blockSplitEquiv N₁ N₂).measurableEmbedding
      (g := fun q : Submission.BoseGases.X N₁ × Submission.BoseGases.X N₂ =>
        (Φ (Submission.BoseGases.mergeBlock N₁ N₂ q)) ^ 2 *
          Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) q.2) |>.mp ?_
    refine hD2.congr (Filter.Eventually.of_forall fun x => ?_)
    have hbs : Submission.BoseGases.blockSplitEquiv N₁ N₂ x
        = (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) :=
      Submission.BoseGases.blockSplitEquiv_apply N₁ N₂ x
    have hm : Submission.BoseGases.mergeBlock N₁ N₂
        (Submission.BoseGases.firstBlock N₁ N₂ x, Submission.BoseGases.lastBlock N₁ N₂ x) = x :=
      Submission.BoseGases.mergeBlock_eq N₁ N₂ x
    have hd2 : Submission.BoseGases.qLHSden2 (N1 := N₁) (N2 := N₂) ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v) (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
        = Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) (Submission.BoseGases.lastBlock N₁ N₂ x) := by
      conv_lhs => rw [← hm]
      exact Submission.BoseGases.qLHSden2_merge ℓ μ _ _ _ _
    simp only [Function.comp_apply, hbs, hm, hd2]
  constructor
  · refine hG1.integral_prod_right.congr (Filter.Eventually.of_forall fun w => ?_)
    show (∫ x in Submission.BoseGases.abox N₁ ℓ,
          Φ (Submission.BoseGases.mergeBlock N₁ N₂ (x, w)) ^ 2 *
            Submission.BoseGases.qLHSden N₁ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
        = Work.BoseFixB1.sbPot h μ u
            (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))
    rw [hsbPot]
  · refine hG2.integral_prod_left.congr (Filter.Eventually.of_forall fun y => ?_)
    show (∫ x in Submission.BoseGases.abox N₂ ℓ,
          Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, x)) ^ 2 *
            Submission.BoseGases.qLHSden N₂ ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
        = Work.BoseFixB1.sbPot h μ u
            (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))
    rw [hsbPot]

/-- **The repaired word-level grouping step.** -/
theorem sbWord_slice_superadd_regime {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : E3)
    (hKin : Work.KinPSuperadd.SlotSplit (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (fun (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ) =>
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Ψ))
    {N₁ N₂ : ℕ}
    {Φ : Submission.BoseGases.X (N₁ + N₂) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseFixB1.sbWord h μ u Φ
      ≥ (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbWord h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbWord h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMdef
  have hpot := sbPot_slice_superadd_regime (v := v) h hv hv1 hvrad hR hv_supp hav hAdm
    hR16 hRχ u (N₁ := N₁) (N₂ := N₂) hΦ
  have hint := sbPot_slice_integrable_regime (v := v) h hv hv1 hvrad hR hv_supp hav hAdm
    hR16 hRχ u (N₁ := N₁) (N₂ := N₂) hΦ
  have hkin := hKin.split Φ hΦ
  have hsw : ∀ {n : ℕ} (Ψ : Submission.BoseGases.X n → ℝ),
      Work.BoseFixB1.sbWord h μ u Ψ
        = Work.BoseFixB1.sbKin (v := v) μ M u Ψ + Work.BoseFixB1.sbPot h μ u Ψ := fun Ψ => rfl
  have h1 : (∫ w in Submission.BoseGases.abox N₂ ℓ, Work.BoseFixB1.sbWord h μ u
        (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = (∫ w in Submission.BoseGases.abox N₂ ℓ, Work.BoseFixB1.sbKin (v := v) μ M u
            (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ w in Submission.BoseGases.abox N₂ ℓ, Work.BoseFixB1.sbPot h μ u
            (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
    rw [← integral_add (hKin.int₁ Φ hΦ) hint.1]
    apply integral_congr_ae
    filter_upwards with w
    exact hsw _
  have h2 : (∫ y in Submission.BoseGases.abox N₁ ℓ, Work.BoseFixB1.sbWord h μ u
        (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = (∫ y in Submission.BoseGases.abox N₁ ℓ, Work.BoseFixB1.sbKin (v := v) μ M u
            (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ ℓ, Work.BoseFixB1.sbPot h μ u
            (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
    rw [← integral_add (hKin.int₂ Φ hΦ) hint.2]
    apply integral_congr_ae
    filter_upwards with y
    exact hsw _
  rw [h1, h2, hsw Φ]
  linarith [hkin, hpot]

end Work.BoseFixB1S
