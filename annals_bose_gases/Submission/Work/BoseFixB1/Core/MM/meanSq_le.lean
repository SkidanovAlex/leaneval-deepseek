import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.Core.MM.threeDimL
import Submission.Work.BoseFixB1.Core.bulkEst
import Submission.Work.BoseFixB1.Core.clipLeft
import Submission.Work.BoseFixB1.Core.meanSq3dE3
import Submission.Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Core.MM

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {ℓ h : ℝ}

/-- Negation of a set integral: `∫⁻_{x ∈ -s} f x = ∫⁻_{x ∈ s} f (-x)`. -/
private lemma lintegral_neg_set {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in -s, f x = ∫⁻ x in s, f (-x) := by
  classical
  have hmp : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_neg volume
  have h1 : ∫⁻ x in -s, f x = ∫⁻ x : ℝ, (-s).indicator f x :=
    (lintegral_indicator hs.neg f).symm
  have h2 : ∫⁻ x : ℝ, (-s).indicator f x = ∫⁻ x : ℝ, (-s).indicator f (-x) :=
    (hmp.lintegral_comp_emb measurableEmbedding_neg _).symm
  have h3 : ∫⁻ x : ℝ, (-s).indicator f (-x)
      = ∫⁻ x : ℝ, s.indicator (fun y => f (-y)) x := by
    refine lintegral_congr fun x => ?_
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ s
    · rw [if_pos hx, if_pos (by rw [Set.mem_neg, neg_neg]; exact hx)]
    · rw [if_neg hx, if_neg (by rw [Set.mem_neg, neg_neg]; exact hx)]
  have h4 : ∫⁻ x : ℝ, s.indicator (fun y => f (-y)) x = ∫⁻ x in s, f (-x) :=
    lintegral_indicator hs _
  rw [h1, h2, h3, h4]

/-- `slI` is odd in its centre: `slI ℓ h (-u) = - slI ℓ h u`. -/
private lemma slI_neg (ℓ h u : ℝ) :
    Work.BoseFixB1S.slI ℓ h (-u) = - Work.BoseFixB1S.slI ℓ h u := by
  ext x
  rw [Set.mem_neg, Work.BoseFixB1S.slI_eq, Work.BoseFixB1S.slI_eq, Set.mem_inter_iff,
    Set.mem_inter_iff, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **The right-clip estimate** (from the left-clip estimate by the reflection
`u ↦ -u`, `x ↦ -x`). -/
private lemma clipRightL_of_clipLeft {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u in Set.Ioc ((ℓ - h) / (2 * h)) ((ℓ + h) / (2 * h)),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  set G : ℝ → ℝ≥0∞ := fun x => F (-x) with hGdef
  have hG : AEMeasurable G (volume : Measure ℝ) := by
    have h1 : AEMeasurable F (Measure.map (fun x : ℝ => -x) (volume : Measure ℝ)) := by
      rw [Measure.map_neg_eq_self]; exact hF
    have h2 : AEMeasurable (F ∘ fun x : ℝ => -x) (volume : Measure ℝ) :=
      h1.comp_measurable measurable_neg
    convert h2 using 1
    funext x
    rfl
  have hpt : ∀ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
        / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      = ((∫⁻ x in Work.BoseFixB1S.slI ℓ h (-u), G x)
        / (volume (Work.BoseFixB1S.slI ℓ h (-u)))) ^ 2 := by
    intro u
    have hnum : (∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
        = ∫⁻ x in Work.BoseFixB1S.slI ℓ h (-u), G x := by
      rw [slI_neg ℓ h u, lintegral_neg_set (Work.BoseFixB1S.measurableSet_slI ℓ h u) G]
      refine lintegral_congr fun x => ?_
      simp only [hGdef]
      rw [neg_neg]
    have hden : (volume (Work.BoseFixB1S.slI ℓ h u))
        = volume (Work.BoseFixB1S.slI ℓ h (-u)) := by
      rw [slI_neg ℓ h u]
      have hm : (fun x : ℝ => -x) ⁻¹' (Work.BoseFixB1S.slI ℓ h u)
          = -(Work.BoseFixB1S.slI ℓ h u) := by
        ext x; simp only [Set.mem_preimage, Set.mem_neg, neg_neg]
      rw [← hm, ← Measure.map_apply measurable_neg (Work.BoseFixB1S.measurableSet_slI ℓ h u),
        Measure.map_neg_eq_self]
    rw [hnum, hden]
  have hregion : (∫⁻ u in Set.Ioc ((ℓ - h) / (2 * h)) ((ℓ + h) / (2 * h)),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
      = (∫⁻ u in Set.Ioc (-((ℓ + h) / (2 * h))) (-((ℓ - h) / (2 * h))),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2) := by
    rw [lintegral_congr hpt]
    rw [(lintegral_neg_set (s := Set.Ioc ((ℓ - h) / (2 * h)) ((ℓ + h) / (2 * h)))
      measurableSet_Ioc (fun v => ((∫⁻ x in Work.BoseFixB1S.slI ℓ h v, G x)
        / (volume (Work.BoseFixB1S.slI ℓ h v))) ^ 2)).symm]
    rw [Set.neg_Ioc]
    exact setLIntegral_congr MeasureTheory.Ico_ae_eq_Ioc
  have hG2 : (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (G x) ^ 2)
      = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
    have hsym : -(Set.Icc (-ℓ / 2) (ℓ / 2)) = Set.Icc (-ℓ / 2) (ℓ / 2) := by
      rw [Set.neg_Icc]
      congr 1 <;> ring
    have h := lintegral_neg_set (s := Set.Icc (-ℓ / 2) (ℓ / 2)) measurableSet_Icc
      (fun y => (F y) ^ 2)
    rw [hsym] at h
    simp only [hGdef]
    exact h.symm
  calc (∫⁻ u in Set.Ioc ((ℓ - h) / (2 * h)) ((ℓ + h) / (2 * h)),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
      = ∫⁻ u in Set.Ioc (-((ℓ + h) / (2 * h))) (-((ℓ - h) / (2 * h))),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, G x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 :=
        hregion
    _ ≤ ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (G x) ^ 2 :=
        Work.BoseFixB1.Core.clipLeft (ℓ := ℓ) (h := h) hh hhℓ hG
    _ = ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by rw [hG2]

private lemma slI_subset_singleton_left (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : u ≤ -((ℓ + h) / (2 * h))) : Work.BoseFixB1S.slI ℓ h u ⊆ {-ℓ / 2} := by
  intro x hx
  rw [Work.BoseFixB1S.slI_eq] at hx
  simp only [Set.mem_inter_iff, Set.mem_Icc] at hx
  simp only [Set.mem_singleton_iff]
  have h1 : h * u + h / 2 ≤ -ℓ / 2 := by
    have h2 : h * u ≤ h * (-((ℓ + h) / (2 * h))) := mul_le_mul_of_nonneg_left hu hh.le
    have h3 : h * (-((ℓ + h) / (2 * h))) = -((ℓ + h) / 2) := by
      field_simp
    rw [h3] at h2
    linarith
  linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2, h1]

/-- If `u` is at or right of the window range then the sliding interval is contained in the single
point `ℓ/2`. -/
private lemma slI_subset_singleton_right (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : ((ℓ + h) / (2 * h)) < u) : Work.BoseFixB1S.slI ℓ h u ⊆ {ℓ / 2} := by
  intro x hx
  rw [Work.BoseFixB1S.slI_eq] at hx
  simp only [Set.mem_inter_iff, Set.mem_Icc] at hx
  simp only [Set.mem_singleton_iff]
  have h1 : ℓ / 2 < h * u - h / 2 := by
    have h2 : h * ((ℓ + h) / (2 * h)) < h * u := mul_lt_mul_of_pos_left hu hh
    have h3 : h * ((ℓ + h) / (2 * h)) = (ℓ + h) / 2 := by field_simp
    rw [h3] at h2
    linarith
  exact absurd hx.1.2 (not_le.mpr (lt_of_lt_of_le h1 hx.2.1))

/-- Outside the window range the sliding interval has measure zero. -/
private lemma volume_slI_eq_zero_of_notMem (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : u ∉ Set.Ioc (-((ℓ + h) / (2 * h))) ((ℓ + h) / (2 * h))) :
    volume (Work.BoseFixB1S.slI ℓ h u) = 0 := by
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with hu | hu
  · refine measure_mono_null (slI_subset_singleton_left (ℓ := ℓ) hh hhℓ hu) ?_
    rw [Real.volume_singleton]
  · refine measure_mono_null (slI_subset_singleton_right (ℓ := ℓ) hh hhℓ hu) ?_
    rw [Real.volume_singleton]

/-- Outside the window range the window integral vanishes. -/
private lemma setLIntegral_slI_eq_zero_of_notMem (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {u : ℝ} (hu : u ∉ Set.Ioc (-((ℓ + h) / (2 * h))) ((ℓ + h) / (2 * h))) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x = 0 :=
  setLIntegral_measure_zero _ _ (volume_slI_eq_zero_of_notMem (ℓ := ℓ) hh hhℓ hu)

/-- **The one-dimensional sliding-box mean-square bound** (assembled from the three
delegated pieces). -/
theorem oneDimMeanSqCore {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
        / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  set B : ℝ := (ℓ - h) / (2 * h) with hBdef
  set R : ℝ := (ℓ + h) / (2 * h) with hRdef
  set I : ℝ≥0∞ := ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 with hIdef
  set Φ : ℝ → ℝ≥0∞ := fun u => ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
      / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 with hΦdef
  have hR0 : 0 < R := by
    rw [hRdef]; exact div_pos (by linarith) (by positivity)
  have hB0 : 0 ≤ B := by
    rw [hBdef]; exact div_nonneg (by linarith) (by positivity)
  have hBR : B ≤ R := by
    rw [hBdef, hRdef, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * h)]
    linarith
  -- the integrand vanishes outside the window range
  have hzero : ∀ u ∉ Set.Ioc (-R) R, Φ u = 0 := by
    intro u hu
    have hvol : volume (Work.BoseFixB1S.slI ℓ h u) = 0 :=
      volume_slI_eq_zero_of_notMem (ℓ := ℓ) hh hhℓ (by simpa [hRdef] using hu)
    have hint : ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x = 0 := setLIntegral_measure_zero _ _ hvol
    rw [hΦdef]
    simp only [hint, hvol]
    rw [ENNReal.div_eq_inv_mul, ENNReal.inv_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  -- rewrite the integral over the window range
  have h1 : ∫⁻ u : ℝ, Φ u = ∫⁻ u in Set.Ioc (-R) R, Φ u := by
    rw [show (∫⁻ u in Set.Ioc (-R) R, Φ u) = ∫⁻ u, (Set.Ioc (-R) R).indicator Φ u from
      (lintegral_indicator measurableSet_Ioc Φ).symm]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Set.Ioc (-R) R
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hzero u hu]
  -- split the window range into the three regions
  have hsplit1 : Set.Ioc (-R) (-B) ∪ Set.Ioc (-B) B = Set.Ioc (-R) B :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hsplit2 : Set.Ioc (-R) B ∪ Set.Ioc B R = Set.Ioc (-R) R :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) hBR
  have hsplit : Set.Ioc (-R) R
      = (Set.Ioc (-R) (-B) ∪ Set.Ioc (-B) B) ∪ Set.Ioc B R := by
    rw [hsplit1, hsplit2]
  have hd1 : Disjoint (Set.Ioc (-R) (-B)) (Set.Ioc (-B) B) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact absurd hx1.2 (not_le.mpr hx2.1)
  have hd2 : Disjoint (Set.Ioc (-R) (-B) ∪ Set.Ioc (-B) B) (Set.Ioc B R) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hx1 with hx1 | hx1
    · exact absurd hx1.2 (not_le.mpr (lt_of_le_of_lt (by linarith) hx2.1))
    · exact absurd hx1.2 (not_le.mpr hx2.1)
  have h2 : ∫⁻ u in Set.Ioc (-R) R, Φ u
      = (∫⁻ u in Set.Ioc (-R) (-B), Φ u) + (∫⁻ u in Set.Ioc (-B) B, Φ u)
        + (∫⁻ u in Set.Ioc B R, Φ u) := by
    rw [hsplit, lintegral_union measurableSet_Ioc hd2,
      lintegral_union measurableSet_Ioc hd1]
  -- the three estimates
  have hL := Work.BoseFixB1.Core.clipLeft (ℓ := ℓ) (h := h) hh hhℓ hF
  have hB' := Work.BoseFixB1.Core.bulkEst (ℓ := ℓ) (h := h) hh hhℓ hF
  have hR' := clipRightL_of_clipLeft (ℓ := ℓ) (h := h) hh hhℓ hF
  have hL' : ∫⁻ u in Set.Ioc (-R) (-B), Φ u ≤ ENNReal.ofReal (4 / h) * I := by
    rw [hΦdef, hIdef]
    exact hL
  have hB'' : ∫⁻ u in Set.Ioc (-B) B, Φ u ≤ ENNReal.ofReal (1 / h) * I := by
    rw [hΦdef, hIdef]
    exact hB'
  have hR'' : ∫⁻ u in Set.Ioc B R, Φ u ≤ ENNReal.ofReal (4 / h) * I := by
    rw [hΦdef, hIdef]
    exact hR'
  have harith : ENNReal.ofReal (4 / h) * I + ENNReal.ofReal (1 / h) * I
      + ENNReal.ofReal (4 / h) * I ≤ ENNReal.ofReal (30 / h) * I := by
    have h9 : ENNReal.ofReal (4 / h) + ENNReal.ofReal (1 / h) + ENNReal.ofReal (4 / h)
        ≤ ENNReal.ofReal (30 / h) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show (4 : ℝ) / h + 1 / h + 4 / h = 9 / h by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hh.le
    calc ENNReal.ofReal (4 / h) * I + ENNReal.ofReal (1 / h) * I + ENNReal.ofReal (4 / h) * I
        = (ENNReal.ofReal (4 / h) + ENNReal.ofReal (1 / h) + ENNReal.ofReal (4 / h)) * I := by
          ring
      _ ≤ ENNReal.ofReal (30 / h) * I := mul_le_mul_left h9 I
  calc ∫⁻ u : ℝ, Φ u
      = ∫⁻ u in Set.Ioc (-R) R, Φ u := h1
    _ = (∫⁻ u in Set.Ioc (-R) (-B), Φ u) + (∫⁻ u in Set.Ioc (-B) B, Φ u)
          + (∫⁻ u in Set.Ioc B R, Φ u) := h2
    _ ≤ ENNReal.ofReal (4 / h) * I + ENNReal.ofReal (1 / h) * I + ENNReal.ofReal (4 / h) * I :=
        add_le_add (add_le_add hL' hB'') hR''
    _ ≤ ENNReal.ofReal (30 / h) * I := harith
    _ = ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by rw [hIdef]

/-- Development copy of the target statement (same content, name `meanSq_leF`). -/
theorem meanSq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 →
    ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) w →
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z) ^ 2)
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3),
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ z in Submission.BoseGases.dlBox ℓ d u, w z) ^ 2)
        ≤ C * (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ *
            ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by
  refine ⟨30 ^ 3, by norm_num, ?_⟩
  intro ℓ d hℓ hd hd1 w hw
  have hcont : Continuous w := hw.continuous
  have H1 : ∀ {ℓ' h' : ℝ}, 0 < h' → h' ≤ ℓ' → ∀ G : ℝ → ℝ≥0∞,
      AEMeasurable G (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ' h' u, G x)
          / (volume (Work.BoseFixB1S.slI ℓ' h' u))) ^ 2
        ≤ ENNReal.ofReal (30 / h') * ∫⁻ x in Set.Icc (-ℓ' / 2) (ℓ' / 2), (G x) ^ 2 :=
    fun hh hhℓ G hG => oneDimMeanSqCore hh hhℓ hG
  have H3 : ∀ {ℓ' h' : ℝ}, 0 < h' → h' ≤ ℓ' → ∀ F : (Fin 3 → ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ' h' u, F y)
          / (volume (Work.BoseFixB1S.slBox ℓ' h' u))) ^ 2
        ≤ ENNReal.ofReal ((30 / h') ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ', (F y) ^ 2 :=
    fun hh hhℓ F hF => threeDimL hh hhℓ hF H1
  set W : E3 → ℝ≥0∞ := fun x => ENNReal.ofReal |w x| with hWdef
  have hWmeas : Measurable W := Measurable.ennreal_ofReal hcont.abs.measurable
  have hE3 := Work.BoseFixB1.Core.meanSq3dE3 (ℓ := ℓ) (d := d) hℓ hd hd1 H3 hWmeas
  set A : E3 → ℝ := fun u => (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
      ∫ z in Submission.BoseGases.dlBox ℓ d u, w z with hAdef
  have hW2 : ∀ x : E3, (W x) ^ 2 = ENNReal.ofReal ((w x) ^ 2) := by
    intro x
    rw [hWdef, ← ENNReal.ofReal_pow (abs_nonneg (w x)), sq_abs]
  have hsub : Submission.BoseGases.acube ℓ ⊆ Metric.closedBall (0 : E3) ℓ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Submission.BoseGases.mem_acube_iff] at hx
    have hco : ∀ i : Fin 3, |x i| ≤ ℓ / 2 := fun i => by
      have h := hx i
      rw [Set.mem_Icc] at h
      exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
    have h1 : ‖x‖ ^ 2 ≤ ℓ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2
          ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
            rw [WithLp.ofLp_toLp, Real.norm_eq_abs]
            exact hco i
        _ = 3 * (ℓ / 2) ^ 2 := by simp
        _ ≤ ℓ ^ 2 := by nlinarith [hℓ]
    nlinarith [norm_nonneg x, h1]
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ x ∈ Metric.closedBall (0 : E3) ℓ, ‖w x‖ ≤ C₀ :=
    (isCompact_closedBall (0 : E3) ℓ).exists_bound_of_continuousOn hcont.continuousOn
  set Cw : ℝ := |C₀| with hCwdef
  have hCw : ∀ x ∈ Metric.closedBall (0 : E3) ℓ, ‖w x‖ ≤ Cw := fun x hx =>
    le_trans (hC₀ x hx) (le_abs_self C₀)
  have hBlt : ∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2 < ⊤ := by
    have hle : ∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2
        ≤ ∫⁻ _x in Submission.BoseGases.acube ℓ, ENNReal.ofReal (Cw ^ 2) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)] with x hx
      rw [hW2 x]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : |w x| ≤ Cw := by
        rw [← Real.norm_eq_abs]
        exact hCw x (hsub hx)
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w x)) h1 2
    have h2 : ∫⁻ _x in Submission.BoseGases.acube ℓ, ENNReal.ofReal (Cw ^ 2)
        = ENNReal.ofReal (Cw ^ 2) * ENNReal.ofReal (ℓ ^ 3) := by
      rw [MeasureTheory.setLIntegral_const, Submission.BoseGases.acube_volume ℓ hℓ.le]
    rw [h2] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hpt : ∀ u : E3, ENNReal.ofReal ((A u) ^ 2)
      ≤ ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / (volume (Submission.BoseGases.dlBox ℓ d u))) ^ 2 := by
    intro u
    set M : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hMdef
    set Q : ℝ := ∫ z in Submission.BoseGases.dlBox ℓ d u, |w z| with hQdef
    set P : ℝ := ∫ z in Submission.BoseGases.dlBox ℓ d u, w z with hPdef
    have hMnn : 0 ≤ M := by
      rw [hMdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
      exact ENNReal.toReal_nonneg
    have hA : A u = (1 / M) * P := by rw [hAdef, hPdef, hMdef]
    rcases eq_or_lt_of_le hMnn with hM0 | hMpos
    · have hA0 : A u = 0 := by rw [hA, ← hM0, one_div, inv_zero, zero_mul]
      rw [hA0]
      simp
    · have hreal : |A u| ≤ M⁻¹ * Q := by
        have h1 : |A u| = M⁻¹ * |P| := by
          rw [hA, abs_mul, one_div, abs_of_pos (inv_pos.mpr hMpos)]
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hMnn)
        rw [hPdef, hQdef]
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (volume : Measure E3).restrict
            (Submission.BoseGases.dlBox ℓ d u)) (f := w)
      have hV : (volume (Submission.BoseGases.dlBox ℓ d u)) = ENNReal.ofReal M := by
        rw [hMdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
        exact (ENNReal.ofReal_toReal
          (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))).symm
      have hQle : ENNReal.ofReal Q ≤ ∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x := by
        have hd1 : ∫ z in Submission.BoseGases.dlBox ℓ d u, |w z|
            = (∫⁻ z in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |w z|).toReal :=
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae
            (μ := (volume : Measure E3).restrict (Submission.BoseGases.dlBox ℓ d u))
            (Filter.Eventually.of_forall fun z => abs_nonneg _) hcont.abs.aestronglyMeasurable
        rw [hQdef, hd1, hWdef]
        exact ENNReal.ofReal_toReal_le
      have hmain : ENNReal.ofReal (M⁻¹ * Q)
          ≤ (∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
            / (volume (Submission.BoseGases.dlBox ℓ d u)) := by
        rw [hV]
        calc ENNReal.ofReal (M⁻¹ * Q) = ENNReal.ofReal (M⁻¹) * ENNReal.ofReal Q :=
              ENNReal.ofReal_mul (inv_nonneg.mpr hMnn)
          _ = (ENNReal.ofReal M)⁻¹ * ENNReal.ofReal Q := by
              rw [ENNReal.ofReal_inv_of_pos hMpos]
          _ ≤ (ENNReal.ofReal M)⁻¹ * ∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x :=
              mul_le_mul' le_rfl hQle
          _ = (∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x) / ENNReal.ofReal M := by
              rw [div_eq_mul_inv, mul_comm]
      calc ENNReal.ofReal ((A u) ^ 2)
          = ENNReal.ofReal (|A u| ^ 2) := by rw [sq_abs]
        _ = ENNReal.ofReal |A u| ^ 2 := ENNReal.ofReal_pow (abs_nonneg _) 2
        _ ≤ ENNReal.ofReal (M⁻¹ * Q) ^ 2 :=
            pow_le_pow_left' (ENNReal.ofReal_le_ofReal hreal) 2
        _ ≤ ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
              / (volume (Submission.BoseGases.dlBox ℓ d u))) ^ 2 := pow_le_pow_left' hmain 2
  have hAmeas : AEMeasurable (fun u : E3 => (A u)) (volume : Measure E3) := by
    have hΦ : Continuous (fun x : Submission.BoseGases.X 1 => w (x 0)) :=
      hcont.comp (by fun_prop)
    have hbm := Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean (ℓ := ℓ) (d := d) hℓ
      (Φ := fun x : Submission.BoseGases.X 1 => w (x 0)) hΦ
    refine hbm.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Work.UBBInputs9.B.boxMean, hAdef, one_div]
  have hlin : ∫⁻ u : E3, ENNReal.ofReal ((A u) ^ 2)
      ≤ ∫⁻ u : E3, ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / (volume (Submission.BoseGases.dlBox ℓ d u))) ^ 2 :=
    lintegral_mono hpt
  have hA2meas : AEMeasurable (fun u : E3 => (A u) ^ 2) (volume : Measure E3) :=
    hAmeas.pow_const 2
  have hfin : ∫⁻ u : E3, (‖(A u) ^ 2‖ₑ) < ⊤ := by
    have h1 : ∫⁻ u : E3, ‖(A u) ^ 2‖ₑ ≤ ∫⁻ u : E3, ENNReal.ofReal ((A u) ^ 2) := by
      refine lintegral_mono fun u => ?_
      rw [Real.enorm_eq_ofReal (sq_nonneg (A u))]
    exact lt_of_le_of_lt (le_trans h1 hlin)
      (lt_of_le_of_lt hE3 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBlt))
  have hInt : MeasureTheory.Integrable (fun u : E3 => (A u) ^ 2) (volume : Measure E3) :=
    ⟨hA2meas.aestronglyMeasurable, hfin⟩
  have hBconv : (∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2).toReal
      = ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by
    have h1 := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun z : E3 => (w z) ^ 2)
      (Filter.Eventually.of_forall fun z => sq_nonneg (w z))
      ((hcont.pow 2).aestronglyMeasurable)
    rw [h1]
    congr 1
    exact lintegral_congr fun x => hW2 x
  have hIneq : (∫ u : E3, (A u) ^ 2)
      ≤ 30 ^ 3 * (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ *
          ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by
    have hAint : ∫ u : E3, (A u) ^ 2 = (∫⁻ u : E3, ENNReal.ofReal ((A u) ^ 2)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun u => sq_nonneg (A u)) hA2meas.aestronglyMeasurable
    have hI0 : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 :=
      integral_nonneg fun z => sq_nonneg _
    have hpos : 0 ≤ ((ℓ * d) ^ 3)⁻¹ := by positivity
    have h1 : (1 : ℝ) ≤ (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 := by
      have h2 : (1 : ℝ) ≤ 1 + (ℓ * d)⁻¹ + |Real.log d| := by
        have h3 : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr (mul_pos hℓ hd).le
        have h4 : 0 ≤ |Real.log d| := abs_nonneg _
        linarith
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h2 3
    have hkey : ((ℓ * d) ^ 3)⁻¹
        ≤ (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ := by
      calc ((ℓ * d) ^ 3)⁻¹ = 1 * ((ℓ * d) ^ 3)⁻¹ := (one_mul _).symm
        _ ≤ (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 hpos
    calc ∫ u : E3, (A u) ^ 2
        = (∫⁻ u : E3, ENNReal.ofReal ((A u) ^ 2)).toReal := hAint
      _ ≤ (ENNReal.ofReal ((30 / (ℓ * d)) ^ 3) *
            ∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2).toReal :=
          ENNReal.toReal_mono
            (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBlt))
            (le_trans hlin hE3)
      _ = (30 / (ℓ * d)) ^ 3 * (∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      _ = (30 / (ℓ * d)) ^ 3 * ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by rw [hBconv]
      _ ≤ 30 ^ 3 * (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ *
            ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by
          calc (30 / (ℓ * d)) ^ 3 * ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2
              = 30 ^ 3 * ((ℓ * d) ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by
                rw [div_pow, div_eq_mul_inv]
            _ ≤ 30 ^ 3 * ((1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹) *
                  ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) hI0
            _ = 30 ^ 3 * (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ *
                  ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by ring
  exact ⟨hInt, hIneq⟩

end Work.BoseFixB1.Core.MM
