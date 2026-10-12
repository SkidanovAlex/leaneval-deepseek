import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.sectorCountBoxAux
import Submission.Work.BoseFixB1B.volume_iUnion_collar_le
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.collarCylinder` — the collar volume bounds at the sliding box

Self-contained copies (with distinct names) of the two collar-volume inputs used by the mass
convergence of the sharp extension:

* `collarBox_le` — the volume of the part of `B(u) = dlBox L d u` on which the box margin is `< δ`
  is `O(δ)` (from `Work.BoseFixB1B.volume_iUnion_collar_le`);
* `collarCylCoord_le`, `collarCyl_le` — the same for one coordinate of a configuration in the
  ambient box, and for the union over the slots (after
  `Work.BoseFixB2.Pot.lintegral_coord_abox`).

The statements (and the argument) are those of `BoseFixB1B/SharpFibreCollar.lean`; they are
reproved here so that the sharp-extension mass convergence does not depend on that module.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The collar of the sliding box: the part of `B(u)` with box margin `< δ`. -/
def collarBoxSet (L d δ : ℝ) (u : E3) : Set E3 :=
  dlBox L d u ∩ {x : E3 | boxMargin L d u x < δ}

lemma collarBoxSet_subset_dlBox (L d δ : ℝ) (u : E3) : collarBoxSet L d δ u ⊆ dlBox L d u :=
  Set.inter_subset_left

lemma collarBoxSet_subset_acube (L d δ : ℝ) (u : E3) : collarBoxSet L d δ u ⊆ acube L :=
  fun x hx => ((mem_dlBox_iff L d u x).mp (collarBoxSet_subset_dlBox L d δ u hx)).1

/-- `boxMargin` is continuous (it is a finite minimum of continuous functions). -/
lemma continuous_boxMargin_aux (L d : ℝ) (u : E3) : Continuous (boxMargin L d u) := by
  unfold boxMargin
  fun_prop

lemma measurableSet_collarBoxSet (L d δ : ℝ) (u : E3) : MeasurableSet (collarBoxSet L d δ u) := by
  refine (measurableSet_dlBox L d u).inter ?_
  exact (isOpen_lt (continuous_boxMargin_aux L d u) continuous_const).measurableSet

/-- **Geometry**: a point of the box with margin `< δ` has one of its six coordinate margins `< δ`. -/
lemma boxMargin_cover {L d δ : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) {x : E3}
    (hx : x ∈ dlBox L d u) (hm : boxMargin L d u x < δ) :
    (∃ i : Fin 3, (∀ m : Fin 3, |x m| ≤ L / 2) ∧ L / 2 - |x i| < δ)
      ∨ (∃ i : Fin 3, (∀ m : Fin 3, |(x - (L * d) • u) m| ≤ L * d / 2)
          ∧ L * d / 2 - |(x - (L * d) • u) i| < δ) := by
  obtain ⟨h1, h2⟩ := (mem_dlBox_iff L d u x).mp hx
  rw [mem_acube_iff] at h1 h2
  rw [boxMargin] at hm
  rcases min_lt_iff.mp hm with hA | hB
  · rcases (Finset.inf'_lt_iff Finset.univ_nonempty).mp hA with ⟨i, -, hi⟩
    exact Or.inl ⟨i, fun m => abs_le.mpr ⟨by linarith [(h1 m).1], by linarith [(h1 m).2]⟩, hi⟩
  · rcases (Finset.inf'_lt_iff Finset.univ_nonempty).mp hB with ⟨i, -, hi⟩
    exact Or.inr ⟨i, fun m => abs_le.mpr ⟨by linarith [(h2 m).1], by linarith [(h2 m).2]⟩, hi⟩

/-- **The collar volume bound on the sliding box.** -/
theorem collarBox_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
      (volume : Measure E3) (collarBoxSet L d δ u) ≤ ENNReal.ofReal (C * δ) := by
  refine ⟨24 * (L / 2) ^ 2 + 24 * (L * d / 2) ^ 2, by positivity, fun δ hδ => ?_⟩
  set S1 : Set E3 := ⋃ i : Fin 3,
    {x : E3 | (∀ m : Fin 3, |(x - (0 : E3)) m| ≤ L / 2) ∧ L / 2 - |(x - (0 : E3)) i| < δ} with hS1
  set S2 : Set E3 := ⋃ i : Fin 3,
    {x : E3 | (∀ m : Fin 3, |(x - (L * d) • u) m| ≤ L * d / 2)
      ∧ L * d / 2 - |(x - (L * d) • u) i| < δ} with hS2
  have hcover : collarBoxSet L d δ u ⊆ S1 ∪ S2 := by
    intro x hx
    rcases boxMargin_cover hL hd u (collarBoxSet_subset_dlBox L d δ u hx) hx.2 with
      ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, by simpa using h1, by simpa using h2⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, h1, h2⟩)
  calc (volume : Measure E3) (collarBoxSet L d δ u)
      ≤ (volume : Measure E3) (S1 ∪ S2) := measure_mono hcover
    _ ≤ (volume : Measure E3) S1 + (volume : Measure E3) S2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (24 * (L / 2) ^ 2 * δ) + ENNReal.ofReal (24 * (L * d / 2) ^ 2 * δ) := by
        refine add_le_add ?_ ?_
        · rw [hS1]
          exact volume_iUnion_collar_le (c := L / 2) (δ := δ) (by positivity) hδ (0 : E3)
        · rw [hS2]
          exact volume_iUnion_collar_le (c := L * d / 2) (δ := δ) (by positivity) hδ
            ((L * d) • u)
    _ = ENNReal.ofReal ((24 * (L / 2) ^ 2 + 24 * (L * d / 2) ^ 2) * δ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The collar of one coordinate.**  For each slot `i`, the volume of the configurations in the
ambient box whose `i`-th coordinate lies in the collar is `O(δ)`. -/
theorem collarCylCoord_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ i : Fin n,
      (volume : Measure (X n)) {x : X n | x ∈ abox n L ∧ x i ∈ collarBoxSet L d δ u}
        ≤ ENNReal.ofReal (C * δ) := by
  obtain ⟨Cc, hCc0, hCc⟩ := collarBox_le hL hd u
  refine ⟨(L ^ 3) ^ (n - 1) * Cc, by positivity, fun δ hδ i => ?_⟩
  set G : E3 → ℝ≥0∞ :=
    (collarBoxSet L d δ u ∩ acube L).indicator (fun _ => (1 : ℝ≥0∞)) with hGdef
  have hGs : AEStronglyMeasurable G (volume : Measure E3) :=
    (Measurable.indicator measurable_const
      ((measurableSet_collarBoxSet L d δ u).inter (acube_measurable L))).aestronglyMeasurable
  have hGint : (∫⁻ a : E3, G a ∂((volume : Measure E3).restrict (acube L)))
      = (volume : Measure E3) (collarBoxSet L d δ u) := by
    have hset : collarBoxSet L d δ u ∩ acube L = collarBoxSet L d δ u :=
      Set.inter_eq_self_of_subset_left (collarBoxSet_subset_acube L d δ u)
    have hmeas : MeasurableSet (collarBoxSet L d δ u ∩ acube L) :=
      (measurableSet_collarBoxSet L d δ u).inter (acube_measurable L)
    rw [hGdef, MeasureTheory.lintegral_indicator hmeas, MeasureTheory.setLIntegral_one,
      Measure.restrict_apply hmeas,
      Set.inter_eq_self_of_subset_left (Set.inter_subset_right : collarBoxSet L d δ u ∩ acube L
        ⊆ acube L), hset]
  have hmeas_i : MeasurableSet {x : X n | x i ∈ collarBoxSet L d δ u} :=
    (measurableSet_collarBoxSet L d δ u).preimage (continuous_apply i).measurable
  have hstep := Work.BoseFixB2.Pot.lintegral_coord_abox (n := n) (ℓ := L) hL i hGs
  have hLe : (∫⁻ x, ({x : X n | x i ∈ collarBoxSet L d δ u}).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂((volume : Measure (X n)).restrict (abox n L)))
      ≤ ∫⁻ x, G (x i) ∂((volume : Measure (X n)).restrict (abox n L)) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (abox_measurable n L)]
    filter_upwards with x hx
    have hmem : x i ∈ acube L := hx i
    by_cases hc : x i ∈ collarBoxSet L d δ u
    · have h1 : ({x : X n | x i ∈ collarBoxSet L d δ u}).indicator (fun _ => (1 : ℝ≥0∞)) x = 1 :=
        Set.indicator_of_mem (s := {x : X n | x i ∈ collarBoxSet L d δ u}) hc _
      have h2 : G (x i) = 1 := by
        rw [hGdef]
        exact Set.indicator_of_mem (s := collarBoxSet L d δ u ∩ acube L) ⟨hc, hmem⟩ _
      rw [h1, h2]
    · have h1 : ({x : X n | x i ∈ collarBoxSet L d δ u}).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 :=
        Set.indicator_of_notMem (s := {x : X n | x i ∈ collarBoxSet L d δ u}) hc _
      rw [h1]
      exact bot_le
  have hmid : (∫⁻ x, G (x i) ∂((volume : Measure (X n)).restrict (abox n L)))
      = (volume : Measure E3) (acube L) ^ (n - 1) * (volume : Measure E3) (collarBoxSet L d δ u) := by
    rw [hstep, hGint]
  calc (volume : Measure (X n)) {x : X n | x ∈ abox n L ∧ x i ∈ collarBoxSet L d δ u}
      = ((volume : Measure (X n)).restrict (abox n L))
          {x : X n | x i ∈ collarBoxSet L d δ u} := by
        rw [Measure.restrict_apply hmeas_i]
        congr 1
        ext x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        exact and_comm
    _ = ∫⁻ x, ({x : X n | x i ∈ collarBoxSet L d δ u}).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂((volume : Measure (X n)).restrict (abox n L)) := by
        rw [MeasureTheory.lintegral_indicator hmeas_i, MeasureTheory.setLIntegral_one]
    _ ≤ ∫⁻ x, G (x i) ∂((volume : Measure (X n)).restrict (abox n L)) := hLe
    _ = (volume : Measure E3) (acube L) ^ (n - 1) * (volume : Measure E3) (collarBoxSet L d δ u) :=
        hmid
    _ ≤ (volume : Measure E3) (acube L) ^ (n - 1) * ENNReal.ofReal (Cc * δ) :=
        mul_le_mul' le_rfl (hCc δ hδ)
    _ = ENNReal.ofReal ((L ^ 3) ^ (n - 1) * (Cc * δ)) := by
        rw [acube_volume L hL.le, ← ENNReal.ofReal_pow (by positivity)]
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((L ^ 3) ^ (n - 1) * Cc * δ) := by
        congr 1
        ring

/-- **The collar of a configuration**: the union over the slots. -/
theorem collarCyl_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
      (volume : Measure (X n))
          {x : X n | x ∈ abox n L ∧ ∃ i : Fin n, x i ∈ collarBoxSet L d δ u}
        ≤ ENNReal.ofReal (C * δ) := by
  obtain ⟨C, hC0, hC⟩ := collarCylCoord_le (L := L) (d := d) hL hd u n
  refine ⟨max 1 (C * n), le_trans zero_le_one (le_max_left _ _), fun δ hδ => ?_⟩
  have hUnion : {x : X n | x ∈ abox n L ∧ ∃ i : Fin n, x i ∈ collarBoxSet L d δ u}
      ⊆ ⋃ i : Fin n, {x : X n | x ∈ abox n L ∧ x i ∈ collarBoxSet L d δ u} := by
    rintro x ⟨hx, i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  calc (volume : Measure (X n))
        {x : X n | x ∈ abox n L ∧ ∃ i : Fin n, x i ∈ collarBoxSet L d δ u}
      ≤ (volume : Measure (X n))
          (⋃ i : Fin n, {x : X n | x ∈ abox n L ∧ x i ∈ collarBoxSet L d δ u}) :=
        measure_mono hUnion
    _ ≤ ∑ i : Fin n, (volume : Measure (X n))
          {x : X n | x ∈ abox n L ∧ x i ∈ collarBoxSet L d δ u} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (C * δ) := Finset.sum_le_sum (fun i _ => hC δ hδ i)
    _ = ENNReal.ofReal (C * n * δ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (max 1 (C * n) * δ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : C * n * δ ≤ max 1 (C * n) * δ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
        linarith

end Work.BoseFixB1B
