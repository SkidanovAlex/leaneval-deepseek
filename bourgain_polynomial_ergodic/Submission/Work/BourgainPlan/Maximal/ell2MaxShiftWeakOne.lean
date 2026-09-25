import Mathlib
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoGrid
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.ell2F_hlMax_twoGrids
import Submission.Work.BourgainPlan.Maximal.linearizedWeakType
import Submission.Work.BourgainPlan.Maximal.lintegral_lwtGood_eq
import Submission.Work.BourgainPlan.Maximal.ae_le_dyMax

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

/-!
# The weak-`(1,1)` bound for the `ℓ²`-valued half-shifted dyadic maximal function

The target statement `ell2MaxShiftWeakOne` is the weak-`(1,1)` endpoint of the vector-valued
(Fefferman--Stein) maximal inequality for the *half-shifted* dyadic grid
`dyCellShift (1/2) n k = [(k+1/2)2^n, (k+3/2)2^n)`, which is not laminar.  The proof follows the
Calderón--Zygmund scheme of `linearizedWeakType`, with the standard (laminar) dyadic grid used to
define the decomposition; the only new point is that *every* half-shifted cell is a union of two
consecutive standard dyadic cells, so the mean-zero property of the CZ bad part (which holds on
every standard dyadic cell that is not contained in a maximal CZ cell) transfers to the shifted
grid, at the price of the one-step neighbourhood `emswStar` of the maximal cells.
-/

/-- The half-shifted dyadic cell of level `n` is the union of the two consecutive dyadic cells
`dyCell (n-1) (2k+1)` and `dyCell (n-1) (2k+2)` of the standard grid. -/
lemma emsw_dyCellShift_half_eq (n k : ℤ) :
    dyCellShift (1 / 2) n k = dyCell (n - 1) (2 * k + 1) ∪ dyCell (n - 1) (2 * k + 2) := by
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    have h := zpow_succ_two (n - 1)
    rw [show n - 1 + 1 = n by ring] at h
    exact h
  have h1 : ((k : ℝ) + 1 / 2) * (2 : ℝ) ^ n = ((2 * k + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (n - 1) := by
    rw [hpow]; push_cast; ring
  have h2 : (((k : ℝ) + 1 / 2) + 1) * (2 : ℝ) ^ n = ((2 * k + 3 : ℤ) : ℝ) * (2 : ℝ) ^ (n - 1) := by
    rw [hpow]; push_cast; ring
  have e1 : (((2 * k + 1 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ (n - 1)
      = ((2 * k + 2 : ℤ) : ℝ) * (2 : ℝ) ^ (n - 1) := by push_cast; ring
  have e2 : (((2 * k + 2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ (n - 1)
      = ((2 * k + 3 : ℤ) : ℝ) * (2 : ℝ) ^ (n - 1) := by push_cast; ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := zpow_two_pos _
  unfold dyCellShift dyCell
  rw [h1, h2, e1, e2]
  exact (Set.Ico_union_Ico_eq_Ico (by nlinarith [hpos]) (by nlinarith [hpos])).symm

lemma emsw_dyCell_succ_subset (m' m j k : ℤ) (h : dyCell m' j ⊆ dyCell m k) :
    dyCell m' (j + 1) ⊆ dyCell m k ∪ dyCell m (k + 1) := by
  have hpm' : (0 : ℝ) < (2 : ℝ) ^ m' := zpow_two_pos _
  have hpm : (0 : ℝ) < (2 : ℝ) ^ m := zpow_two_pos _
  have hjlt : (j : ℝ) * (2 : ℝ) ^ m' < ((j : ℝ) + 1) * (2 : ℝ) ^ m' := by nlinarith
  obtain ⟨hA, hB⟩ := (Set.Ico_subset_Ico_iff hjlt).mp h
  have hmm : (2 : ℝ) ^ m' ≤ (2 : ℝ) ^ m := by
    nlinarith [hA, hB, mul_pos hpm' hpm]
  have hlt' : ((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m' < (((j + 1 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ m' := by
    nlinarith [hpm']
  have hsub : dyCell m' (j + 1) ⊆ Set.Ico ((k : ℝ) * (2 : ℝ) ^ m) (((k : ℝ) + 2) * (2 : ℝ) ^ m) := by
    rw [dyCell]
    refine (Set.Ico_subset_Ico_iff hlt').mpr ⟨?_, ?_⟩
    · calc (k : ℝ) * (2 : ℝ) ^ m ≤ (j : ℝ) * (2 : ℝ) ^ m' := hA
        _ ≤ ((j : ℝ) + 1) * (2 : ℝ) ^ m' := by nlinarith
        _ = ((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m' := by push_cast; ring
    · calc (((j + 1 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ m'
          = ((j : ℝ) + 1) * (2 : ℝ) ^ m' + (2 : ℝ) ^ m' := by push_cast; ring
        _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ m + (2 : ℝ) ^ m' := by linarith [hB]
        _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ m + (2 : ℝ) ^ m := by linarith [hmm]
        _ = ((k : ℝ) + 2) * (2 : ℝ) ^ m := by ring
  have hIco : dyCell m k ∪ dyCell m (k + 1)
      = Set.Ico ((k : ℝ) * (2 : ℝ) ^ m) (((k : ℝ) + 2) * (2 : ℝ) ^ m) := by
    have h1 : dyCell m k = Set.Ico ((k : ℝ) * (2 : ℝ) ^ m) (((k : ℝ) + 1) * (2 : ℝ) ^ m) := rfl
    have h2 : dyCell m (k + 1) = Set.Ico (((k : ℝ) + 1) * (2 : ℝ) ^ m) (((k : ℝ) + 2) * (2 : ℝ) ^ m) := by
      unfold dyCell
      push_cast
      ring_nf
    rw [h1, h2, Set.Ico_union_Ico_eq_Ico (by nlinarith) (by nlinarith)]
  rwa [hIco]

lemma emsw_dyCell_pred_subset (m' m j k : ℤ) (h : dyCell m' j ⊆ dyCell m k) :
    dyCell m' (j - 1) ⊆ dyCell m k ∪ dyCell m (k - 1) := by
  have hpm' : (0 : ℝ) < (2 : ℝ) ^ m' := zpow_two_pos _
  have hpm : (0 : ℝ) < (2 : ℝ) ^ m := zpow_two_pos _
  have hjlt : (j : ℝ) * (2 : ℝ) ^ m' < ((j : ℝ) + 1) * (2 : ℝ) ^ m' := by nlinarith
  obtain ⟨hA, hB⟩ := (Set.Ico_subset_Ico_iff hjlt).mp h
  have hmm : (2 : ℝ) ^ m' ≤ (2 : ℝ) ^ m := by
    nlinarith [hA, hB, mul_pos hpm' hpm]
  have hlt' : ((j - 1 : ℤ) : ℝ) * (2 : ℝ) ^ m' < (((j - 1 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ m' := by
    push_cast
    nlinarith [hpm']
  have hsub : dyCell m' (j - 1) ⊆ Set.Ico (((k : ℝ) - 1) * (2 : ℝ) ^ m) (((k : ℝ) + 1) * (2 : ℝ) ^ m) := by
    rw [dyCell]
    refine (Set.Ico_subset_Ico_iff hlt').mpr ⟨?_, ?_⟩
    · calc (((k : ℝ) - 1)) * (2 : ℝ) ^ m = (k : ℝ) * (2 : ℝ) ^ m - (2 : ℝ) ^ m := by ring
        _ ≤ (j : ℝ) * (2 : ℝ) ^ m' - (2 : ℝ) ^ m' := by linarith
        _ = ((j - 1 : ℤ) : ℝ) * (2 : ℝ) ^ m' := by push_cast; ring
    · calc (((j - 1 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ m' = (j : ℝ) * (2 : ℝ) ^ m' := by push_cast; ring
        _ ≤ ((j : ℝ) + 1) * (2 : ℝ) ^ m' := by nlinarith
        _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ m := hB
  have hIco : dyCell m k ∪ dyCell m (k - 1)
      = Set.Ico (((k : ℝ) - 1) * (2 : ℝ) ^ m) (((k : ℝ) + 1) * (2 : ℝ) ^ m) := by
    have h0 : dyCell m (k - 1) = Set.Ico (((k : ℝ) - 1) * (2 : ℝ) ^ m) ((k : ℝ) * (2 : ℝ) ^ m) := by
      unfold dyCell
      push_cast
      ring_nf
    have h1 : dyCell m k = Set.Ico ((k : ℝ) * (2 : ℝ) ^ m) (((k : ℝ) + 1) * (2 : ℝ) ^ m) := rfl
    rw [h1, h0, Set.union_comm]
    exact Set.Ico_union_Ico_eq_Ico (by nlinarith) (by nlinarith)
  rwa [hIco]

/-- The union of the maximal CZ cells of `czMax σ a` together with their dyadic neighbours at the
same level.  This is the set on which the half-shifted cell averages of the CZ bad part may fail to
vanish. -/
noncomputable def emswStar (σ : ℝ → ℝ≥0∞) (a : ℝ≥0∞) : Set ℝ :=
  ⋃ p ∈ czMax σ a, (dyCell p.1 p.2 ∪ dyCell p.1 (p.2 + 1) ∪ dyCell p.1 (p.2 - 1))

lemma measurableSet_emswStar (σ : ℝ → ℝ≥0∞) (a : ℝ≥0∞) :
    MeasurableSet (emswStar σ a) :=
  MeasurableSet.biUnion (Set.countable_univ.mono (Set.subset_univ _)) fun p _ =>
    ((dyCell_measurable p.1 p.2).union (dyCell_measurable p.1 (p.2 + 1))).union
      (dyCell_measurable p.1 (p.2 - 1))

lemma volume_emswStar_le {σ : ℝ → ℝ≥0∞} {a : ℝ≥0∞} (ha : 0 < a) (hat : a ≠ ⊤) :
    volume (emswStar σ a) ≤ 3 * (a⁻¹ * ∫⁻ y, σ y) := by
  have hsub : emswStar σ a ⊆ ⋃ p : {p : ℤ × ℤ // p ∈ czMax σ a},
      (dyCell p.1.1 p.1.2 ∪ dyCell p.1.1 (p.1.2 + 1) ∪ dyCell p.1.1 (p.1.2 - 1)) := by
    intro x hx
    rw [emswStar, mem_iUnion₂] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  calc volume (emswStar σ a)
      ≤ ∑' p : {p : ℤ × ℤ // p ∈ czMax σ a},
          volume (dyCell p.1.1 p.1.2 ∪ dyCell p.1.1 (p.1.2 + 1) ∪ dyCell p.1.1 (p.1.2 - 1)) :=
        (MeasureTheory.measure_mono hsub).trans (MeasureTheory.measure_iUnion_le _)
    _ ≤ ∑' p : {p : ℤ × ℤ // p ∈ czMax σ a}, 3 * volume (dyCell p.1.1 p.1.2) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        have hv : ∀ k : ℤ, volume (dyCell p.1.1 k) = volume (dyCell p.1.1 p.1.2) := by
          intro k; rw [dyCell_volume_eq, dyCell_volume_eq]
        calc volume (dyCell p.1.1 p.1.2 ∪ dyCell p.1.1 (p.1.2 + 1) ∪ dyCell p.1.1 (p.1.2 - 1))
            ≤ volume (dyCell p.1.1 p.1.2 ∪ dyCell p.1.1 (p.1.2 + 1))
              + volume (dyCell p.1.1 (p.1.2 - 1)) := measure_union_le _ _
          _ ≤ (volume (dyCell p.1.1 p.1.2) + volume (dyCell p.1.1 (p.1.2 + 1)))
              + volume (dyCell p.1.1 (p.1.2 - 1)) :=
              add_le_add (measure_union_le _ _) le_rfl
          _ = 3 * volume (dyCell p.1.1 p.1.2) := by
              rw [hv (p.1.2 + 1), hv (p.1.2 - 1)]; ring
    _ = 3 * ∑' p : {p : ℤ × ℤ // p ∈ czMax σ a}, volume (dyCell p.1.1 p.1.2) :=
        ENNReal.tsum_mul_left
    _ ≤ 3 * (a⁻¹ * ∫⁻ y, σ y) := mul_le_mul_right (tsum_czMax_volume_le ha hat) 3

/-- If `x` is outside `emswStar σ a`, then **neither half** of the half-shifted cell of `x` is
contained in a maximal CZ cell. -/
lemma emsw_halves_not_subset {σ : ℝ → ℝ≥0∞} {a : ℝ≥0∞} {x : ℝ}
    (hx : x ∉ emswStar σ a) (n k : ℤ) (hxC : x ∈ dyCellShift (1 / 2) n k) :
    (∀ p ∈ czMax σ a, ¬ dyCell (n - 1) (2 * k + 1) ⊆ dyCell p.1 p.2) ∧
      (∀ p ∈ czMax σ a, ¬ dyCell (n - 1) (2 * k + 2) ⊆ dyCell p.1 p.2) := by
  have hxsplit : x ∈ dyCell (n - 1) (2 * k + 1) ∪ dyCell (n - 1) (2 * k + 2) := by
    rwa [emsw_dyCellShift_half_eq] at hxC
  constructor
  · intro p hp hsub
    apply hx
    rw [emswStar, mem_iUnion₂]
    refine ⟨p, hp, ?_⟩
    simp only [Set.mem_union] at hxsplit ⊢
    rcases hxsplit with h1 | h2
    · exact Or.inl (Or.inl (hsub h1))
    · have h2' : x ∈ dyCell (n - 1) ((2 * k + 1) + 1) := by
        rw [show (2 * k + 1) + 1 = 2 * k + 2 by ring]; exact h2
      rcases emsw_dyCell_succ_subset (n - 1) p.1 (2 * k + 1) p.2 hsub h2' with h3 | h3
      · exact Or.inl (Or.inl h3)
      · exact Or.inl (Or.inr h3)
  · intro p hp hsub
    apply hx
    rw [emswStar, mem_iUnion₂]
    refine ⟨p, hp, ?_⟩
    simp only [Set.mem_union] at hxsplit ⊢
    rcases hxsplit with h1 | h2
    · have h1' : x ∈ dyCell (n - 1) ((2 * k + 2) - 1) := by
        rw [show (2 * k + 2) - 1 = 2 * k + 1 by ring]; exact h1
      rcases emsw_dyCell_pred_subset (n - 1) p.1 (2 * k + 2) p.2 hsub h1' with h3 | h3
      · exact Or.inl (Or.inl h3)
      · exact Or.inr h3
    · exact Or.inl (Or.inl (hsub h2))

/-- Off `emswStar σ a`, the half-shifted dyadic maximal function of `‖f t ·‖ₑ` and that of the
CZ good part `lwtG f σ a t` agree: the bad part has vanishing integral over every standard dyadic
cell whose halves occur inside a half-shifted cell containing `x`. -/
lemma emsw_dyMaxShift_lwtG_eq {n : ℕ} {f : Fin n → ℝ → ℝ} (hf : ∀ t, Measurable (f t))
    {σ : ℝ → ℝ≥0∞} {a : ℝ≥0∞}
    (hintabs : ∀ t, Integrable (fun y => |f t y|))
    (t : Fin n) {x : ℝ} (hx : x ∉ emswStar σ a) :
    dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x
      = dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x := by
  have hdisp : ∀ (m k : ℤ) (_ : x ∈ dyCellShift (1 / 2) m k),
      ∫⁻ y in dyCellShift (1 / 2) m k, (fun y => ‖lwtG f σ a t y‖ₑ) y
        = ∫⁻ y in dyCellShift (1 / 2) m k, (fun y => ‖f t y‖ₑ) y := by
    intro m k hmem
    obtain ⟨hR1, hR2⟩ := emsw_halves_not_subset hx m k hmem
    have h1 := lintegral_lwtGood_eq (σ := σ) (c := a) (ψ := fun y => |f t y|)
      (fun y => abs_nonneg _) (hf t).abs (hintabs t) (m := m - 1) (k := 2 * k + 1) hR1
    have h2 := lintegral_lwtGood_eq (σ := σ) (c := a) (ψ := fun y => |f t y|)
      (fun y => abs_nonneg _) (hf t).abs (hintabs t) (m := m - 1) (k := 2 * k + 2) hR2
    have hL1 : ∫⁻ y in dyCell (m - 1) (2 * k + 1), (fun y => ‖lwtG f σ a t y‖ₑ) y
        = ∫⁻ y in dyCell (m - 1) (2 * k + 1),
            ENNReal.ofReal (lwtGood (fun y => |f t y|) σ a y) := by
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal (lwtG_nonneg f σ a t y)]
      rfl
    have hR1' : ∫⁻ y in dyCell (m - 1) (2 * k + 1), (fun y => ‖f t y‖ₑ) y
        = ∫⁻ y in dyCell (m - 1) (2 * k + 1), ENNReal.ofReal (|f t y|) := by
      refine lintegral_congr fun y => ?_
      exact Real.enorm_eq_ofReal_abs (f t y)
    have hL2 : ∫⁻ y in dyCell (m - 1) (2 * k + 2), (fun y => ‖lwtG f σ a t y‖ₑ) y
        = ∫⁻ y in dyCell (m - 1) (2 * k + 2),
            ENNReal.ofReal (lwtGood (fun y => |f t y|) σ a y) := by
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal (lwtG_nonneg f σ a t y)]
      rfl
    have hR2' : ∫⁻ y in dyCell (m - 1) (2 * k + 2), (fun y => ‖f t y‖ₑ) y
        = ∫⁻ y in dyCell (m - 1) (2 * k + 2), ENNReal.ofReal (|f t y|) := by
      refine lintegral_congr fun y => ?_
      exact Real.enorm_eq_ofReal_abs (f t y)
    have hdisj : Disjoint (dyCell (m - 1) (2 * k + 1)) (dyCell (m - 1) (2 * k + 2)) :=
      dyCell_disjoint (by omega : 2 * k + 1 ≠ 2 * k + 2)
    have hmeas1 : MeasurableSet (dyCell (m - 1) (2 * k + 1)) := dyCell_measurable _ _
    have hmeas2 : MeasurableSet (dyCell (m - 1) (2 * k + 2)) := dyCell_measurable _ _
    rw [emsw_dyCellShift_half_eq, MeasureTheory.lintegral_union hmeas2 hdisj,
      MeasureTheory.lintegral_union hmeas2 hdisj]
    rw [hL1, h1, ← hR1', hL2, h2, ← hR2']
  have hcell : ∀ (m k : ℤ) (hmem : x ∈ dyCellShift (1 / 2) m k),
      ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * ∫⁻ y in dyCellShift (1 / 2) m k, (fun y => ‖f t y‖ₑ) y
        = ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹)
          * ∫⁻ y in dyCellShift (1 / 2) m k, (fun y => ‖lwtG f σ a t y‖ₑ) y := by
    intro m k hmem
    rw [hdisp m k hmem]
  unfold dyMaxShift
  refine le_antisymm (iSup_le fun m => iSup_le fun k => iSup_le fun hmem => ?_)
    (iSup_le fun m => iSup_le fun k => iSup_le fun hmem => ?_)
  · rw [hcell m k hmem]
    exact le_iSup_of_le m (le_iSup_of_le k (le_iSup_of_le hmem le_rfl))
  · rw [← hcell m k hmem]
    exact le_iSup_of_le m (le_iSup_of_le k (le_iSup_of_le hmem le_rfl))


/-- Measurability of the half-shifted dyadic maximal function in `x` (for an arbitrary `φ`). -/
private lemma emsw_dyMaxShift_measurable (α : ℝ) (φ : ℝ → ℝ≥0∞) : Measurable (dyMaxShift α φ) := by
  have h : dyMaxShift α φ = fun x => ⨆ (p : ℤ × ℤ), (dyCellShift α p.1 p.2).indicator
      (fun _ => ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹) * ∫⁻ y in dyCellShift α p.1 p.2, φ y) x := by
    funext x
    refine le_antisymm ?_ ?_
    · unfold dyMaxShift
      refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
      refine le_iSup_of_le (n, k) ?_
      rw [Set.indicator_of_mem hx]
    · refine iSup_le fun p => ?_
      by_cases hp : x ∈ dyCellShift α p.1 p.2
      · rw [Set.indicator_of_mem hp]
        unfold dyMaxShift
        exact le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le hp le_rfl))
      · rw [Set.indicator_of_notMem hp]; exact bot_le
  rw [h]
  exact Measurable.iSup fun p =>
    Measurable.indicator measurable_const (dyCellShift_measurable α p.1 p.2)

/-- **The `L²(ℓ²)` bound for the half-shifted `ℓ²`-valued dyadic maximal function**, uniform in the
number of components: it is the sum of the scalar strong `(2,2)` bounds of `hlMax` (to which
`dyMaxShift (1/2)` is pointwise dominated). -/
lemma emsw_lintegral_ell2MaxShift_sq_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (g : Fin n → ℝ → ℝ), (∀ t, Measurable (g t)) →
      ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ))
        ≤ ENNReal.ofReal (K ^ (2 : ℝ)) * ∫⁻ x, ell2Sq g x := by
  obtain ⟨C, hC, hb⟩ :=
    Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num : (1 : ℝ) < 2)
  refine ⟨C, hC, fun n g hg => ?_⟩
  have hsum : ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ))
      = ∑ t : Fin n, ∫⁻ x, (dyMaxShift (1 / 2) (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ) := by
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
      (emsw_dyMaxShift_measurable (1 / 2) (fun y => ‖g t y‖ₑ))
  have hSq : ∫⁻ x, ell2Sq g x = ∑ t : Fin n, ∫⁻ x, ‖g t x‖ₑ ^ (2 : ℝ) := by
    unfold ell2Sq
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (hg t).enorm
  rw [hsum, hSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  refine le_trans (MeasureTheory.lintegral_mono fun x => ?_) (hb (g t))
  exact ENNReal.rpow_le_rpow (dyMaxShift_le_hlMax (1 / 2) (fun y => ‖g t y‖ₑ) x)
    (by norm_num : (0 : ℝ) ≤ 2)


/-- **The weak-`(1,1)` bound for the `ℓ²`-valued half-shifted dyadic maximal function, uniform in
the number of components.** -/
theorem ell2MaxShiftWeakOne :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {x : ℝ | ENNReal.ofReal lam <
          (∑ t, (Work.BourgainPlan.Maximal.dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hKpos, hKbound⟩ := emsw_lintegral_ell2MaxShift_sq_le
  have hK2 : (0 : ℝ) ≤ K ^ (2 : ℝ) := Real.rpow_nonneg hKpos.le 2
  have hCpos : (0 : ℝ) < 6 + 3 * K ^ (2 : ℝ) + 1 := by linarith
  refine ⟨6 + 3 * K ^ (2 : ℝ) + 1, hCpos, fun n f hf lam hlam => ?_⟩
  set σ : ℝ → ℝ≥0∞ := ell2Sigma f with hσdef
  set a : ℝ≥0∞ := ENNReal.ofReal (lam / 2) with hadef
  have hσeq : ∀ x, σ x = ENNReal.ofReal (lwtNorm f x) := fun x => ell2Sigma_eq_ofReal f x
  have hσmeas : Measurable σ := by rw [hσdef]; exact ell2Sigma_measurable hf
  have hInt_eq : (∫⁻ x, (ell2Sq f x) ^ ((1 : ℝ) / 2)) = ∫⁻ x, σ x :=
    lintegral_congr fun x => (congrFun hσdef x).symm
  have ha_pos : 0 < a := ENNReal.ofReal_pos.mpr (by linarith)
  have ha_ne : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha_inv : a⁻¹ = ENNReal.ofReal (2 / lam) := by
    rw [hadef, ← ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < lam / 2)]
    congr 1
    field_simp
  rw [hInt_eq]
  by_cases htop : ∫⁻ x, σ x = ⊤
  · have hne : ENNReal.ofReal ((6 + 3 * K ^ (2 : ℝ) + 1) / lam) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (div_pos hCpos hlam)).ne'
    rw [htop, ENNReal.mul_top hne]
    exact le_top
  · have hI : ∫⁻ x, σ x < ⊤ := lt_top_iff_ne_top.mpr htop
    have hs_int : Integrable (lwtNorm f) := by
      refine (lintegral_ofReal_ne_top_iff_integrable (lwtNorm_measurable hf).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => lwtNorm_nonneg f x)).mp ?_
      have h2 : (∫⁻ x, ENNReal.ofReal (lwtNorm f x)) = ∫⁻ x, σ x :=
        lintegral_congr fun x => (hσeq x).symm
      rw [h2]
      exact hI.ne
    have hint_abs : ∀ t, Integrable (fun y => |f t y|) := fun t =>
      hs_int.mono' (hf t).abs.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa using abs_le_lwtNorm f t y)
    have havg : ∀ p : ℤ × ℤ, p ∈ czMax σ a → lwtCellAvg (lwtNorm f) p ≤ lam := by
      intro p hp
      have h1 := czMax_avg_le ha_pos hI hp
      have h2 := ofReal_lwtCellAvg (A := lwtNorm f) (σ := σ) (p := p)
        (fun y => lwtNorm_nonneg f y) hσeq (hs_int.integrableOn)
      rw [h2] at h1
      have h3 : 2 * a = ENNReal.ofReal lam := by
        rw [hadef, show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [h3] at h1
      rwa [ENNReal.ofReal_le_ofReal_iff hlam.le] at h1
    have hae_off : ∀ᵐ y ∂volume, y ∉ lwtOm σ a → lwtNorm f y ≤ lam / 2 := by
      have hae_le : ∀ᵐ x ∂volume, σ x ≤ dyMax σ x := by
        have heq : (fun y => ENNReal.ofReal (lwtNorm f y)) = σ := funext fun y => (hσeq y).symm
        have h := ae_le_dyMax (lwtNorm f) hs_int.locallyIntegrable (fun x => lwtNorm_nonneg f x)
        filter_upwards [h] with x hx
        rw [heq] at hx
        rwa [hσeq x]
      filter_upwards [hae_le] with x hx hxnot
      have h1 : dyMax σ x ≤ a := by
        by_contra hcon
        rw [not_le] at hcon
        exact hxnot (by rw [lwtOm_eq_levelSet ha_pos hI]; exact hcon)
      have h2' : σ x ≤ a := hx.trans h1
      rw [hσeq x, hadef] at h2'
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith : (0 : ℝ) ≤ lam / 2)).mp h2'
    have hI_sq : ∫⁻ y, ell2Sq (lwtG f σ a) y ≤
        ENNReal.ofReal (lam ^ 2) * volume (lwtOm σ a) + ENNReal.ofReal (lam / 2) * ∫⁻ y, σ y :=
      lintegral_ell2Sq_lwtG_le hf hσmeas hlam hσeq hs_int hint_abs havg hae_off
    have hgood : ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ))
        ≤ ENNReal.ofReal (K ^ (2 : ℝ)) * ∫⁻ y, ell2Sq (lwtG f σ a) y :=
      hKbound n (lwtG f σ a) (fun t => lwtG_measurable hf σ a t)
    have hvolOm : volume (lwtOm σ a) ≤ ENNReal.ofReal (2 / lam) * ∫⁻ y, σ y := by
      rw [← ha_inv]
      exact volume_lwtOm_le ha_pos ha_ne
    have hlam2pos : (0 : ℝ) < lam ^ 2 := by positivity
    have hcoef1 : (ENNReal.ofReal (lam ^ 2))⁻¹ * ENNReal.ofReal (lam / 2)
        = ENNReal.ofReal (1 / (2 * lam)) := by
      rw [← ENNReal.ofReal_inv_of_pos hlam2pos,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (lam ^ 2)⁻¹)]
      congr 1
      field_simp
    have hcoef3 : ENNReal.ofReal (2 / lam) + ENNReal.ofReal (1 / (2 * lam))
        = ENNReal.ofReal (5 / (2 * lam)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      norm_num
    have hcoef2 : ENNReal.ofReal (K ^ (2 : ℝ)) * ENNReal.ofReal (5 / (2 * lam))
        = ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam)) := by
      rw [← ENNReal.ofReal_mul hK2]
      congr 1
      ring
    have hcoef4 : (3 : ℝ≥0∞) * ENNReal.ofReal (2 / lam) = ENNReal.ofReal (6 / lam) := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    have hcoef5 : ENNReal.ofReal (6 / lam) + ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam))
        = ENNReal.ofReal ((6 + 5 * K ^ (2 : ℝ) / 2) / lam) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hE1 : (ENNReal.ofReal (lam ^ 2))⁻¹ * ∫⁻ y, ell2Sq (lwtG f σ a) y
        ≤ ENNReal.ofReal (5 / (2 * lam)) * ∫⁻ y, σ y := by
      calc (ENNReal.ofReal (lam ^ 2))⁻¹ * ∫⁻ y, ell2Sq (lwtG f σ a) y
          ≤ (ENNReal.ofReal (lam ^ 2))⁻¹
              * (ENNReal.ofReal (lam ^ 2) * volume (lwtOm σ a)
                + ENNReal.ofReal (lam / 2) * ∫⁻ y, σ y) :=
              mul_le_mul_of_nonneg_left hI_sq bot_le
        _ = ((ENNReal.ofReal (lam ^ 2))⁻¹ * ENNReal.ofReal (lam ^ 2)) * volume (lwtOm σ a)
              + ((ENNReal.ofReal (lam ^ 2))⁻¹ * ENNReal.ofReal (lam / 2)) * ∫⁻ y, σ y := by
              ring
        _ = volume (lwtOm σ a) + ENNReal.ofReal (1 / (2 * lam)) * ∫⁻ y, σ y := by
              rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hlam2pos).ne'
                ENNReal.ofReal_ne_top, one_mul, hcoef1]
        _ ≤ ENNReal.ofReal (2 / lam) * (∫⁻ y, σ y)
              + ENNReal.ofReal (1 / (2 * lam)) * (∫⁻ y, σ y) := add_le_add hvolOm (le_refl _)
        _ = (ENNReal.ofReal (2 / lam) + ENNReal.ofReal (1 / (2 * lam))) * ∫⁻ y, σ y := by ring
        _ = ENNReal.ofReal (5 / (2 * lam)) * ∫⁻ y, σ y := by rw [hcoef3]
    have hmarkov : volume {x | ENNReal.ofReal (lam ^ 2)
        ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)}
        ≤ (ENNReal.ofReal (lam ^ 2))⁻¹
          * ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) := by
      have hmeas : Measurable (fun x => ∑ t : Fin n,
          (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) :=
        Finset.measurable_sum _ fun t _ =>
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
            (emsw_dyMaxShift_measurable (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ))
      have h := mul_meas_ge_le_lintegral (μ := volume) hmeas (ENNReal.ofReal (lam ^ 2))
      have h0 : ENNReal.ofReal (lam ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hlam2pos).ne'
      have ht : ENNReal.ofReal (lam ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
      calc volume {x | ENNReal.ofReal (lam ^ 2)
              ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)}
          = 1 * volume {x | ENNReal.ofReal (lam ^ 2)
              ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)} :=
              (one_mul _).symm
        _ = ((ENNReal.ofReal (lam ^ 2))⁻¹ * ENNReal.ofReal (lam ^ 2))
              * volume {x | ENNReal.ofReal (lam ^ 2)
                ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)} := by
              rw [ENNReal.inv_mul_cancel h0 ht]
        _ = (ENNReal.ofReal (lam ^ 2))⁻¹
              * (ENNReal.ofReal (lam ^ 2) * volume {x | ENNReal.ofReal (lam ^ 2)
                ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)}) := by
              ring
        _ ≤ (ENNReal.ofReal (lam ^ 2))⁻¹
              * ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) :=
              mul_le_mul_of_nonneg_left h bot_le
    have hlev : {x | ENNReal.ofReal lam
          < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ⊆ {x | ENNReal.ofReal (lam ^ 2)
          ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have h1 : ENNReal.ofReal lam ^ (2 : ℝ)
          < ((∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
        ENNReal.rpow_lt_rpow hx (by norm_num : (0 : ℝ) < 2)
      rw [← ENNReal.rpow_mul, show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one] at h1
      have h2 : ENNReal.ofReal lam ^ (2 : ℝ) = ENNReal.ofReal (lam ^ 2) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
          ← ENNReal.ofReal_pow hlam.le]
      rw [h2] at h1
      exact h1.le
    have hbound_good : volume {x | ENNReal.ofReal lam
          < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ≤ ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam)) * ∫⁻ y, σ y := by
      refine (measure_mono hlev).trans ?_
      refine hmarkov.trans ?_
      calc (ENNReal.ofReal (lam ^ 2))⁻¹
            * ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ))
          ≤ (ENNReal.ofReal (lam ^ 2))⁻¹
              * (ENNReal.ofReal (K ^ (2 : ℝ)) * ∫⁻ y, ell2Sq (lwtG f σ a) y) :=
              mul_le_mul_of_nonneg_left hgood bot_le
        _ = (ENNReal.ofReal (lam ^ 2))⁻¹ * ENNReal.ofReal (K ^ (2 : ℝ))
              * ∫⁻ y, ell2Sq (lwtG f σ a) y := by ring
        _ ≤ ENNReal.ofReal (K ^ (2 : ℝ))
              * (ENNReal.ofReal (5 / (2 * lam)) * ∫⁻ y, σ y) := by
              rw [mul_comm ((ENNReal.ofReal (lam ^ 2))⁻¹) (ENNReal.ofReal (K ^ (2 : ℝ))), mul_assoc]
              exact mul_le_mul_of_nonneg_left hE1 bot_le
        _ = ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam)) * ∫⁻ y, σ y := by
              rw [show ENNReal.ofReal (K ^ (2 : ℝ)) * (ENNReal.ofReal (5 / (2 * lam)) * (∫⁻ y, σ y))
                  = (ENNReal.ofReal (K ^ (2 : ℝ)) * ENNReal.ofReal (5 / (2 * lam))) * (∫⁻ y, σ y)
                  from by ring, hcoef2]
    have hvol_star : volume (emswStar σ a) ≤ ENNReal.ofReal (6 / lam) * (∫⁻ y, σ y) := by
      have h1 := volume_emswStar_le (σ := σ) (a := a) ha_pos ha_ne
      rw [ha_inv] at h1
      have h2 : (3 : ℝ≥0∞) * (ENNReal.ofReal (2 / lam) * (∫⁻ y, σ y))
          = ENNReal.ofReal (6 / lam) * (∫⁻ y, σ y) := by
        rw [← mul_assoc, hcoef4]
      exact h1.trans (le_of_eq h2)
    have hoff : ∀ x, x ∉ emswStar σ a →
        (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ))
          = (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) := by
      intro x hx'
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [emsw_dyMaxShift_lwtG_eq hf hint_abs t hx']
    have hsub_off : ({x | ENNReal.ofReal lam
          < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ∩ (emswStar σ a)ᶜ)
        ⊆ {x | ENNReal.ofReal lam
          < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖lwtG f σ a t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)} := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      simp only [Set.mem_setOf_eq] at hx1 ⊢
      rw [hoff x hx2] at hx1
      exact hx1
    have hsplit : volume {x | ENNReal.ofReal lam
          < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ≤ volume (emswStar σ a)
          + volume ({x | ENNReal.ofReal lam
            < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
            ∩ (emswStar σ a)ᶜ) := by
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro x hx
      by_cases hxs : x ∈ emswStar σ a
      · exact Or.inl hxs
      · exact Or.inr ⟨hx, hxs⟩
    have hfinal_al : ENNReal.ofReal (6 / lam) * (∫⁻ y, σ y)
        + ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam)) * (∫⁻ y, σ y)
        = ENNReal.ofReal ((6 + 5 * K ^ (2 : ℝ) / 2) / lam) * (∫⁻ y, σ y) := by
      have h1 : ENNReal.ofReal (6 / lam) * (∫⁻ y, σ y)
          + ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam)) * (∫⁻ y, σ y)
          = (ENNReal.ofReal (6 / lam)
              + ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam))) * (∫⁻ y, σ y) := by ring
      rw [h1, hcoef5]
    have hmono_const : ENNReal.ofReal ((6 + 5 * K ^ (2 : ℝ) / 2) / lam)
        ≤ ENNReal.ofReal ((6 + 3 * K ^ (2 : ℝ) + 1) / lam) := by
      refine ENNReal.ofReal_le_ofReal ?_
      refine div_le_div_of_nonneg_right ?_ hlam.le
      linarith
    calc volume {x | ENNReal.ofReal lam
            < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ≤ volume (emswStar σ a)
            + volume ({x | ENNReal.ofReal lam
              < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
              ∩ (emswStar σ a)ᶜ) := hsplit
      _ ≤ ENNReal.ofReal (6 / lam) * (∫⁻ y, σ y)
            + ENNReal.ofReal (5 * K ^ (2 : ℝ) / (2 * lam)) * (∫⁻ y, σ y) :=
          add_le_add hvol_star ((measure_mono hsub_off).trans hbound_good)
      _ = ENNReal.ofReal ((6 + 5 * K ^ (2 : ℝ) / 2) / lam) * ∫⁻ y, σ y := hfinal_al
      _ ≤ ENNReal.ofReal ((6 + 3 * K ^ (2 : ℝ) + 1) / lam) * ∫⁻ y, σ y :=
          mul_le_mul_of_nonneg_right hmono_const bot_le

end Work.BourgainPlan.Maximal
