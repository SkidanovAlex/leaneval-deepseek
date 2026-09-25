import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type

/-!
# The dyadic maximal function on `ℝ`

First brick of the **Fefferman--Stein vector-valued maximal inequality**

`‖ (Σ_t (M f_t)^2)^{1/2} ‖_{L^p} ≤ C_p ‖ (Σ_t |f_t|^2)^{1/2} ‖_{L^p}   (1 < p < ∞)`,

which Mirek--Stein--Trojan cite from Stein's *Harmonic Analysis* in the proof of their Theorem 17
(the vector-valued maximal estimate for the continuous Radon operators) — the input `(eq:54)` of
their §4 maximal argument, hence a component of the `1 < p < 2` frontier of Bourgain's theorem in
this project (see `WINDOW_WEAK_TYPE_STATUS_S9.md`).

This file sets up the dyadic cells, the dyadic maximal function `dyMax`, the elementary comparison
with the corpus's centred maximal function `hlMax`, and the scalar theory of `dyMax` (transferred
from the corpus's `Commons.Analysis.Maximal.real_maximal_{weak,strong}_type`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax)

/-- The dyadic cell `[k·2^n, (k+1)·2^n)` of level `n ∈ ℤ` and index `k ∈ ℤ`. -/
def dyCell (n k : ℤ) : Set ℝ := Set.Ico ((k : ℝ) * (2 : ℝ) ^ n) (((k : ℝ) + 1) * (2 : ℝ) ^ n)

/-- The index of the dyadic cell of level `n` containing `x`. -/
noncomputable def dyIdx (n : ℤ) (x : ℝ) : ℤ := ⌊x / (2 : ℝ) ^ n⌋

lemma dyCell_measurable (n k : ℤ) : MeasurableSet (dyCell n k) := measurableSet_Ico

lemma zpow_two_pos (n : ℤ) : (0 : ℝ) < (2 : ℝ) ^ n := zpow_pos (by norm_num) n

/-- The length of a dyadic cell is `2^n`. -/
lemma dyCell_len (n k : ℤ) :
    ((k : ℝ) + 1) * (2 : ℝ) ^ n - (k : ℝ) * (2 : ℝ) ^ n = (2 : ℝ) ^ n := by ring

lemma dyCell_nonempty (n k : ℤ) : (dyCell n k).Nonempty :=
  ⟨(k : ℝ) * (2 : ℝ) ^ n, le_rfl, by have := zpow_two_pos n; linarith [dyCell_len n k]⟩

lemma dyIdx_mem (n : ℤ) (x : ℝ) : x ∈ dyCell n (dyIdx n x) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := zpow_two_pos n
  have h1 : ((dyIdx n x : ℝ)) ≤ x / (2 : ℝ) ^ n := by
    rw [dyIdx]; exact Int.floor_le _
  have h2 : x / (2 : ℝ) ^ n < (dyIdx n x : ℝ) + 1 := by
    rw [dyIdx]; exact Int.lt_floor_add_one _
  constructor
  · have := (le_div_iff₀ hpos).mp h1
    simpa [mul_comm] using this
  · have := (div_lt_iff₀ hpos).mp h2
    simpa [mul_comm] using this

/-- Cells of a fixed level are disjoint. -/
lemma dyCell_disjoint {n k k' : ℤ} (h : k ≠ k') : Disjoint (dyCell n k) (dyCell n k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  wlog hle : k ≤ k' generalizing k k' with H
  · exact H h.symm hx' hx (not_le.mp hle).le
  have hlt : k < k' := lt_of_le_of_ne hle h
  have hstep : ((k : ℝ) + 1) ≤ (k' : ℝ) := by
    have : k + 1 ≤ k' := hlt
    exact_mod_cast this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := zpow_two_pos n
  have h1 : x < ((k : ℝ) + 1) * (2 : ℝ) ^ n := hx.2
  have h2 : (k' : ℝ) * (2 : ℝ) ^ n ≤ x := hx'.1
  have hmono : ((k : ℝ) + 1) * (2 : ℝ) ^ n ≤ (k' : ℝ) * (2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hstep hpos.le
  linarith

/-- Cells of a fixed level that meet are equal. -/
lemma dyCell_same_level_eq {n : ℤ} {x y : ℝ}
    (h : (dyCell n (dyIdx n x) ∩ dyCell n (dyIdx n y)).Nonempty) :
    dyIdx n x = dyIdx n y := by
  by_contra hne
  obtain ⟨w, hw⟩ := h
  exact Set.disjoint_left.mp (dyCell_disjoint hne) hw.1 hw.2

lemma dyCell_lintegral_eq_Icc (φ : ℝ → ℝ≥0∞) (n k : ℤ) :
    ∫⁻ y in dyCell n k, φ y
      = ∫⁻ y in Set.Icc ((k : ℝ) * (2 : ℝ) ^ n) (((k : ℝ) + 1) * (2 : ℝ) ^ n), φ y := by
  set a : ℝ := (k : ℝ) * (2 : ℝ) ^ n with ha
  set b : ℝ := ((k : ℝ) + 1) * (2 : ℝ) ^ n with hb
  rw [dyCell, ha, hb, ← lintegral_indicator measurableSet_Ico,
    ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr_ae
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
    (Real.volume_singleton (a := b))] with y hy
  by_cases h1 : y ∈ Set.Ico a b
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.Ico_subset_Icc_self h1)]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : y ∈ Set.Icc a b
    · have hyb : y = b := by
        refine le_antisymm h2.2 ?_
        by_contra hcon
        exact h1 ⟨h2.1, lt_of_not_ge hcon⟩
      exact absurd hyb hy
    · rw [Set.indicator_of_notMem h2]

/-- The dyadic maximal function: the supremum of the averages of `φ` over the dyadic cells
containing `x`. -/
noncomputable def dyMax (φ : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (n : ℤ) (k : ℤ) (_ : x ∈ dyCell n k),
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) * ∫⁻ y in dyCell n k, φ y

/-- The dyadic maximal function is dominated by the centred Hardy--Littlewood maximal function. -/
theorem dyMax_le_hlMax (φ : ℝ → ℝ≥0∞) (x : ℝ) : dyMax φ x ≤ hlMax φ x := by
  unfold dyMax
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  have hxmem : (k : ℝ) * (2 : ℝ) ^ n ≤ x ∧ x ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ n :=
    ⟨hx.1, hx.2.le⟩
  have hweight : ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹)
      = ENNReal.ofReal ((((k : ℝ) + 1) * (2 : ℝ) ^ n
          - (k : ℝ) * (2 : ℝ) ^ n))⁻¹ := by
    rw [dyCell_len]
  rw [hweight, dyCell_lintegral_eq_Icc]
  exact Commons.Analysis.Maximal.hlMax_le_of_mem φ hxmem.1 hxmem.2

lemma dyMax_mono {φ ψ : ℝ → ℝ≥0∞} (h : φ ≤ ψ) (x : ℝ) : dyMax φ x ≤ dyMax ψ x := by
  unfold dyMax
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  refine le_trans (mul_le_mul_right ?_ _)
    (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))
  exact lintegral_mono h

theorem dyMax_measurable (φ : ℝ → ℝ≥0∞) : Measurable (dyMax φ) := by
  have h : dyMax φ = fun x => ⨆ (p : ℤ × ℤ), (dyCell p.1 p.2).indicator
      (fun _ => ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹) * ∫⁻ y in dyCell p.1 p.2, φ y) x := by
    funext x
    refine le_antisymm ?_ ?_
    · unfold dyMax
      refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
      refine le_iSup_of_le (n, k) ?_
      rw [Set.indicator_of_mem hx]
    · refine iSup_le fun p => ?_
      by_cases hp : x ∈ dyCell p.1 p.2
      · rw [Set.indicator_of_mem hp]
        unfold dyMax
        exact le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le hp le_rfl))
      · rw [Set.indicator_of_notMem hp]; exact bot_le
  rw [h]
  exact Measurable.iSup fun p => Measurable.indicator measurable_const (dyCell_measurable p.1 p.2)

/-- Scalar strong `(p,p)` bound for the dyadic maximal function, `p > 1`
(elementary consequence of the centred bound). -/
theorem dyMax_strong_type (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
      ∫⁻ x, (dyMax (fun y => ‖f y‖ₑ) x) ^ p ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  obtain ⟨C, hC, hb⟩ := Commons.Analysis.Maximal.real_maximal_strong_type p hp
  refine ⟨C, hC, fun f => le_trans (lintegral_mono fun x => ?_) (hb f)⟩
  exact ENNReal.rpow_le_rpow (dyMax_le_hlMax (fun y => ‖f y‖ₑ) x)
    (le_trans zero_le_one hp.le)

/-- Scalar weak `(1,1)` bound for the dyadic maximal function. -/
theorem dyMax_weak_type :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (lam : ℝ), 0 < lam →
      volume {x : ℝ | ENNReal.ofReal lam < dyMax (fun y => ‖f y‖ₑ) x}
        ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, ‖f x‖ₑ := by
  obtain ⟨C, hC, hb⟩ := Commons.Analysis.Maximal.real_maximal_weak_type
  refine ⟨C, hC, fun f lam hlam => ?_⟩
  refine le_trans (MeasureTheory.measure_mono ?_) (hb f lam hlam)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact lt_of_lt_of_le hx (dyMax_le_hlMax (fun y => ‖f y‖ₑ) x)

end Work.BourgainPlan.Maximal
