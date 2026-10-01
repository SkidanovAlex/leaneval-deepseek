import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.card_hensel_le
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.natDegree_critN_le_four
import Submission.Work.LinnikBurgess.lfSmall.transfer_three
import Submission.Work.LinnikBurgess.lfSmall.content_three_ge
import Submission.Work.LinnikBurgess.lfSmall.content_three_split
import Submission.Work.LinnikBurgess.lfSmall.capcount_three
import Submission.Work.LinnikBurgess.lfSmall.DLp_of_unc_three
import Submission.Work.LinnikBurgess.lfSmall.DLp_of_cap_three
import Submission.Work.LinnikBurgess.lfSmall.DLp_of_content_three
import Submission.Work.LinnikBurgess.lfSmall.card_lvlSet_le_three

open scoped BigOperators
open Classical

set_option maxHeartbeats 1000000

namespace Work.LinnikBurgess
namespace lfSmall

/-! ## Arithmetic of `cubeLevel 3` and `capLevel 3` -/

theorem cubeLevel_three (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by norm_num)]

theorem capLevel_three (e : ℕ) : capLevel 3 e = e - 2 * ((e + 2) / 3) := by
  rw [capLevel, cubeLevel_three]

theorem capLevel_le_cubeLevel_three (e : ℕ) : capLevel 3 e ≤ cubeLevel 3 e := by
  rw [capLevel_three, cubeLevel_three]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem capLevel_le_self_three (e : ℕ) : capLevel 3 e ≤ e := by
  rw [capLevel_three]; omega

theorem one_le_cubeLevel_three {e : ℕ} (he : 13 ≤ e) : 1 ≤ cubeLevel 3 e := by
  rw [cubeLevel_three]; omega

/-! ## Unfolding `gaussTwoRHS` -/

private lemma gaussTwoRHS_eq_sum (e : ℕ) (a b : Fin 3 → ℕ) :
    gaussTwoRHS 3 e (cubeLevel 3 e) a b
      = ∑ y ∈ suppSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2) := by
  classical
  rw [gaussTwoRHS, suppSet, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : suppPred 3 e a b y
  · rw [if_pos h]
    rw [if_pos (show UnitAt 3 y a b ∧
        3 ^ (cubeLevel 3 e + vcap 3 (e - 2 * cubeLevel 3 e) (defect2 3 e a b y).val)
          ∣ (defect1 3 e a b y).val from h)]
    simp only [bval, capLevel]
    norm_num
  · rw [if_neg h]
    rw [if_neg (show ¬ (UnitAt 3 y a b ∧
        3 ^ (cubeLevel 3 e + vcap 3 (e - 2 * cubeLevel 3 e) (defect2 3 e a b y).val)
          ∣ (defect1 3 e a b y).val) from h)]

private lemma suppSet_eq_unc_union_cap (e : ℕ) (a b : Fin 3 → ℕ) :
    suppSet 3 e a b = uncSet 3 e a b ∪ capSet 3 e a b := by
  ext y
  simp only [uncSet, capSet, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro h
    rcases lt_or_ge (nval 3 e a b y) (capLevel 3 e) with hlt | hle
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hle⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

private lemma unc_cap_disjoint (e : ℕ) (a b : Fin 3 → ℕ) :
    Disjoint (uncSet 3 e a b) (capSet 3 e a b) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  simp only [uncSet, Finset.mem_filter] at hy1
  simp only [capSet, Finset.mem_filter] at hy2
  omega

private lemma suppPred_of_mem_uncSet {e : ℕ} {a b : Fin 3 → ℕ} {y : ℕ}
    (hy : y ∈ uncSet 3 e a b) : suppPred 3 e a b y := by
  have h1 : (y ∈ Finset.range (3 ^ cubeLevel 3 e) ∧ suppPred 3 e a b y)
      ∧ nval 3 e a b y < capLevel 3 e := by
    simpa only [uncSet, suppSet, Finset.mem_filter] using hy
  exact h1.1.2

private lemma nval_lt_of_mem_uncSet {e : ℕ} {a b : Fin 3 → ℕ} {y : ℕ}
    (hy : y ∈ uncSet 3 e a b) : nval 3 e a b y < capLevel 3 e := by
  have h1 : (y ∈ Finset.range (3 ^ cubeLevel 3 e) ∧ suppPred 3 e a b y)
      ∧ nval 3 e a b y < capLevel 3 e := by
    simpa only [uncSet, suppSet, Finset.mem_filter] using hy
  exact h1.2

private lemma suppPred_of_mem_capSet {e : ℕ} {a b : Fin 3 → ℕ} {y : ℕ}
    (hy : y ∈ capSet 3 e a b) : suppPred 3 e a b y := by
  have h1 : (y ∈ Finset.range (3 ^ cubeLevel 3 e) ∧ suppPred 3 e a b y)
      ∧ capLevel 3 e ≤ nval 3 e a b y := by
    simpa only [capSet, suppSet, Finset.mem_filter] using hy
  exact h1.1.2

private lemma le_nval_of_mem_capSet {e : ℕ} {a b : Fin 3 → ℕ} {y : ℕ}
    (hy : y ∈ capSet 3 e a b) : capLevel 3 e ≤ nval 3 e a b y := by
  have h1 : (y ∈ Finset.range (3 ^ cubeLevel 3 e) ∧ suppPred 3 e a b y)
      ∧ capLevel 3 e ≤ nval 3 e a b y := by
    simpa only [capSet, suppSet, Finset.mem_filter] using hy
  exact h1.2

/-! ## Menu weights -/

private lemma menuW_unc {e s : ℕ} (he : 13 ≤ e) (hs : s < capLevel 3 e) :
    menuW 3 e s 0 = 10 ^ 6 * (3 : ℝ) ^ ((s : ℝ) / 2) := by
  have h5 : ¬ (5 ≤ 3) := by norm_num
  have he12 : ¬ (e ≤ 12) := by omega
  simp only [menuW, h5, he12, reduceIte, true_and]
  rw [if_pos (le_of_lt hs), max_eq_left (Nat.zero_le _), if_neg (ne_of_lt hs), add_zero]
  simp only [Nat.cast_ofNat]

private lemma menuW_cap {e : ℕ} (he : 13 ≤ e) :
    menuW 3 e (capLevel 3 e) 0
      = 10 ^ 6 * (3 : ℝ) ^ ((capLevel 3 e : ℝ) / 2)
        + 10 ^ 6 * (3 : ℝ) ^ ((cubeLevel 3 e : ℝ) / 2) := by
  have h5 : ¬ (5 ≤ 3) := by norm_num
  have he12 : ¬ (e ≤ 12) := by omega
  simp only [menuW, h5, he12, reduceIte, true_and]
  rw [if_pos le_rfl, max_eq_left (Nat.zero_le _), if_pos rfl]
  simp only [Nat.cast_ofNat, Nat.cast_zero, add_zero]

private lemma menuW_content {e j : ℕ} (he : 13 ≤ e) (hj : j ≠ 0) :
    10 ^ 6 * (3 : ℝ) ^ ((((cubeLevel 3 e : ℕ) : ℝ) + j) / 2)
      ≤ menuW 3 e (max (capLevel 3 e) j) j := by
  have h5 : ¬ (5 ≤ 3) := by norm_num
  have he12 : ¬ (e ≤ 12) := by omega
  simp only [menuW, h5, he12, reduceIte, true_and]
  rw [if_neg (show ¬ (j = 0 ∧ max (capLevel 3 e) j ≤ capLevel 3 e) from by
    rintro ⟨h0, -⟩; exact hj h0)]
  simp only [Nat.cast_ofNat, zero_add]
  exact le_rfl

private lemma menuW_nonneg {e s j : ℕ} (he : 13 ≤ e) : 0 ≤ menuW 3 e s j := by
  have h5 : ¬ (5 ≤ 3) := by norm_num
  have he12 : ¬ (e ≤ 12) := by omega
  simp only [menuW, h5, he12, reduceIte]
  split_ifs <;> positivity

private lemma ite_nonneg (P : Prop) [Decidable P] (c : ℝ) (h : 0 ≤ c) :
    0 ≤ (if P then c else 0) := by
  split <;> simp [h]

/-! ## The support sum -/

private lemma unc_sum_le {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (hN : critN a b ≠ 0)
    (hdeg : (critN a b).natDegree ≤ 4) (hbt : SuppTransfer 3 e a b) :
    ∑ y ∈ uncSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2)
      ≤ ∑ s ∈ Finset.range (capLevel 3 e),
          10 ^ 6 * (3 : ℝ) ^ ((s : ℝ) / 2) * (if DLp 3 s a b then 1 else 0) := by
  classical
  have hbv : ∀ y ∈ uncSet 3 e a b, bval 3 e a b y = nval 3 e a b y := by
    intro y hy
    rw [(hbt y (suppPred_of_mem_uncSet hy)).1,
      min_eq_left (le_of_lt (nval_lt_of_mem_uncSet hy))]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hbv y hy])]
  have hmap : ∀ y ∈ uncSet 3 e a b, nval 3 e a b y ∈ Finset.range (capLevel 3 e) :=
    fun y hy => Finset.mem_range.mpr (Finset.mem_filter.mp hy).2
  rw [← Finset.sum_fiberwise_of_maps_to hmap (f := fun y => (3 : ℝ) ^ ((nval 3 e a b y : ℝ) / 2))]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsT : s < capLevel 3 e := Finset.mem_range.mp hs
  rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hDL : DLp 3 s a b
  · rw [if_pos hDL]
    have hle : ((uncSet 3 e a b).filter (fun y => nval 3 e a b y = s)).card ≤ 4 := by
      refine le_trans (Finset.card_le_card ?_)
        (card_lvlSet_le_three he a b hN hdeg hbt hsT)
      intro y hy
      obtain ⟨hyu, hys⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyu).1, hys⟩
    calc ((uncSet 3 e a b).filter (fun y => nval 3 e a b y = s)).card
            * (3 : ℝ) ^ ((s : ℝ) / 2)
        ≤ 4 * (3 : ℝ) ^ ((s : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (Real.rpow_nonneg (by norm_num) _)
      _ ≤ 10 ^ 6 * (3 : ℝ) ^ ((s : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 10 ^ 6)
            (Real.rpow_nonneg (by norm_num) _)
      _ = 10 ^ 6 * (3 : ℝ) ^ ((s : ℝ) / 2) * 1 := (mul_one _).symm
  · rw [if_neg hDL]
    have hempty : (uncSet 3 e a b).filter (fun y => nval 3 e a b y = s) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hyu hys
      refine hDL ?_
      rw [← hys]
      exact DLp_of_unc_three he a b (suppPred_of_mem_uncSet hyu) hbt (nval_lt_of_mem_uncSet hyu)
    rw [hempty]
    simp

/-- The capped part of the support contributes `card · 3^(T/2)`. -/
private lemma cap_sum_eq (e : ℕ) (a b : Fin 3 → ℕ) (hbt : SuppTransfer 3 e a b) :
    ∑ y ∈ capSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2)
      = ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) := by
  classical
  have hbv : ∀ y ∈ capSet 3 e a b, bval 3 e a b y = capLevel 3 e := by
    intro y hy
    rw [(hbt y (suppPred_of_mem_capSet hy)).1, min_eq_right (le_nval_of_mem_capSet hy)]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hbv y hy]), Finset.sum_const, nsmul_eq_mul]

/-! ### Row bounds for `localFactor` -/

private noncomputable def LFterm (e : ℕ) (a b : Fin 3 → ℕ) (s j : ℕ) : ℝ :=
  menuW 3 e s j * (if DLp 3 s a b ∧ 3 ^ j ∣ contAB a b then (1:ℝ) else 0)

private lemma LFterm_nonneg {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (s j : ℕ) :
    0 ≤ LFterm e a b s j :=
  mul_nonneg (menuW_nonneg he) (ite_nonneg (DLp 3 s a b ∧ 3 ^ j ∣ contAB a b) 1 (by norm_num))

private lemma localFactor_eq_rows (e : ℕ) (a b : Fin 3 → ℕ) :
    localFactor 3 e a b = ∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1), LFterm e a b s j := by
  rw [localFactor]; rfl

/-- `localFactor` dominates the `j = 0` row up to `T = capLevel 3 e`. -/
private lemma localFactor_ge_row_succ {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    (∑ s ∈ Finset.range (capLevel 3 e + 1), LFterm e a b s 0) ≤ localFactor 3 e a b := by
  classical
  rw [localFactor_eq_rows]
  refine le_trans (Finset.sum_le_sum (f := fun s => LFterm e a b s 0)
    (g := fun s => ∑ j ∈ Finset.range (e + 1), LFterm e a b s j) (fun s _ => ?_)) ?_
  · exact Finset.single_le_sum (f := fun j => LFterm e a b s j)
      (fun j _ => LFterm_nonneg he a b s j) (a := 0)
      (Finset.mem_range.mpr (by omega : 0 < e + 1))
  · refine Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun s => ∑ j ∈ Finset.range (e + 1), LFterm e a b s j) ?_ ?_
    · intro s hs
      have hs' := Finset.mem_range.mp hs
      have hT := capLevel_le_self_three e
      exact Finset.mem_range.mpr (by omega)
    · intro s _ _
      exact Finset.sum_nonneg (fun j _ => LFterm_nonneg he a b s j)

/-- `localFactor` dominates the `j = 0` row below `T` plus the single summand at `(max T j₀, j₀)`. -/
private lemma localFactor_ge_row_and_content {e j₀ : ℕ} (he : 13 ≤ e)
    (a b : Fin 3 → ℕ) (hj₀ : j₀ ≠ 0) (hj₀r : j₀ ∈ Finset.range (e + 1)) :
    (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0)
      + LFterm e a b (max (capLevel 3 e) j₀) j₀ ≤ localFactor 3 e a b := by
  classical
  set s₀ := max (capLevel 3 e) j₀ with hs₀def
  have hs₀r : s₀ ∈ Finset.range (e + 2) := by
    rw [Finset.mem_range, hs₀def]
    have h1 : capLevel 3 e ≤ e := capLevel_le_self_three e
    have h2 : j₀ ≤ e := by have := Finset.mem_range.mp hj₀r; omega
    have h3 : max (capLevel 3 e) j₀ ≤ e := max_le h1 h2
    omega
  have hnotmem : s₀ ∉ Finset.range (capLevel 3 e) := by
    rw [Finset.mem_range, hs₀def]
    have : capLevel 3 e ≤ max (capLevel 3 e) j₀ := le_max_left _ _
    have hj₀pos : 0 < j₀ := Nat.pos_of_ne_zero hj₀
    omega
  have hrow0 : ∀ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0
      ≤ ∑ j ∈ Finset.range (e + 1), LFterm e a b s j :=
    fun s _ => Finset.single_le_sum (f := fun j => LFterm e a b s j)
      (fun j _ => LFterm_nonneg he a b s j) (a := 0) (Finset.mem_range.mpr (by omega : 0 < e + 1))
  have hsingle : LFterm e a b s₀ j₀ ≤ ∑ j ∈ Finset.range (e + 1), LFterm e a b s₀ j :=
    Finset.single_le_sum (f := fun j => LFterm e a b s₀ j)
      (fun j _ => LFterm_nonneg he a b s₀ j) (a := j₀) hj₀r
  have hRHS : localFactor 3 e a b
      = (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1), LFterm e a b s j) :=
    localFactor_eq_rows e a b
  rw [hRHS]
  have hsplit : (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1), LFterm e a b s j)
      = (∑ s ∈ (Finset.range (e + 2)).erase s₀, ∑ j ∈ Finset.range (e + 1), LFterm e a b s j)
        + ∑ j ∈ Finset.range (e + 1), LFterm e a b s₀ j :=
    (Finset.sum_erase_add _ _ hs₀r).symm
  rw [hsplit]
  refine add_le_add ?_ hsingle
  refine le_trans (Finset.sum_le_sum hrow0) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (f := fun s => ∑ j ∈ Finset.range (e + 1), LFterm e a b s j) ?_ ?_
  · intro s hs
    have hs' := Finset.mem_range.mp hs
    have hs0 : capLevel 3 e ≤ s₀ := by rw [hs₀def]; exact le_max_left _ _
    have h1 : capLevel 3 e ≤ e := capLevel_le_self_three e
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  · intro s _ _
    exact Finset.sum_nonneg (fun j _ => LFterm_nonneg he a b s j)


private lemma capSet_card_le (e : ℕ) (a b : Fin 3 → ℕ) :
    (capSet 3 e a b).card ≤ 3 ^ cubeLevel 3 e := by
  classical
  have hsub : capSet 3 e a b ⊆ Finset.range (3 ^ cubeLevel 3 e) := by
    intro y hy
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
  calc (capSet 3 e a b).card ≤ (Finset.range (3 ^ cubeLevel 3 e)).card :=
        Finset.card_le_card hsub
    _ = 3 ^ cubeLevel 3 e := Finset.card_range _

private lemma rpow_three_mono {x y : ℝ} (h : x ≤ y) :
    (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) h

private lemma rpow_three_nn (x : ℝ) : (0:ℝ) ≤ (3 : ℝ) ^ x :=
  Real.rpow_nonneg (by norm_num) x

/-- A single summand of a row is dominated by the whole row. -/
private lemma LFterm_le_row {e s j : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hjr : j ∈ Finset.range (e + 1)) :
    LFterm e a b s j ≤ ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j' :=
  Finset.single_le_sum (f := fun j' => LFterm e a b s j') (fun j' _ => LFterm_nonneg he a b s j')
    (a := j) hjr

/-- Two distinct summands of a row are dominated by the whole row. -/
private lemma LFterm_pair_le_row {e s j₀ : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hj₀ : j₀ ≠ 0) (hj₀r : j₀ ∈ Finset.range (e + 1)) :
    LFterm e a b s 0 + LFterm e a b s j₀ ≤ ∑ j ∈ Finset.range (e + 1), LFterm e a b s j := by
  have h0 : (0 : ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_pair (f := fun j => LFterm e a b s j) (Ne.symm hj₀)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => LFterm e a b s j) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact hj₀r
  · intro x _ _; exact LFterm_nonneg he a b s x

/-- `localFactor` dominates the block of rows `s ≤ T`. -/
private lemma localFactor_ge_rowblock {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    (∑ s ∈ Finset.range (capLevel 3 e + 1), ∑ j ∈ Finset.range (e + 1), LFterm e a b s j)
      ≤ localFactor 3 e a b := by
  classical
  rw [localFactor_eq_rows]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun s => ∑ j ∈ Finset.range (e + 1), LFterm e a b s j) ?_ ?_
  · intro s hs
    have hs' := Finset.mem_range.mp hs
    have h1 : capLevel 3 e ≤ e := capLevel_le_self_three e
    exact Finset.mem_range.mpr (by omega)
  · intro s _ _; exact Finset.sum_nonneg (fun j _ => LFterm_nonneg he a b s j)

/-- `localFactor` dominates the block of rows `s ≤ T` together with the row `j₀ > T`. -/
private lemma localFactor_ge_rowblock_and_row {e j₀ : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hj₀r : j₀ ∈ Finset.range (e + 1)) (hj₀T : capLevel 3 e < j₀) :
    (∑ s ∈ Finset.range (capLevel 3 e + 1), ∑ j ∈ Finset.range (e + 1), LFterm e a b s j)
      + (∑ j ∈ Finset.range (e + 1), LFterm e a b j₀ j) ≤ localFactor 3 e a b := by
  classical
  rw [localFactor_eq_rows]
  have hj₀r' : j₀ ∈ Finset.range (e + 2) := by
    rw [Finset.mem_range]; have := Finset.mem_range.mp hj₀r; omega
  rw [← Finset.sum_erase_add _ _ hj₀r']
  refine add_le_add ?_ (le_refl _)
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun s => ∑ j ∈ Finset.range (e + 1), LFterm e a b s j) ?_ ?_
  · intro s hs
    have hs' := Finset.mem_range.mp hs
    have h1 : capLevel 3 e ≤ e := capLevel_le_self_three e
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  · intro s _ _; exact Finset.sum_nonneg (fun j _ => LFterm_nonneg he a b s j)

/-- The capped part of the support: `card · 3^(T/2)` is dominated by the `(T,0)` term plus the
content term with exponent `min J e` (the `p = 3` case of `card_capSet_le_content`, with the trivial
bound `card ≤ 3^m` covering a very large content). -/
private lemma cap_card_le {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) (hbt : SuppTransfer 3 e a b) :
    ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
      ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
        + 10 ^ 6 * (3 : ℝ) ^ ((((cubeLevel 3 e
            + min (padicValNat 3 (contAB a b)) e) : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨hdeg2, hcont⟩ := critN_ne_zero_of_unique a b i hi
  have hdeg : (critN a b).natDegree ≤ 4 := natDegree_critN_le_four a b
  have h3m : 3 * cubeLevel 3 e ≤ e + 2 := by
    rw [cubeLevel_three]; exact Nat.mul_div_le _ _
  have htriv : ((capSet 3 e a b).card : ℝ) ≤ (3 : ℝ) ^ ((cubeLevel 3 e : ℝ)) := by
    have h1 : (capSet 3 e a b).card ≤ 3 ^ cubeLevel 3 e := capSet_card_le e a b
    calc ((capSet 3 e a b).card : ℝ) ≤ ((3 ^ cubeLevel 3 e : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (3 : ℝ) ^ (((cubeLevel 3 e : ℕ)) : ℝ) := by
            rw [Real.rpow_natCast]; push_cast; ring
      _ = (3 : ℝ) ^ ((cubeLevel 3 e : ℝ)) := rfl
  by_cases h3 : (3 : ℕ) ∣ contAB a b
  · set J := padicValNat 3 (contAB a b) with hJdef
    have hJ1 : 1 ≤ J := one_le_padicValNat_of_dvd hcont h3
    have hJdiv : (3 ^ J : ℕ) ∣ contAB a b := (padicValNat_dvd_iff_le hcont).mpr le_rfl
    have hJndiv : ¬ ((3 ^ (J + 1) : ℕ) ∣ contAB a b) := pow_succ_padicValNat_not_dvd hcont
    obtain ⟨h, hh1, hhJ, hcoeff, hhmax⟩ := content_three_split i hi hJ1 hJdiv hJndiv
    have hcard := cap_count_content_three (J := J) he a b hdeg2 hdeg hcoeff hhmax hbt hh1 hhJ hJdiv hJndiv
    have hcardR : ((capSet 3 e a b).card : ℝ)
        ≤ 10 ^ 3 * (3 : ℝ) ^ (((max 0 (cubeLevel 3 e
            - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ)) := by
      exact_mod_cast hcard
    by_cases hJe : J ≤ e
    · rw [show min (padicValNat 3 (contAB a b)) e = J from by
        rw [← hJdef]; exact min_eq_left hJe]
      have hdiv : cubeLevel 3 e + capLevel 3 e - J - 1
          ≤ 2 * ((cubeLevel 3 e + capLevel 3 e - J - 1) / 2) + 1 := by
        have h1 := Nat.div_add_mod (cubeLevel 3 e + capLevel 3 e - J - 1) 2
        have h2 := Nat.mod_lt (cubeLevel 3 e + capLevel 3 e - J - 1) (by norm_num : 0 < 2)
        omega
      have hXnat : 2 * (max 0 (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2))
          + capLevel 3 e ≤ cubeLevel 3 e + J + 2 := by
        set d := (cubeLevel 3 e + capLevel 3 e - J - 1) / 2 with hddef
        set X := max 0 (cubeLevel 3 e - d) with hXdef
        have hcases : X = 0 ∨ X = cubeLevel 3 e - d := by
          rcases lt_or_ge 0 (cubeLevel 3 e - d) with h | h
          · exact Or.inr (by rw [hXdef]; exact max_eq_right (le_of_lt h))
          · exact Or.inl (by rw [hXdef]; exact max_eq_left h)
        have hd2 : cubeLevel 3 e + capLevel 3 e - J - 1 ≤ 2 * d + 1 := by
          rw [hddef]; exact hdiv
        have hle := capLevel_le_cubeLevel_three e
        rcases hcases with h0 | hpos
        · rw [h0]; omega
        · rw [hpos]; omega
      have hXnatR : (2 : ℝ) * ((max 0 (cubeLevel 3 e
            - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ) + ((capLevel 3 e : ℕ) : ℝ)
          ≤ (((cubeLevel 3 e + J + 2 : ℕ)) : ℝ) := by exact_mod_cast hXnat
      have hexp : ((max 0 (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ)
          + ((capLevel 3 e : ℕ) : ℝ) / 2 ≤ (((cubeLevel 3 e + J) : ℕ) : ℝ) / 2 + 1 := by
        push_cast at hXnatR ⊢
        linarith
      have hnn1 : (0:ℝ) ≤ (3 : ℝ) ^ (((max 0 (cubeLevel 3 e
          - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ)) := rpow_three_nn _
      have hnn2 : (0:ℝ) ≤ (3 : ℝ) ^ ((((cubeLevel 3 e + J) : ℕ) : ℝ) / 2) := rpow_three_nn _
      calc ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
          ≤ (10 ^ 3 * (3 : ℝ) ^ (((max 0 (cubeLevel 3 e
              - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ)))
            * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hcardR (rpow_three_nn _)
        _ = 10 ^ 3 * ((3 : ℝ) ^ (((max 0 (cubeLevel 3 e
              - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ))
            * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)) := by ring
        _ = 10 ^ 3 * (3 : ℝ) ^ (((max 0 (cubeLevel 3 e
              - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) : ℕ) : ℝ)
            + ((capLevel 3 e : ℕ) : ℝ) / 2) := by
            rw [Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        _ ≤ 10 ^ 3 * (3 : ℝ) ^ ((((cubeLevel 3 e + J) : ℕ) : ℝ) / 2 + 1) :=
            mul_le_mul_of_nonneg_left (rpow_three_mono hexp) (by norm_num)
        _ = (10 ^ 3 * 3) * (3 : ℝ) ^ ((((cubeLevel 3 e + J) : ℕ) : ℝ) / 2) := by
            rw [Real.rpow_add (by norm_num : (0:ℝ) < 3), Real.rpow_one]
            ring
        _ ≤ 10 ^ 6 * (3 : ℝ) ^ ((((cubeLevel 3 e + J) : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (by norm_num : (10:ℝ) ^ 3 * 3 ≤ 10 ^ 6) hnn2
        _ ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
            + 10 ^ 6 * (3 : ℝ) ^ ((((cubeLevel 3 e + J) : ℕ) : ℝ) / 2) := by
            have h1 : (0:ℝ) ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) :=
              mul_nonneg (by norm_num) (rpow_three_nn _)
            linarith
    · rw [show min (padicValNat 3 (contAB a b)) e = e from by
          rw [← hJdef]; exact min_eq_right (le_of_lt (not_le.mp hJe))]
      have hc2 : 2 ≤ cubeLevel 3 e := by rw [cubeLevel_three]; omega
      have hme : cubeLevel 3 e + capLevel 3 e ≤ e := by
        rw [capLevel_three]; omega
      have hmeR : ((cubeLevel 3 e + capLevel 3 e : ℕ) : ℝ) ≤ ((e : ℕ) : ℝ) := by exact_mod_cast hme
      have hexp2 : ((cubeLevel 3 e : ℕ) : ℝ) + ((capLevel 3 e : ℕ) : ℝ) / 2
          ≤ ((((cubeLevel 3 e + e) : ℕ)) : ℝ) / 2 := by
        push_cast at hmeR ⊢
        linarith
      have hnn : (0:ℝ) ≤ (3 : ℝ) ^ ((((cubeLevel 3 e + e) : ℕ) : ℝ) / 2) := rpow_three_nn _
      calc ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
          ≤ (3 : ℝ) ^ ((cubeLevel 3 e : ℝ)) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right htriv (rpow_three_nn _)
        _ = (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) + ((capLevel 3 e : ℕ) : ℝ) / 2) := by
            rw [Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        _ ≤ (3 : ℝ) ^ ((((cubeLevel 3 e + e) : ℕ) : ℝ) / 2) := rpow_three_mono hexp2
        _ ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
            + 10 ^ 6 * (3 : ℝ) ^ ((((cubeLevel 3 e + e) : ℕ) : ℝ) / 2) := by
            have h1 : (0:ℝ) ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) :=
              mul_nonneg (by norm_num) (rpow_three_nn _)
            linarith
  · have hcard := cap_count_noncontent_three he a b hdeg2 hdeg h3 hbt
    have hcardR : ((capSet 3 e a b).card : ℝ) ≤ 100 := by exact_mod_cast hcard
    have hJ0 : min (padicValNat 3 (contAB a b)) e = 0 := by
      have h0 : padicValNat 3 (contAB a b) = 0 := by
        by_contra hne
        exact h3 ((padicValNat_dvd_iff_le hcont).mpr (Nat.pos_of_ne_zero hne))
      rw [h0]; exact min_eq_left (Nat.zero_le _)
    rw [hJ0]
    simp only [Nat.add_zero]
    calc ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
        ≤ 100 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcardR (rpow_three_nn _)
      _ ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (rpow_three_nn _)
      _ ≤ 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
          + 10 ^ 6 * (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2) := by
          exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (rpow_three_nn _))

/-- `Linnik` (Burgess route): the capped stationary-phase sum at `p = 3` is dominated by the local
factor. -/
theorem counting_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    gaussTwoRHS 3 e (cubeLevel 3 e) a b ≤ localFactor 3 e a b := by
  classical
  obtain ⟨hdeg2, hcont⟩ := critN_ne_zero_of_unique a b i hi
  have hdeg : (critN a b).natDegree ≤ 4 := natDegree_critN_le_four a b
  have hN : critN a b ≠ 0 := by
    intro h0; rw [h0] at hdeg2; simp at hdeg2
  have hbt : SuppTransfer 3 e a b := transfer_three (by omega) a b
  rw [gaussTwoRHS_eq_sum e a b, suppSet_eq_unc_union_cap e a b,
    Finset.sum_union (unc_cap_disjoint e a b)]
  have hunc : (∑ y ∈ uncSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2))
      ≤ ∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0 := by
    refine le_trans (unc_sum_le he a b hN hdeg hbt) ?_
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hsT : s < capLevel 3 e := Finset.mem_range.mp hs
    rw [LFterm, menuW_unc he hsT]
    simp only [pow_zero, one_dvd, and_true]
    exact le_rfl
  have hrow_le : (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0) ≤ localFactor 3 e a b := by
    refine le_trans ?_ (localFactor_ge_row_succ he a b)
    refine Finset.sum_le_sum_of_subset_of_nonneg (f := fun s => LFterm e a b s 0) ?_ ?_
    · intro s hs; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hs; omega)
    · intro s _ _; exact LFterm_nonneg he a b s 0
  rcases eq_or_ne (capSet 3 e a b) ∅ with h0 | hne
  · rw [h0] at *
    simp only [Finset.sum_empty, add_zero]
    exact le_trans hunc hrow_le
  · obtain ⟨y0, hy0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hDLT : DLp 3 (capLevel 3 e) a b :=
      DLp_of_cap_three he a b (suppPred_of_mem_capSet hy0) hbt (le_nval_of_mem_capSet hy0)
    have hunit0 : UnitAt 3 y0 a b := (suppPred_of_mem_capSet hy0).1
    set J := padicValNat 3 (contAB a b) with hJdef
    set j := min J e with hjdef
    have hjr : j ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by
      have h1 : j ≤ e := min_le_right _ _
      omega)
    have hjn : (3 ^ j : ℕ) ∣ contAB a b := by
      have h1 : j ≤ J := min_le_left _ _
      exact dvd_trans (Nat.pow_dvd_pow 3 h1) ((padicValNat_dvd_iff_le hcont).mpr le_rfl)
    have hDLj : DLp 3 (max (capLevel 3 e) j) a b := by
      by_cases hle : j ≤ capLevel 3 e
      · rw [max_eq_left hle]; exact hDLT
      · rw [max_eq_right (le_of_lt (not_le.mp hle))]
        have hJ1 : 1 ≤ J := by
          by_contra hcon
          push_neg at hcon
          have hJ0 : J = 0 := by omega
          rw [hJ0] at hjdef
          have hj0 : j = 0 := by omega
          omega
        have hJdiv : (3 ^ J : ℕ) ∣ contAB a b := (padicValNat_dvd_iff_le hcont).mpr le_rfl
        have hJndiv : ¬ ((3 ^ (J + 1) : ℕ) ∣ contAB a b) := pow_succ_padicValNat_not_dvd hcont
        obtain ⟨h, hh1, hhJ, hcoeff, hhmax⟩ := content_three_split i hi hJ1 hJdiv hJndiv
        have hge : J ≤ h := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨n, hn⟩ := hhmax
          exact hn (dvd_trans (by exact_mod_cast Nat.pow_dvd_pow 3 hcon)
            (content_three_ge i hi hJdiv n))
        exact DLp_of_content_three (e := e) a b hunit0 hcoeff
          (by have : j ≤ J := min_le_left _ _; omega)
    have hLFT : 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
        ≤ LFterm e a b (capLevel 3 e) 0 := by
      rw [LFterm, menuW_cap he, if_pos ⟨hDLT, by simp⟩, mul_one]
      linarith [rpow_three_nn (((cubeLevel 3 e : ℕ) : ℝ) / 2)]
    have hLFT' : 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2) + 10 ^ 6
        ≤ LFterm e a b (capLevel 3 e) 0 := by
      rw [LFterm, menuW_cap he, if_pos ⟨hDLT, by simp⟩, mul_one]
      have h1 : (1:ℝ) ≤ (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2) := by
        calc (1:ℝ) = (3 : ℝ) ^ (0:ℝ) := by simp
          _ ≤ (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2) :=
              rpow_three_mono (by positivity)
      linarith
    have hLFj : 10 ^ 6 * (3 : ℝ) ^ ((((cubeLevel 3 e + j) : ℕ) : ℝ) / 2)
        ≤ LFterm e a b (max (capLevel 3 e) j) j := by
      rw [LFterm]
      by_cases hj0 : j = 0
      · rw [hj0]
        rw [max_eq_left (Nat.zero_le _ : (0:ℕ) ≤ capLevel 3 e), menuW_cap he,
          if_pos ⟨hDLT, by simp⟩, mul_one]
        have h1 : (1:ℝ) ≤ (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2) := by
          calc (1:ℝ) = (3 : ℝ) ^ (0:ℝ) := by simp
            _ ≤ (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2) := rpow_three_mono (by positivity)
        simp only [Nat.add_zero]
        exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (rpow_three_nn _))
      · rw [if_pos ⟨hDLj, hjn⟩, mul_one]
        simpa only [Nat.cast_add] using menuW_content he hj0
    have hcapsum := cap_card_le he a b i hi hbt
    rw [cap_sum_eq e a b hbt] at *
    rw [← hJdef, ← hjdef] at hcapsum
    by_cases hj0 : j = 0
    · rw [hj0] at hcapsum
      simp only [Nat.add_zero] at hcapsum
      calc (∑ y ∈ uncSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2))
            + ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
          ≤ (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0)
            + (10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
              + 10 ^ 6 * (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2)) :=
            add_le_add hunc hcapsum
        _ ≤ (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0)
            + LFterm e a b (capLevel 3 e) 0 := by
            refine add_le_add le_rfl ?_
            have hcapT0 : 10 ^ 6 * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
                + 10 ^ 6 * (3 : ℝ) ^ (((cubeLevel 3 e : ℕ) : ℝ) / 2)
                ≤ LFterm e a b (capLevel 3 e) 0 := by
              rw [LFterm, menuW_cap he, if_pos ⟨hDLT, by simp⟩, mul_one]
            exact hcapT0
        _ = ∑ s ∈ Finset.range (capLevel 3 e + 1), LFterm e a b s 0 :=
            (Finset.sum_range_succ _ _).symm
        _ ≤ localFactor 3 e a b := localFactor_ge_row_succ he a b
    · have hcap2 : ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
          ≤ LFterm e a b (capLevel 3 e) 0 + LFterm e a b (max (capLevel 3 e) j) j :=
        le_trans hcapsum (add_le_add hLFT hLFj)
      have hTT : LFterm e a b (capLevel 3 e) 0
          ≤ ∑ j' ∈ Finset.range (e + 1), LFterm e a b (capLevel 3 e) j' :=
        LFterm_le_row he a b (Finset.mem_range.mpr (by omega))
      have hrowT : capLevel 3 e ∈ Finset.range (capLevel 3 e + 1) :=
        Finset.mem_range.mpr (by omega)
      have huncT : (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0)
          ≤ ∑ s ∈ Finset.range (capLevel 3 e), ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j' :=
        Finset.sum_le_sum (fun s _ => LFterm_le_row he a b (Finset.mem_range.mpr (by omega)))
      have huncU : (∑ s ∈ Finset.range (capLevel 3 e), ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j')
          ≤ ∑ s ∈ Finset.range (capLevel 3 e + 1), ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j' :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun s => ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j')
          (fun s hs => Finset.mem_range.mpr (by have := Finset.mem_range.mp hs; omega))
          (fun s _ _ => Finset.sum_nonneg (fun j' _ => LFterm_nonneg he a b s j'))
      by_cases hjT : j ≤ capLevel 3 e
      · have hmax : max (capLevel 3 e) j = capLevel 3 e := max_eq_left hjT
        rw [hmax] at hcap2
        have hpair := LFterm_pair_le_row (s := capLevel 3 e) he a b hj0 hjr
        calc (∑ y ∈ uncSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2))
              + ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
            ≤ (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0)
              + (LFterm e a b (capLevel 3 e) 0 + LFterm e a b (capLevel 3 e) j) := by
              linarith [hunc, hcap2]
          _ ≤ (∑ s ∈ Finset.range (capLevel 3 e), ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j')
              + (∑ j' ∈ Finset.range (e + 1), LFterm e a b (capLevel 3 e) j') := by
              linarith [huncT, hTT, hpair]
          _ = ∑ s ∈ Finset.range (capLevel 3 e + 1),
                ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j' :=
              (Finset.sum_range_succ _ _).symm
          _ ≤ localFactor 3 e a b := localFactor_ge_rowblock he a b
      · have hjT' : capLevel 3 e < j := not_le.mp hjT
        have hmax : max (capLevel 3 e) j = j := max_eq_right (le_of_lt hjT')
        rw [hmax] at hcap2
        have hjj : LFterm e a b j j ≤ ∑ j' ∈ Finset.range (e + 1), LFterm e a b j j' :=
          LFterm_le_row he a b hjr
        have hjjrow : LFterm e a b j j
            ≤ ∑ s ∈ Finset.range (e + 2), ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j' :=
          le_trans hjj (Finset.single_le_sum
            (f := fun s => ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j')
            (fun s _ => Finset.sum_nonneg (fun j' _ => LFterm_nonneg he a b s j'))
            (a := j) (by
              rw [Finset.mem_range]
              have := Finset.mem_range.mp hjr
              omega))
        calc (∑ y ∈ uncSet 3 e a b, (3 : ℝ) ^ (((bval 3 e a b y : ℕ) : ℝ) / 2))
              + ((capSet 3 e a b).card : ℝ) * (3 : ℝ) ^ (((capLevel 3 e : ℕ) : ℝ) / 2)
            ≤ (∑ s ∈ Finset.range (capLevel 3 e), LFterm e a b s 0)
              + (LFterm e a b (capLevel 3 e) 0 + LFterm e a b j j) :=
              add_le_add hunc hcap2
          _ ≤ (∑ s ∈ Finset.range (capLevel 3 e),
                ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j')
              + ((∑ j' ∈ Finset.range (e + 1), LFterm e a b (capLevel 3 e) j')
                + (∑ j' ∈ Finset.range (e + 1), LFterm e a b j j')) :=
              add_le_add huncT (add_le_add hTT hjj)
          _ = (∑ s ∈ Finset.range (capLevel 3 e + 1),
                ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j')
              + (∑ j' ∈ Finset.range (e + 1), LFterm e a b j j') := by
              rw [Finset.sum_range_succ
                (f := fun s => ∑ j' ∈ Finset.range (e + 1), LFterm e a b s j'), add_assoc]
          _ ≤ localFactor 3 e a b :=
              localFactor_ge_rowblock_and_row he a b hjr hjT'


/-!
## STATUS (v2) — six remaining errors, all in `cap_card_le` except the last three

1. line ~395 (`hXnat`, second branch): `omega` needs the division bound explicitly; add
   `have hd : cubeLevel 3 e + capLevel 3 e - J - 2 ≤ 2 * ((cubeLevel 3 e + capLevel 3 e - J - 1) / 2) := by omega`
   (or prove `hXnat` by hand from that).
2. lines ~431/~450: the `le_add_of_nonneg_left`/`_right` steps have the summands swapped:
   in the content branch the quantity to bound sits in the *second* summand (use
   `le_add_of_nonneg_right`), in the trivial/`min = e` branches it sits in the second summand as
   well once the goal is rewritten to `X ≤ 10^6 * 3^(T/2) + X`.
3. line ~458 (no-content branch): after `rw [hJ0]` the second summand is `10^6 * 3^((m+0)/2)`;
   rewrite `Nat.add_zero` first, then finish with `le_add_of_nonneg_right` and the nonnegativity of
   `10^6 * 3^(m/2)` (do *not* bound it by `10^6 * 1`).
4. lines ~553/~562 (`simp made no progress`): the `simp only [...]` in `hunc` and in `hLFj` is a
   no-op once the `rw` has already normalised the goal; delete it (the goal is closed by `rfl`-style
   `le_rfl` or by `menuW_content`).
5. line ~575 (`linarith` in the `hj0` branch of the assembly): `rw [hj0]` then
   `max_eq_left (Nat.zero_le _)`, `menuW_cap he`, the indicator, and `Nat.add_zero`; finish with
   `linarith [rpow_three_nn ...]` (compare `10^6 * 3^((m+0)/2)` with `10^6 * 3^(T/2) + 10^6 * 3^(m/2)`).

Everything else (delegated modules, `unc_sum_le`, `cap_sum_eq`, the `LFterm` row lemmas, the
`localFactor` block lemmas, the final assembly skeleton) is in place and type-checks.
-/


/-!
## STATUS (v3) — remaining errors are all arithmetic plumbing; the mathematics is settled

Current build errors (12), by location:

* `cap_card_le`, `hXnat` (~line 397): `omega` cannot combine its division hypothesis with the
  goal.  Replace the whole `hXnat`/`hexp` pair by a *direct* real-arithmetic argument: from
  `d := (m + T - J - 1)/2` and `X := max 0 (m - d)` prove
  `(X : ℝ) + (T : ℝ)/2 ≤ ((m + J : ℕ) : ℝ)/2 + 1` by first establishing the ℕ statement
  `X + d ≤ m` and `2*d + 2 ≥ m + T - J` (both by `omega` on the two branches of `d ≤ m`), then
  casting with `exact_mod_cast`/`push_cast` and `linarith`.
* `cap_card_le`, the two `linarith` steps (~432, ~453): the exponent comparisons compare
  `3 ^ (X + T/2)` with `3 ^ ((m+J)/2 + 1)` and `3 ^ (m + T/2)` with `3 ^ ((m+e)/2)`; it is safest
  to *keep the exponents explicit* (`set X : ℝ := ...`, `set A : ℝ := ...`) and finish each step
  with `rpow_three_mono` + `linarith` on the exponent inequality alone, rather than letting
  `linarith` see the `3 ^ ...` atoms.
* assembly, `j = 0` branch (~568): `subst hj0` fails because `hj0 : j = 0` has `j` as a `set`
  local definition; use `rw [hj0] at hcapsum ⊢` and then `simp only [Nat.add_zero] at hcapsum`
  (the residual `cubeLevel 3 e + 0` sits *under* a cast, so `rw` will not reach it).
* assembly, the two `calc`s in the `j ≠ 0` branch (~620, ~629): after `rw [cap_sum_eq ...] at *`
  the *goal* has `↑(capSet 3 e a b).card * 3^(T/2)` in place of the cap sum, so both calc headers
  must start with that card form (already done in the `j = 0` branch — mirror it).
* the last four `linarith`s (~582, ~637, ~641): the same "expressions agree up to a `set`
  abbreviation" issue; `linarith` cannot use the `hJdef`/`hjdef` equations, so rewrite
  `hcapsum` into the `j`-form (`rw [← hJdef, ← hjdef] at hcapsum`, already inserted) *before*
  splitting on `j = 0` and on `j ≤ T`.
* line ~560: a `simp only [...]` that is now a no-op — delete it.

Once these are in, `declare_proven()` should pass: every other lemma in the file (arithmetic,
`gaussTwoRHS_eq_sum`, the `uncSet ⊔ capSet` split, `menuW_*`, `unc_sum_le`, `cap_sum_eq`,
`LFterm`/row-block lemmas, `capSet_card_le`, `cap_card_le`'s skeleton) type-checks, and the
delegated modules (`transfer_three`, `content_three`, `content_three_ge`, `content_three_split`,
`card_capSet_le_noncontent_three`, `card_capSet_le_content_three`, `DLp_of_unc_three`,
`DLp_of_cap_three`, `DLp_of_content_three`, `card_lvlSet_le_three`) are proved or delegated.
-/


/-!
## STATUS — complete

`Submission/Work/LinnikBurgess/lfSmall/counting_three.lean` proves
`Work.LinnikBurgess.lfSmall.counting_three` outright, with no `sorry` in the file or in its
import closure (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`).

The two cap-set cardinality bounds that were still outstanding are proved in
`Submission/Work/LinnikBurgess/lfSmall/capcount_three.lean`:

* `cap_count_noncontent_three : ¬ 3 ∣ contAB a b → (capSet 3 e a b).card ≤ 100`
  (triple vanishing at `k = 2` gives `3^2 ∤ N''(y)` for `y ∈ capSet`, hence `v_3(N''(y)) ≤ 1`;
  Hensel's lemma on `N'` confines every `y ∈ capSet` to within `3^{-(T-1)}` of a root of `N'`,
  and `card_root_close_le_three` gives `card ≤ deg(N') · 3^(m - T + 1) ≤ 3 · 27 = 81`).
* `cap_count_content_three : card ≤ 10^3 · 3^(m - ⌊(m + T - J - 1)/2⌋)`
  (`M = N / 3^J`; Hensel on `M` when `2 ν < K = m + T - J` and on `M'` otherwise, where
  triple vanishing at `k = J + 2` forces `v_3(M''(y)) ≤ 1`; `card_root_close_le_three` with
  `Q = M · M'` and modulus `E = ⌊(m + T - J - 1)/2⌋ - 2`).

The imports of the two now-unused modules `card_capSet_le_noncontent_three` /
`card_capSet_le_content_three` (which still carry `sorry`) were removed from this file.
-/
