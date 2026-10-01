import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.corr6_norm_le_prod_local
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_shifts
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.critN_content_iff
import Submission.Work.LinnikBurgess.natDegree_critN_le_four
import Submission.Work.LinnikBurgess.bval_transfer
import Submission.Work.LinnikBurgess.card_lvlSet_le
import Submission.Work.LinnikBurgess.card_capSet_le_noncontent
import Submission.Work.LinnikBurgess.card_capSet_le_content
import Submission.Work.LinnikBurgess.card_capSet_le_small
import Submission.Work.LinnikBurgess.DLp_of_unc
import Submission.Work.LinnikBurgess.DLp_of_cap
import Submission.Work.LinnikBurgess.DLp_of_content
import Submission.Work.LinnikBurgess.corr6_primePow_gaussTwo_le
import Submission.Work.LinnikBurgess.local_corr6_nonContent_sharp

open scoped BigOperators
open Classical

set_option maxHeartbeats 1000000

namespace Work.LinnikBurgess

private lemma menuW_unc {p e s : ℕ} (h5 : 5 ≤ p) (hs : s < capLevel p e) :
    menuW p e s 0 = 4 * (p : ℝ) ^ ((s : ℝ) / 2) := by
  rw [menuW, if_pos h5, if_pos rfl, if_pos hs]

private lemma menuW_cap {p e : ℕ} (h5 : 5 ≤ p) :
    menuW p e (capLevel p e) 0 = 7 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := by
  rw [menuW, if_pos h5, if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]

private lemma menuW_cap_succ {p e : ℕ} (h5 : 5 ≤ p) :
    menuW p e (capLevel p e + 1) 0 = 60 * (p : ℝ) ^ ((e : ℝ) / 6) := by
  rw [menuW, if_pos h5, if_pos rfl, if_neg (by omega : ¬ (capLevel p e + 1 < capLevel p e)),
    if_neg (by omega : ¬ (capLevel p e + 1 = capLevel p e)), if_pos rfl]

private lemma menuW_content {p e s j : ℕ} (h5 : 5 ≤ p) (hj : j ≠ 0)
    (hs : s = max (capLevel p e) j) :
    menuW p e s j = 7 * ((e : ℝ) + 1) * (p : ℝ) ^ (((cubeLevel p e : ℝ) + j) / 2) := by
  rw [menuW, if_pos h5, if_neg hj, if_pos hs]

private lemma menuW_nonneg {p e s j : ℕ} (h5 : 5 ≤ p) : 0 ≤ menuW p e s j := by
  have hp : (0:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 0 ≤ p)
  rw [menuW, if_pos h5]
  by_cases hj : j = 0
  · rw [if_pos hj]
    by_cases h1 : s < capLevel p e
    · rw [if_pos h1]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hp _)
    · rw [if_neg h1]
      by_cases h2 : s = capLevel p e
      · rw [if_pos h2]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hp _)
      · rw [if_neg h2]
        by_cases h3 : s = capLevel p e + 1
        · rw [if_pos h3]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hp _)
        · rw [if_neg h3]
  · rw [if_neg hj]
    by_cases h4 : s = max (capLevel p e) j
    · rw [if_pos h4]
      exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (Real.rpow_nonneg hp _)
    · rw [if_neg h4]

private lemma ite_nonneg (P : Prop) [Decidable P] (c : ℝ) (h : 0 ≤ c) :
    0 ≤ (if P then c else 0) := by
  split <;> simp [h]

/-- The double sum of `localFactor` is nonnegative for `p ≥ 5`. -/
private lemma localFactor_nonneg {p e : ℕ} (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ) :
    0 ≤ localFactor p e a b := by
  rw [localFactor]
  refine Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => ?_))
  exact mul_nonneg (menuW_nonneg hp5)
    (ite_nonneg (DLp p s a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num))

/-- `localFactor` dominates the single menu term `4 p^{s/2}` at `(s,0)`, `s < T`. -/
private lemma localFactor_ge_unc {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    {s : ℕ} (hs : s < capLevel p e) :
    4 * (p : ℝ) ^ ((s : ℝ) / 2) * (if DLp p s a b then 1 else 0) ≤ localFactor p e a b := by
  classical
  have hs2 : s ∈ Finset.range (e + 2) :=
    Finset.mem_range.mpr (by have := capLevel_le_self (p := p) (e := e) hp5; omega)
  have h0 : (0:ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  have hterm : menuW p e s 0 * (if DLp p s a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      = 4 * (p : ℝ) ^ ((s : ℝ) / 2) * (if DLp p s a b then 1 else 0) := by
    rw [menuW_unc hp5 hs]
    simp only [pow_zero, one_dvd, and_true]
  rw [← hterm]
  calc menuW p e s 0 * (if DLp p s a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      = menuW p e s 0 * (if DLp p s a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0) := rfl
    _ ≤ ∑ j ∈ Finset.range (e + 1),
          menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun j => menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0))
          (fun j _ => mul_nonneg (menuW_nonneg hp5)
            (ite_nonneg (DLp p s a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num)))
          (a := 0) h0
    _ ≤ ∑ s' ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
          menuW p e s' j * (if DLp p s' a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun s' => ∑ j ∈ Finset.range (e + 1),
            menuW p e s' j * (if DLp p s' a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0))
          (fun s' _ => Finset.sum_nonneg
            (fun j _ => mul_nonneg (menuW_nonneg hp5)
              (ite_nonneg (DLp p s' a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num))))
          (a := s) hs2
    _ = localFactor p e a b := rfl

/-- `localFactor` dominates the single menu term `7 p^{T/2}` at `(T,0)`. -/
private lemma localFactor_ge_cap {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (hDL : DLp p (capLevel p e) a b) :
    7 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) ≤ localFactor p e a b := by
  classical
  have hs2 : capLevel p e ∈ Finset.range (e + 2) :=
    Finset.mem_range.mpr (by have := capLevel_le_self (p := p) (e := e) hp5; omega)
  have h0 : (0:ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  have hterm : menuW p e (capLevel p e) 0
        * (if DLp p (capLevel p e) a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      = 7 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := by
    rw [menuW_cap hp5, if_pos ⟨hDL, by simp⟩, mul_one]
  rw [← hterm]
  calc menuW p e (capLevel p e) 0
        * (if DLp p (capLevel p e) a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      ≤ ∑ j ∈ Finset.range (e + 1),
          menuW p e (capLevel p e) j
            * (if DLp p (capLevel p e) a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun j => menuW p e (capLevel p e) j
            * (if DLp p (capLevel p e) a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0))
          (fun j _ => mul_nonneg (menuW_nonneg hp5)
            (ite_nonneg (DLp p (capLevel p e) a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num)))
          (a := 0) h0
    _ ≤ ∑ s' ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
          menuW p e s' j * (if DLp p s' a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun s' => ∑ j ∈ Finset.range (e + 1),
            menuW p e s' j * (if DLp p s' a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0))
          (fun s' _ => Finset.sum_nonneg
            (fun j _ => mul_nonneg (menuW_nonneg hp5)
              (ite_nonneg (DLp p s' a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num))))
          (a := capLevel p e) hs2
    _ = localFactor p e a b := rfl

/-- `localFactor` dominates the menu term `60 p^{e/6}` at `(T+1,0)`. -/
private lemma localFactor_ge_cap_succ {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (hDL : DLp p (capLevel p e + 1) a b) :
    60 * (p : ℝ) ^ ((e : ℝ) / 6) ≤ localFactor p e a b := by
  classical
  have hsucc : capLevel p e + 1 ∈ Finset.range (e + 2) :=
    Finset.mem_range.mpr (by have := capLevel_le_self (p := p) (e := e) hp5; omega)
  have h0 : (0:ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  have hterm : menuW p e (capLevel p e + 1) 0
        * (if DLp p (capLevel p e + 1) a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      = 60 * (p : ℝ) ^ ((e : ℝ) / 6) := by
    rw [menuW_cap_succ hp5, if_pos ⟨hDL, by simp⟩, mul_one]
  rw [← hterm]
  calc menuW p e (capLevel p e + 1) 0
        * (if DLp p (capLevel p e + 1) a b ∧ p ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      ≤ ∑ j ∈ Finset.range (e + 1),
          menuW p e (capLevel p e + 1) j
            * (if DLp p (capLevel p e + 1) a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun j => menuW p e (capLevel p e + 1) j
            * (if DLp p (capLevel p e + 1) a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0))
          (fun j _ => mul_nonneg (menuW_nonneg hp5)
            (ite_nonneg (DLp p (capLevel p e + 1) a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num)))
          (a := 0) h0
    _ ≤ ∑ s' ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
          menuW p e s' j * (if DLp p s' a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun s' => ∑ j ∈ Finset.range (e + 1),
            menuW p e s' j * (if DLp p s' a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0))
          (fun s' _ => Finset.sum_nonneg
            (fun j _ => mul_nonneg (menuW_nonneg hp5)
              (ite_nonneg (DLp p s' a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num))))
          (a := capLevel p e + 1) hsucc
    _ = localFactor p e a b := rfl

/-- `localFactor` dominates the content menu term `7 (e+1) p^{(m+j)/2}` at `(max T j, j)`. -/
private lemma localFactor_ge_content {p e j : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (hj : 1 ≤ j) (hje : j ≤ e) (hDL : DLp p (max (capLevel p e) j) a b)
    (hcont : p ^ j ∣ contAB a b) :
    7 * ((e : ℝ) + 1) * (p : ℝ) ^ (((cubeLevel p e : ℝ) + j) / 2) ≤ localFactor p e a b := by
  classical
  have hs2 : max (capLevel p e) j ∈ Finset.range (e + 2) :=
    Finset.mem_range.mpr (by have := capLevel_le_self (p := p) (e := e) hp5; omega)
  have hj2 : j ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
  have hterm : menuW p e (max (capLevel p e) j) j
        * (if DLp p (max (capLevel p e) j) a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0)
      = 7 * ((e : ℝ) + 1) * (p : ℝ) ^ (((cubeLevel p e : ℝ) + j) / 2) := by
    rw [menuW_content hp5 (by omega) rfl, if_pos ⟨hDL, hcont⟩, mul_one]
  rw [← hterm]
  calc menuW p e (max (capLevel p e) j) j
        * (if DLp p (max (capLevel p e) j) a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0)
      ≤ ∑ j' ∈ Finset.range (e + 1),
          menuW p e (max (capLevel p e) j) j'
            * (if DLp p (max (capLevel p e) j) a b ∧ p ^ j' ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun j' => menuW p e (max (capLevel p e) j) j'
            * (if DLp p (max (capLevel p e) j) a b ∧ p ^ j' ∣ contAB a b then (1:ℝ) else 0))
          (fun j' _ => mul_nonneg (menuW_nonneg hp5)
            (ite_nonneg (DLp p (max (capLevel p e) j) a b ∧ p ^ j' ∣ contAB a b) 1 (by norm_num)))
          (a := j) hj2
    _ ≤ ∑ s' ∈ Finset.range (e + 2), ∑ j' ∈ Finset.range (e + 1),
          menuW p e s' j' * (if DLp p s' a b ∧ p ^ j' ∣ contAB a b then (1:ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun s' => ∑ j' ∈ Finset.range (e + 1),
            menuW p e s' j' * (if DLp p s' a b ∧ p ^ j' ∣ contAB a b then (1:ℝ) else 0))
          (fun s' _ => Finset.sum_nonneg
            (fun j' _ => mul_nonneg (menuW_nonneg hp5)
              (ite_nonneg (DLp p s' a b ∧ p ^ j' ∣ contAB a b) 1 (by norm_num))))
          (a := max (capLevel p e) j) hs2
    _ = localFactor p e a b := rfl

/-! ### The support sum -/

private lemma gaussTwoRHS_eq_sum {p e : ℕ} (a b : Fin 3 → ℕ) :
    gaussTwoRHS p e (cubeLevel p e) a b
      = ∑ y ∈ suppSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2) := by
  classical
  rw [gaussTwoRHS, suppSet, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : suppPred p e a b y
  · rw [if_pos h]
    rw [if_pos (show UnitAt p y a b ∧
        p ^ (cubeLevel p e + vcap p (e - 2 * cubeLevel p e) (defect2 p e a b y).val)
          ∣ (defect1 p e a b y).val from h)]
    simp only [bval, capLevel]
  · rw [if_neg h]
    rw [if_neg (show ¬ (UnitAt p y a b ∧
        p ^ (cubeLevel p e + vcap p (e - 2 * cubeLevel p e) (defect2 p e a b y).val)
          ∣ (defect1 p e a b y).val) from h)]

private lemma unc_sum_le {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hN : critN a b ≠ 0) (hdeg : (critN a b).natDegree ≤ 4)
    (hbt : SuppTransfer p e a b) :
    ∑ y ∈ uncSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
      ≤ ∑ s ∈ Finset.range (capLevel p e),
          4 * (p : ℝ) ^ ((s : ℝ) / 2) * (if DLp p s a b then 1 else 0) := by
  classical
  have hbv : ∀ y ∈ uncSet p e a b, bval p e a b y = nval p e a b y := by
    intro y hy
    obtain ⟨hys, hlt⟩ := Finset.mem_filter.mp hy
    have hsp : suppPred p e a b y := (Finset.mem_filter.mp hys).2
    rw [(hbt y hsp).1, min_eq_left (le_of_lt hlt)]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hbv y hy])]
  have hmap : ∀ y ∈ uncSet p e a b, nval p e a b y ∈ Finset.range (capLevel p e) :=
    fun y hy => Finset.mem_range.mpr (Finset.mem_filter.mp hy).2
  rw [← Finset.sum_fiberwise_of_maps_to hmap (f := fun y => (p : ℝ) ^ ((nval p e a b y : ℝ) / 2))]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsT : s < capLevel p e := Finset.mem_range.mp hs
  rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hDL : DLp p s a b
  · rw [if_pos hDL]
    have hle : ((uncSet p e a b).filter (fun y => nval p e a b y = s)).card ≤ 4 := by
      refine le_trans (Finset.card_le_card ?_)
        (card_lvlSet_le (p := p) (e := e) (a := a) (b := b) hp5 he hN hdeg hbt hsT)
      intro y hy
      obtain ⟨hyu, hys⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyu).1, hys⟩
    calc ((uncSet p e a b).filter (fun y => nval p e a b y = s)).card
            * (p : ℝ) ^ ((s : ℝ) / 2)
        ≤ 4 * (p : ℝ) ^ ((s : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle)
            (Real.rpow_nonneg (by positivity) _)
      _ = 4 * (p : ℝ) ^ ((s : ℝ) / 2) * 1 := (mul_one _).symm
  · rw [if_neg hDL]
    have hempty : (uncSet p e a b).filter (fun y => nval p e a b y = s) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hyu hy2
      exact hDL (by
        rw [← hy2]
        exact DLp_of_unc (p := p) (e := e) (a := a) (b := b) hp5 he
          (Finset.mem_filter.mp (Finset.mem_filter.mp hyu).1).2 hbt (by rw [hy2]; exact hsT))
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    simp

/-! ### Row bounds for `localFactor` -/

/-- A single summand of `localFactor`. -/
private noncomputable def LFterm (p e : ℕ) (a b : Fin 3 → ℕ) (s j : ℕ) : ℝ :=
  menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then (1:ℝ) else 0)

private lemma LFterm_nonneg {p e : ℕ} (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ) (s j : ℕ) :
    0 ≤ LFterm p e a b s j :=
  mul_nonneg (menuW_nonneg hp5) (ite_nonneg (DLp p s a b ∧ p ^ j ∣ contAB a b) 1 (by norm_num))

private lemma localFactor_eq_rows {p e : ℕ} (a b : Fin 3 → ℕ) :
    localFactor p e a b = ∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j := by
  rw [localFactor]; rfl

/-- `localFactor` dominates the `j = 0` row up to `T = capLevel p e`. -/
private lemma localFactor_ge_row_succ {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ) :
    (∑ s ∈ Finset.range (capLevel p e + 1), LFterm p e a b s 0) ≤ localFactor p e a b := by
  classical
  rw [localFactor_eq_rows]
  refine le_trans (Finset.sum_le_sum (f := fun s => LFterm p e a b s 0)
    (g := fun s => ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j) (fun s _ => ?_)) ?_
  · exact Finset.single_le_sum (f := fun j => LFterm p e a b s j)
      (fun j _ => LFterm_nonneg hp5 a b s j) (a := 0)
      (Finset.mem_range.mpr (by omega : 0 < e + 1))
  · refine Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun s => ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j) ?_ ?_
    · intro s hs
      have hs' := Finset.mem_range.mp hs
      have hT := capLevel_le_self (p := p) (e := e) hp5
      exact Finset.mem_range.mpr (by omega)
    · intro s _ _
      exact Finset.sum_nonneg (fun j _ => LFterm_nonneg hp5 a b s j)

/-- `localFactor` dominates the `j = 0` row up to `T` *plus* the single summand at
`(max T j₀, j₀)` with `j₀ ≠ 0`. -/
private lemma localFactor_ge_row_and_content {p e j₀ : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (a b : Fin 3 → ℕ) (hj₀ : j₀ ≠ 0) (hj₀r : j₀ ∈ Finset.range (e + 1)) :
    (∑ s ∈ Finset.range (capLevel p e), LFterm p e a b s 0)
      + LFterm p e a b (max (capLevel p e) j₀) j₀ ≤ localFactor p e a b := by
  classical
  set s₀ := max (capLevel p e) j₀ with hs₀def
  have hs₀T : capLevel p e ≤ s₀ := le_max_left _ _
  have hs₀r : s₀ ∈ Finset.range (e + 2) := by
    rw [Finset.mem_range, hs₀def]
    have h1 : capLevel p e ≤ e := capLevel_le_self (p := p) (e := e) hp5
    have h2 : j₀ ≤ e := by have := Finset.mem_range.mp hj₀r; omega
    have h3 : max (capLevel p e) j₀ ≤ e := max_le h1 h2
    omega
  have hnotmem : s₀ ∉ Finset.range (capLevel p e) := by
    rw [Finset.mem_range]; omega
  have hrow0 : ∀ s ∈ Finset.range (capLevel p e), LFterm p e a b s 0
      ≤ ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j := by
    intro s _
    exact Finset.single_le_sum (f := fun j => LFterm p e a b s j)
      (fun j _ => LFterm_nonneg hp5 a b s j) (a := 0)
      (Finset.mem_range.mpr (by omega : 0 < e + 1))
  have hrowj : LFterm p e a b s₀ j₀ ≤ ∑ j ∈ Finset.range (e + 1), LFterm p e a b s₀ j :=
    Finset.single_le_sum (f := fun j => LFterm p e a b s₀ j)
      (fun j _ => LFterm_nonneg hp5 a b s₀ j) hj₀r
  rw [localFactor_eq_rows]
  calc (∑ s ∈ Finset.range (capLevel p e), LFterm p e a b s 0) + LFterm p e a b s₀ j₀
      ≤ (∑ s ∈ Finset.range (capLevel p e), ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j)
        + (∑ j ∈ Finset.range (e + 1), LFterm p e a b s₀ j) := add_le_add (Finset.sum_le_sum hrow0) hrowj
    _ = ∑ s ∈ (Finset.range (capLevel p e)) ∪ {s₀}, ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j := by
        rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr hnotmem), Finset.sum_singleton]
    _ ≤ ∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun s => ∑ j ∈ Finset.range (e + 1), LFterm p e a b s j) ?_ ?_
        · intro s hs
          rcases Finset.mem_union.mp hs with h | h
          · have hs' := Finset.mem_range.mp h
            have hT := capLevel_le_self (p := p) (e := e) hp5
            exact Finset.mem_range.mpr (by omega)
          · rw [Finset.mem_singleton] at h
            subst h
            exact hs₀r
        · intro s _ _
          exact Finset.sum_nonneg (fun j _ => LFterm_nonneg hp5 a b s j)

/-- The `j = 0` row of `localFactor` up to `T` is the uncapped menu sum. -/
private lemma row_eq_unc {p e : ℕ} (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ) :
    (∑ s ∈ Finset.range (capLevel p e), LFterm p e a b s 0)
      = ∑ s ∈ Finset.range (capLevel p e),
          4 * (p : ℝ) ^ ((s : ℝ) / 2) * (if DLp p s a b then 1 else 0) := by
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [LFterm, menuW_unc hp5 (Finset.mem_range.mp hs)]
  simp only [pow_zero, one_dvd, and_true]

/-! ### Bounds for the capped part -/

private lemma cap_sum_eq {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hbt : SuppTransfer p e a b) :
    ∑ y ∈ capSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
      = ((capSet p e a b).card : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := by
  classical
  have hb : ∀ y ∈ capSet p e a b, bval p e a b y = capLevel p e := by
    intro y hy
    obtain ⟨hys, hle⟩ := Finset.mem_filter.mp hy
    have hsp : suppPred p e a b y := (Finset.mem_filter.mp hys).2
    rw [(hbt y hsp).1, min_eq_right hle]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hb y hy])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- `(N mod p) ≠ 0` follows from `¬ p ∣ contAB a b`. -/
private lemma map_ne_zero_of_not_dvd {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (h : ¬ p ∣ contAB a b) : (critN a b).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro h0
  apply h
  have hall : ∀ n, ((p ^ 1 : ℕ) : ℤ) ∣ (critN a b).coeff n := by
    intro n
    have h1 : (((critN a b).coeff n : ℤ) : ZMod p) = 0 := by
      have := congrArg (fun q : Polynomial (ZMod p) => q.coeff n) h0
      simpa [Polynomial.coeff_map] using this
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((critN a b).coeff n) p).mp h1
    simpa using h2
  have := (critN_content_iff (p := p) (k := 1) hp5 a b).mp hall
  simpa using this

/-- The capped part in the `¬ p ∣ contAB` regime: it is dominated by the `(T,0)` menu summand. -/
private lemma cap_sum_le_noncontent {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hdeg2 : 2 ≤ (critN a b).natDegree)
    (hdeg : (critN a b).natDegree ≤ 4) (hbt : SuppTransfer p e a b)
    (hnot : ¬ p ∣ contAB a b) (hcase : e ≤ 3 ∨ ¬ DLp p (capLevel p e + 1) a b) :
    ∑ y ∈ capSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
      ≤ LFterm p e a b (capLevel p e) 0 := by
  classical
  have hmod := map_ne_zero_of_not_dvd hp5 a b hnot
  have hpnn : (0:ℝ) ≤ (p:ℝ) := by positivity
  rw [cap_sum_eq hp5 he a b hbt]
  by_cases hDL : DLp p (capLevel p e) a b
  · have hcard : (capSet p e a b).card ≤ 4 := by
      rcases hcase with he3 | hnoDL
      · exact card_capSet_le_small (p := p) (e := e) (a := a) (b := b) hp5 he he3 hdeg hmod hbt
      · exact card_capSet_le_noncontent (p := p) (e := e) (a := a) (b := b) hp5 he hdeg2 hdeg hmod hbt hnoDL
    have hstep : ((capSet p e a b).card : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
        ≤ 4 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.rpow_nonneg hpnn _)
    have hval : LFterm p e a b (capLevel p e) 0 = 7 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := by
      rw [LFterm, menuW_cap hp5, if_pos ⟨hDL, by simp⟩, mul_one]
    rw [hval]
    have h4 : 4 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
        ≤ 7 * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := by
      have := Real.rpow_nonneg hpnn ((capLevel p e : ℝ) / 2)
      linarith
    exact le_trans hstep h4
  · have hempty : capSet p e a b = ∅ := by
      rw [capSet, Finset.filter_eq_empty_iff]
      intro y hy hc
      exact hDL (DLp_of_cap (p := p) (e := e) (a := a) (b := b) hp5 he
        (Finset.mem_filter.mp hy).2 hbt hc)
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
    rw [LFterm, if_neg (by simp [hDL])]
    exact mul_nonneg (menuW_nonneg hp5) (by norm_num)

/-- The capped part in the `p ∣ contAB` regime: it is dominated by the `(max T j, j)` menu summand,
with `j = min J e`, `J = v_p(contAB)`. -/
private lemma cap_sum_le_content {p e J j : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hdeg2 : 2 ≤ (critN a b).natDegree)
    (hdeg : (critN a b).natDegree ≤ 4) (hc0 : contAB a b ≠ 0) (hbt : SuppTransfer p e a b)
    (hdvd : p ∣ contAB a b) (hJdef : padicValNat p (contAB a b) = J) (hjdef : j = min J e) :
    ∑ y ∈ capSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
      ≤ LFterm p e a b (max (capLevel p e) j) j := by
  classical
  have hpnn : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hj1 : 1 ≤ j := by
    rw [hjdef]
    have h1 : 1 ≤ J := by
      rw [← hJdef]
      have h1 := (padicValNat_dvd_iff (p := p) 1 (contAB a b)).mp (by simpa using hdvd)
      rcases h1 with h | h
      · exact absurd h hc0
      · exact h
    exact le_min h1 (by omega)
  rw [cap_sum_eq hp5 he a b hbt]
  by_cases hne : (capSet p e a b).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hsp0 : suppPred p e a b y₀ :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy₀).1).2
    have hunit0 : UnitAt p y₀ a b := hsp0.1
    have hcap0 : capLevel p e ≤ nval p e a b y₀ := (Finset.mem_filter.mp hy₀).2
    have hjleJ : j ≤ J := by rw [hjdef]; exact min_le_left _ _
    have hjle : j ≤ e := by rw [hjdef]; exact min_le_right _ _
    have hDLmax : DLp p (max (capLevel p e) j) a b := by
      rcases max_choice (capLevel p e) j with h | h
      · rw [h]; exact DLp_of_cap (p := p) (e := e) (a := a) (b := b) hp5 he hsp0 hbt hcap0
      · rw [h]; exact DLp_of_content (p := p) (e := e) (J := J) (a := a) (b := b) hp5
          hunit0 hc0 hJdef j hjleJ hjle
    have hcont : p ^ j ∣ contAB a b := by
      have hpJdvd : p ^ J ∣ contAB a b := by rw [← hJdef]; exact pow_padicValNat_dvd
      exact dvd_trans (Nat.pow_dvd_pow p hjleJ) hpJdvd
    have hval : LFterm p e a b (max (capLevel p e) j) j
        = 7 * ((e:ℝ) + 1) * (p : ℝ) ^ (((cubeLevel p e : ℝ) + (j:ℝ)) / 2) := by
      rw [LFterm, menuW_content hp5 (by omega) rfl, if_pos ⟨hDLmax, hcont⟩, mul_one]
    rw [hval]
    by_cases hbig : e - cubeLevel p e ≤ J
    · -- trivial count
      have hcard : (capSet p e a b).card ≤ p ^ cubeLevel p e := by
        refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range _))
        intro y hy
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
      have hstep : ((capSet p e a b).card : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
          ≤ ((p ^ cubeLevel p e : ℕ) : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.rpow_nonneg hpnn _)
      have hppos : (0:ℝ) < (p:ℝ) := by positivity
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by
        have hprime : p.Prime := Fact.out
        exact_mod_cast hprime.one_le
      have heq : ((p ^ cubeLevel p e : ℕ) : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
          = (p : ℝ) ^ ((e : ℝ) / 2) := by
        have h1 : ((cubeLevel p e + capLevel p e : ℕ) : ℝ) = ((e - cubeLevel p e : ℕ) : ℝ) := by
          rw [cubeLevel_add_capLevel hp5 he]
        rw [Nat.cast_add, Nat.cast_sub (cubeLevel_le_self hp5 (by omega))] at h1
        have hT' : (capLevel p e : ℝ) = (e:ℝ) - 2 * (cubeLevel p e : ℝ) := by
          have h : capLevel p e = e - 2 * cubeLevel p e := rfl
          rw [h, Nat.cast_sub (two_mul_cubeLevel_le hp5 he)]
          push_cast
          ring
        rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (cubeLevel p e), ← Real.rpow_add hppos]
        congr 1
        rw [hT']
        linarith
      have hexp : (e : ℝ) / 2 ≤ ((cubeLevel p e : ℝ) + (j : ℝ)) / 2 := by
        have h : e ≤ cubeLevel p e + j := by
          have hjge : e - cubeLevel p e ≤ j := by
            rw [hjdef]
            by_cases hcase : J ≤ e
            · rw [min_eq_left hcase]; exact hbig
            · rw [min_eq_right (le_of_lt (not_le.mp hcase))]; omega
          omega
        have h' : (e : ℝ) ≤ (cubeLevel p e : ℝ) + (j : ℝ) := by exact_mod_cast h
        linarith
      have hlast : (p : ℝ) ^ ((e : ℝ) / 2)
          ≤ 7 * ((e : ℝ) + 1) * (p : ℝ) ^ (((cubeLevel p e : ℝ) + (j : ℝ)) / 2) := by
        have h1 : (1:ℝ) ≤ 7 * ((e:ℝ) + 1) := by
          have : (0:ℝ) ≤ (e:ℝ) := by positivity
          nlinarith
        calc (p : ℝ) ^ ((e : ℝ) / 2)
            ≤ (p : ℝ) ^ (((cubeLevel p e : ℝ) + (j : ℝ)) / 2) :=
              Real.rpow_le_rpow_of_exponent_le hp1 hexp
          _ ≤ 7 * ((e : ℝ) + 1) * (p : ℝ) ^ (((cubeLevel p e : ℝ) + (j : ℝ)) / 2) := by
              nth_rewrite 1 [← one_mul ((p:ℝ) ^ (((cubeLevel p e : ℝ) + (j:ℝ)) / 2))]
              exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpnn _)
      exact le_trans (le_trans hstep (le_of_eq heq)) (le_trans hlast le_rfl)
    · -- the content count
      have hA : J < e - cubeLevel p e := not_le.mp hbig
      have hA1 : 1 ≤ J := by
        have h1 : 1 ≤ padicValNat p (contAB a b) := by
          have h0 := (padicValNat_dvd_iff (p := p) 1 (contAB a b)).mp (by simpa using hdvd)
          rcases h0 with h | h
          · exact absurd h hc0
          · exact h
        rwa [hJdef] at h1
      have hcontAll : ∀ n, ((p ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n :=
        (critN_content_iff (p := p) (k := J) hp5 a b).mpr (by rw [← hJdef]; exact pow_padicValNat_dvd)
      have hprim : ∃ n, ¬ ((p ^ (J + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n := by
        by_contra hcon
        push_neg at hcon
        have : p ^ (J + 1) ∣ contAB a b :=
          (critN_content_iff (p := p) (k := J + 1) hp5 a b).mp hcon
        have hle : J + 1 ≤ padicValNat p (contAB a b) := by
          have h1 := (padicValNat_dvd_iff (p := p) (J + 1) (contAB a b)).mp this
          rcases h1 with h | h
          · exact absurd h hc0
          · exact h
        rw [hJdef] at hle
        omega
      have hcard := card_capSet_le_content (p := p) (e := e) (J := J) (a := a) (b := b)
        hp5 he hdeg2 hdeg hcontAll hprim hbt hA1 hA
      set K := max 0 (cubeLevel p e - (e - cubeLevel p e - J + 1) / 2) with hKdef
      have hs1 : ((capSet p e a b).card : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
          ≤ ((7 * (e + 1) * p ^ K : ℕ) : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.rpow_nonneg hpnn _)
      have hcast : ((7 * (e + 1) * p ^ K : ℕ) : ℝ) = 7 * ((e:ℝ) + 1) * (p:ℝ) ^ ((K:ℝ)) := by
        push_cast
        rw [Real.rpow_natCast]
      have hA2 : (e - cubeLevel p e - J : ℕ) ≤ 2 * cubeLevel p e := by
        have := capLevel_le_cubeLevel_div (p := p) (e := e) hp5 he
        omega
      have hjJ : j = J := by rw [hjdef]; exact min_eq_left (le_of_lt (by omega))
      have hexpK : ((K:ℝ)) + ((capLevel p e : ℝ)) / 2
          ≤ ((cubeLevel p e : ℝ) + (j : ℝ)) / 2 := by
        rw [hjJ]
        have hTreal : (capLevel p e : ℝ) = (e:ℝ) - 2 * (cubeLevel p e : ℝ) := by
          have h : capLevel p e = e - 2 * cubeLevel p e := rfl
          rw [h, Nat.cast_sub (two_mul_cubeLevel_le hp5 he)]
          push_cast
          ring
        have hdiv : (((e - cubeLevel p e - J + 1) / 2 : ℕ) : ℝ)
            ≥ ((e - cubeLevel p e - J : ℕ) : ℝ) / 2 := by
          have hnat : (e - cubeLevel p e - J : ℕ) ≤ 2 * ((e - cubeLevel p e - J + 1) / 2 : ℕ) := by
            have h1 := Nat.div_add_mod (e - cubeLevel p e - J + 1) 2
            have h2 := Nat.mod_lt (e - cubeLevel p e - J + 1) (by norm_num : 0 < 2)
            omega
          have hreal : ((e - cubeLevel p e - J : ℕ) : ℝ)
              ≤ 2 * (((e - cubeLevel p e - J + 1) / 2 : ℕ) : ℝ) := by
            exact_mod_cast hnat
          linarith
        have hKle : (K : ℝ) ≤ (cubeLevel p e : ℝ) - ((e - cubeLevel p e - J : ℕ) : ℝ) / 2 := by
          have h1 : (K : ℝ) = max 0 ((cubeLevel p e : ℝ)
              - (((e - cubeLevel p e - J + 1) / 2 : ℕ) : ℝ)) := by
            rw [hKdef, Nat.cast_max, Nat.cast_zero]
            congr 1
            exact Nat.cast_sub (R := ℝ) (by omega)
          rw [h1]
          have h3 : (0:ℝ) ≤ (cubeLevel p e : ℝ) - ((e - cubeLevel p e - J : ℕ) : ℝ) / 2 := by
            have hh : ((e - cubeLevel p e - J : ℕ) : ℝ) ≤ 2 * (cubeLevel p e : ℝ) := by
              exact_mod_cast hA2
            linarith
          exact max_le h3 (by linarith)
        have hAreal : ((e - cubeLevel p e - J : ℕ) : ℝ)
            = (e : ℝ) - (cubeLevel p e : ℝ) - (J : ℝ) := by
          have h1 : (e - cubeLevel p e - J : ℕ) = (e - cubeLevel p e) - J := rfl
          rw [h1, Nat.cast_sub (R := ℝ) (by omega : J ≤ e - cubeLevel p e),
            Nat.cast_sub (R := ℝ) (by omega : cubeLevel p e ≤ e)]
        linarith
      have hstep2 : 7 * ((e:ℝ) + 1) * (p:ℝ) ^ ((K:ℝ)) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
          = 7 * ((e:ℝ) + 1) * ((p:ℝ) ^ ((K:ℝ)) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)) := by ring
      have hstep3 : (p:ℝ) ^ ((K:ℝ)) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
          = (p:ℝ) ^ ((K:ℝ) + (capLevel p e : ℝ) / 2) := (Real.rpow_add (by positivity) _ _).symm
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by
        have hprime : p.Prime := Fact.out
        exact_mod_cast hprime.one_le
      have hstep4 : (p:ℝ) ^ ((K:ℝ) + (capLevel p e : ℝ) / 2)
          ≤ (p:ℝ) ^ (((cubeLevel p e : ℝ) + (j:ℝ)) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hp1 hexpK
      calc ((capSet p e a b).card : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)
          ≤ ((7 * (e + 1) * p ^ K : ℕ) : ℝ) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := hs1
        _ = 7 * ((e:ℝ) + 1) * (p:ℝ) ^ ((K:ℝ)) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2) := by
              rw [hcast]
        _ = 7 * ((e:ℝ) + 1) * ((p:ℝ) ^ ((K:ℝ)) * (p : ℝ) ^ ((capLevel p e : ℝ) / 2)) := hstep2
        _ = 7 * ((e:ℝ) + 1) * ((p:ℝ) ^ ((K:ℝ) + (capLevel p e : ℝ) / 2)) := by rw [hstep3]
        _ ≤ 7 * ((e:ℝ) + 1) * ((p:ℝ) ^ (((cubeLevel p e : ℝ) + (j:ℝ)) / 2)) :=
              mul_le_mul_of_nonneg_left hstep4 (by positivity)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact LFterm_nonneg hp5 a b _ _

/-! ### Splitting the support sum -/

private lemma suppSet_sum_split {p e : ℕ} (a b : Fin 3 → ℕ) :
    ∑ y ∈ suppSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
      = (∑ y ∈ uncSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2))
        + ∑ y ∈ capSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2) := by
  classical
  have h2 : capSet p e a b
      = (suppSet p e a b).filter (fun y => ¬ nval p e a b y < capLevel p e) := by
    rw [capSet]
    exact Finset.filter_congr (fun y _ => by simp only [not_lt])
  rw [uncSet, h2]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : nval p e a b y < capLevel p e
  · rw [if_pos h, if_neg (not_not_intro h), add_zero]
  · rw [if_neg h, if_pos h, zero_add]

/-- Theorem L (U7).  Brute-force sanity first: p=7,e=4, a=(1,1,4), b=(2,5,5): |S|=215.9, p^{e/2}=49, localFactor=226.6; p=7,e=7 same v: |S|=10578.4, localFactor=603.4. -/
theorem localFactor_bound_ge5 {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b := by
  classical
  have hNZ := critN_ne_zero_of_unique a b i hi
  have hdeg2 : 2 ≤ (critN a b).natDegree := hNZ.1
  have hc0 : contAB a b ≠ 0 := hNZ.2
  have hdeg : (critN a b).natDegree ≤ 4 := natDegree_critN_le_four a b
  have hN : critN a b ≠ 0 := fun h => by rw [h] at hdeg2; simp at hdeg2
  have hbt : SuppTransfer p e a b := bval_transfer hp5 he a b
  have hp2 : p ≠ 2 := by omega
  have hpnn : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hppos : (0:ℝ) < (p:ℝ) := by positivity
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by
    have hprime : p.Prime := Fact.out
    exact_mod_cast hprime.one_le
  have hm1 : 1 ≤ cubeLevel p e := one_le_cubeLevel hp5 (by omega)
  have h3 : e ≤ 3 * cubeLevel p e := e_le_three_mul_cubeLevel hp5
  have h2 : 2 * cubeLevel p e ≤ e := two_mul_cubeLevel_le hp5 he
  have hAA := corr6_primePow_gaussTwo_le (p := p) (e := e) (m := cubeLevel p e) hp2 hm1 h3 h2 χ hχ a b
  -- the sum bound, in each of the cases that are not covered by Lemma B
  have hsum : ∀ (hcase : p ∣ contAB a b ∨
      (¬ p ∣ contAB a b ∧ (e ≤ 3 ∨ ¬ DLp p (capLevel p e + 1) a b))),
      gaussTwoRHS p e (cubeLevel p e) a b ≤ localFactor p e a b := by
    intro hcase
    rw [gaussTwoRHS_eq_sum, suppSet_sum_split]
    rcases hcase with hdvd | ⟨hnot, hsmall⟩
    · -- ### `p ∣ contAB`: the content regime
      set J := padicValNat p (contAB a b) with hJdef
      set j := min J e with hjdef
      have hJ1 : 1 ≤ J := by
        rw [hJdef]
        have h0 := (padicValNat_dvd_iff (p := p) 1 (contAB a b)).mp (by simpa using hdvd)
        rcases h0 with h | h
        · exact absurd h hc0
        · exact h
      have hj0 : j ≠ 0 := by
        rw [hjdef]
        intro h
        have h1 : 1 ≤ min J e := le_min hJ1 (by omega)
        omega
      have hj0r : j ∈ Finset.range (e + 1) := by
        rw [hjdef]
        exact Finset.mem_range.mpr (by have := min_le_right J e; omega)
      have hcap := cap_sum_le_content (p := p) (e := e) (J := J) (j := j) hp5 he a b
        hdeg2 hdeg hc0 hbt hdvd hJdef hjdef
      have hunc := unc_sum_le (p := p) (e := e) (a := a) (b := b) hp5 he hN hdeg hbt
      have hrow := localFactor_ge_row_and_content (p := p) (e := e) (j₀ := j) hp5 a b hj0 hj0r
      calc (∑ y ∈ uncSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2))
            + ∑ y ∈ capSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
          ≤ (∑ s ∈ Finset.range (capLevel p e),
                4 * (p : ℝ) ^ ((s : ℝ) / 2) * (if DLp p s a b then 1 else 0))
            + LFterm p e a b (max (capLevel p e) j) j := add_le_add hunc hcap
        _ = (∑ s ∈ Finset.range (capLevel p e), LFterm p e a b s 0)
            + LFterm p e a b (max (capLevel p e) j) j := by rw [← row_eq_unc hp5 a b]
        _ ≤ localFactor p e a b := hrow
    · -- ### `¬ p ∣ contAB`
      have hcap := cap_sum_le_noncontent (p := p) (e := e) (a := a) (b := b) hp5 he
        hdeg2 hdeg hbt hnot hsmall
      have hunc := unc_sum_le (p := p) (e := e) (a := a) (b := b) hp5 he hN hdeg hbt
      have hrow := localFactor_ge_row_succ (p := p) (e := e) (a := a) (b := b) hp5
      calc (∑ y ∈ uncSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2))
            + ∑ y ∈ capSet p e a b, (p : ℝ) ^ ((bval p e a b y : ℝ) / 2)
          ≤ (∑ s ∈ Finset.range (capLevel p e),
                4 * (p : ℝ) ^ ((s : ℝ) / 2) * (if DLp p s a b then 1 else 0))
            + LFterm p e a b (capLevel p e) 0 := add_le_add hunc hcap
        _ = (∑ s ∈ Finset.range (capLevel p e), LFterm p e a b s 0)
            + LFterm p e a b (capLevel p e) 0 := by rw [← row_eq_unc hp5 a b]
        _ = ∑ s ∈ Finset.range (capLevel p e + 1), LFterm p e a b s 0 :=
            (Finset.sum_range_succ (fun s => LFterm p e a b s 0) (capLevel p e)).symm
        _ ≤ localFactor p e a b := hrow
  -- case analysis on the configuration
  by_cases hdvd : p ∣ contAB a b
  · calc ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
        ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e (cubeLevel p e) a b := hAA
      _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b :=
          mul_le_mul_of_nonneg_left (hsum (Or.inl hdvd)) (Real.rpow_nonneg hpnn _)
  · by_cases hDL : DLp p (capLevel p e + 1) a b
    · by_cases he4 : 4 ≤ e
      · -- ### Lemma B (the saturated menu term)
        have hB := local_corr6_nonContent_sharp (p := p) (e := e) hp5 he4 χ hχ a b hdvd
        have hlf := localFactor_ge_cap_succ (p := p) (e := e) (a := a) (b := b) hp5 hDL
        have hsq : (p : ℝ) ^ (2 * (e : ℝ) / 3)
            = (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 6) := by
          rw [← Real.rpow_add hppos]
          congr 1
          ring
        have hstep : 12 * (p : ℝ) ^ ((e : ℝ) / 2) + 48 * (p : ℝ) ^ (2 * (e : ℝ) / 3)
            ≤ (p : ℝ) ^ ((e : ℝ) / 2) * (60 * (p : ℝ) ^ ((e : ℝ) / 6)) := by
          rw [hsq]
          have hX : (0:ℝ) ≤ (p : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_nonneg hpnn _
          have hY : (1:ℝ) ≤ (p : ℝ) ^ ((e : ℝ) / 6) := Real.one_le_rpow hp1 (by positivity)
          have hXY : (p : ℝ) ^ ((e : ℝ) / 2) * 1 ≤ (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ ((e : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left hY hX
          nlinarith [hX, hXY]
        exact le_trans (le_trans hB hstep)
          (mul_le_mul_of_nonneg_left hlf (Real.rpow_nonneg hpnn _))
      · exact le_trans hAA (mul_le_mul_of_nonneg_left
          (hsum (Or.inr ⟨hdvd, Or.inl (by omega)⟩)) (Real.rpow_nonneg hpnn _))
    · exact le_trans hAA (mul_le_mul_of_nonneg_left
        (hsum (Or.inr ⟨hdvd, Or.inr hDL⟩)) (Real.rpow_nonneg hpnn _))


end Work.LinnikBurgess
