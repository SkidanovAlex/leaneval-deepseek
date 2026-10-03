/-
# Auxiliary facts for the uniformly bounded randomised symbol of the lacunary bump family

This module collects the elementary (sorry-free) toolbox shared by
`Work.KMTPlan.A6.randSymb_sup_le_of_lipschitz` and the individual lemmas delegated for it:

* `norm_ee_eq_one`, `norm_ee_sub_le` — `ee x = exp (2πix)` has modulus one, and
  `‖ee a - ee b‖ ≤ 2π|a-b|` (the character `ee` is `Work.KMTAreas.A7.ee`);
* `lacunary_le_succ`, `lacunary_floor_mono` — a `Λ`-lacunary sequence with `Λ > 1` is increasing,
  hence `n ↦ ⌊a n⌋` is nondecreasing: this is what makes the order-interval structure of
  `lowSmallSet` (`lowSmallSet_conv`) usable;
* `logN_mono`, `pow_logN_le_max`, `lt_two_mul_pow_logN`, `two_pow_logN_le_two_mul_N`,
  `le_two_mul_pow_logN` — the dyadic scale `2 ^ Log N` used in `varphiN` is comparable to the
  integer scale `N` (`N ≤ 2 * 2^LogN` and `2^LogN ≤ 2 * N` for `N ≥ 1`);
* `card_jump_le_two` — the indicator of an order-convex set of `ℕ` has at most two jumps.

Everything is stated with fully qualified names, so the files of `KMTPlan/A6` that import this
module can use the facts directly.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## The character `ee` -/

theorem norm_ee_eq_one (x : ℝ) : ‖Work.KMTAreas.A7.ee x‖ = 1 := by
  have h : Work.KMTAreas.A7.ee x
      = Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I) := by
    simp only [Work.KMTAreas.A7.ee]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_ee_sub_le (a b : ℝ) :
    ‖Work.KMTAreas.A7.ee a - Work.KMTAreas.A7.ee b‖ ≤ 2 * Real.pi * |a - b| := by
  wlog hab : a ≤ b generalizing a b with H
  · rw [abs_sub_comm, norm_sub_rev]
    exact H b a (le_of_not_ge hab)
  have hd : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt Work.KMTAreas.A7.ee (2 * ↑Real.pi * Complex.I * Work.KMTAreas.A7.ee x)
        (Set.Icc a b) x := by
    intro x _
    have h := Work.KMTAreas.A7.hasDerivAt_ee_const_mul 1 x
    have h2 : HasDerivAt Work.KMTAreas.A7.ee
        (2 * ↑Real.pi * Complex.I * Work.KMTAreas.A7.ee x) x := by simpa using h
    exact h2.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b,
      ‖2 * ↑Real.pi * Complex.I * Work.KMTAreas.A7.ee x‖ ≤ 2 * Real.pi := by
    intro x _
    have hA : ‖2 * ↑Real.pi * Complex.I‖ = 2 * Real.pi := by
      have h := Work.KMTAreas.A7.norm_A 1
      simpa using h
    have hfin : ‖2 * ↑Real.pi * Complex.I * Work.KMTAreas.A7.ee x‖ = 2 * Real.pi := by
      rw [norm_mul, hA, norm_ee_eq_one, mul_one]
    exact hfin.le
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' hd hbound b
    (Set.right_mem_Icc.mpr hab)
  calc ‖Work.KMTAreas.A7.ee a - Work.KMTAreas.A7.ee b‖
      = ‖Work.KMTAreas.A7.ee b - Work.KMTAreas.A7.ee a‖ := norm_sub_rev _ _
    _ ≤ 2 * Real.pi * (b - a) := hmain
    _ = 2 * Real.pi * |a - b| := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring

theorem lacunary_le_succ (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (n : ℕ) : a n ≤ a (n + 1) := by
  have hpos : (0 : ℝ≥0) < a n := by
    by_contra h
    rw [not_lt, le_zero_iff] at h
    have h0 := ha n
    rw [h, div_zero] at h0
    exact absurd h0 (not_lt.mpr zero_le)
  have h2 : Λ * a n < a (n + 1) := by
    have h3 := mul_lt_mul_of_pos_right (ha n) hpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at h3
  calc a n = 1 * a n := (one_mul _).symm
    _ ≤ Λ * a n := by
        simpa using mul_le_mul_of_nonneg_right hΛ.le (zero_le : (0 : ℝ≥0) ≤ a n)
    _ ≤ a (n + 1) := h2.le

theorem lacunary_floor_mono (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) :
    Monotone (fun n => Nat.floor (a n)) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_floor (le_trans (Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ a n)) (lacunary_le_succ Λ hΛ ha n))

theorem logN_mono : Monotone Work.Analysis.EndVar.logN := by
  intro N M hNM
  simp only [Work.Analysis.EndVar.logN]
  exact_mod_cast Nat.log_mono_right (max_le_max_right _ hNM)

theorem pow_logN_le_max (N : ℕ) :
    (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ≤ (max N 2 : ℕ) := by
  have h := Nat.pow_log_le_self 2 (x := max N 2) (by positivity)
  have hcast : (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
      = ((2 : ℕ) ^ (Nat.log 2 (max N 2)) : ℝ) := by
    rw [show Work.Analysis.EndVar.logN N = ((Nat.log 2 (max N 2) : ℤ)) from rfl]
    rw [show (((Nat.log 2 (max N 2) : ℤ) : ℝ)) = ((Nat.log 2 (max N 2) : ℕ) : ℝ) by
      push_cast; ring]
    rw [Real.rpow_natCast]
    norm_cast
  rw [hcast]
  exact_mod_cast h

theorem lt_two_mul_pow_logN (N : ℕ) :
    (N : ℝ) < 2 * (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
  have h' : ((max N 2 : ℕ) : ℝ) < (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  have hbase : (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
      = ((2 : ℕ) ^ (Nat.log 2 (max N 2)) : ℝ) := by
    rw [show Work.Analysis.EndVar.logN N = ((Nat.log 2 (max N 2) : ℤ)) from rfl]
    rw [show (((Nat.log 2 (max N 2) : ℤ) : ℝ)) = ((Nat.log 2 (max N 2) : ℕ) : ℝ) by
      push_cast; ring]
    rw [Real.rpow_natCast]
    norm_cast
  have h2 : (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ)
      = 2 * (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) := by
    rw [pow_succ, hbase]
    push_cast
    ring
  have hNle : (N : ℝ) ≤ ((max N 2 : ℕ) : ℝ) := by exact_mod_cast le_max_left N 2
  rw [h2] at h'
  linarith

theorem two_pow_logN_le_two_mul_N {N : ℕ} (hN : 1 ≤ N) :
    (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ≤ 2 * N := by
  refine le_trans (pow_logN_le_max N) ?_
  have h : (max N 2 : ℕ) ≤ 2 * N := by omega
  exact_mod_cast h

theorem card_jump_le_two {T : Set ℕ}
    (hT : ∀ {n j m : ℕ}, n ≤ j → j ≤ m → n ∈ T → m ∈ T → j ∈ T) (K : ℕ)
    [DecidablePred (· ∈ T)] :
    ((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card ≤ 2 := by
  classical
  have hup : ((Finset.range K).filter (fun n => n ∉ T ∧ n + 1 ∈ T)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    have hp1 : p ∉ T := (Finset.mem_filter.mp hp).2.1
    have hp2 : p + 1 ∈ T := (Finset.mem_filter.mp hp).2.2
    have hq1 : q ∉ T := (Finset.mem_filter.mp hq).2.1
    have hq2 : q + 1 ∈ T := (Finset.mem_filter.mp hq).2.2
    rcases lt_or_gt_of_ne hpq with h | h
    · exact hq1 (hT (by omega) (by omega) hp2 hq2)
    · exact hp1 (hT (by omega) (by omega) hq2 hp2)
  have hdn : ((Finset.range K).filter (fun n => n ∈ T ∧ n + 1 ∉ T)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    have hp1 : p ∈ T := (Finset.mem_filter.mp hp).2.1
    have hp2 : p + 1 ∉ T := (Finset.mem_filter.mp hp).2.2
    have hq1 : q ∈ T := (Finset.mem_filter.mp hq).2.1
    have hq2 : q + 1 ∉ T := (Finset.mem_filter.mp hq).2.2
    rcases lt_or_gt_of_ne hpq with h | h
    · exact hp2 (hT (by omega) (by omega) hp1 hq1)
    · exact hq2 (hT (by omega) (by omega) hq1 hp1)
  calc ((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card
      ≤ (((Finset.range K).filter (fun n => n ∉ T ∧ n + 1 ∈ T))
          ∪ ((Finset.range K).filter (fun n => n ∈ T ∧ n + 1 ∉ T))).card := by
        apply Finset.card_le_card
        intro n hn
        obtain ⟨hnK, hniff⟩ := Finset.mem_filter.mp hn
        rw [Finset.mem_union]
        by_cases hnT : n ∈ T
        · right
          exact Finset.mem_filter.mpr ⟨hnK, hnT, fun h => hniff ⟨fun _ => h, fun _ => hnT⟩⟩
        · left
          exact Finset.mem_filter.mpr ⟨hnK, hnT,
            by_contra fun h => hniff ⟨fun h' => absurd h' hnT, fun h' => absurd h' h⟩⟩
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ 2 := by omega

end
end Work.KMTPlan.A6
