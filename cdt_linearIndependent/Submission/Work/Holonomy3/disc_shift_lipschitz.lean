import Mathlib
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.count_le_of_disc
import Submission.Work.Holonomy3.koksma_monotone
import Submission.Work.Holonomy3.cnt_le_cnt_of
import Submission.Work.Holonomy3.card_filter_add_card_filter_le

/-!
# The box discrepancy is Lipschitz for small shifts of the points

`Work.Holonomy3.disc_shift_lipschitz`: moving every point of a configuration `t` of `d` points of
`[0,1]` by at most `η` changes the box discrepancy (`Submission.CDT.Discrepancy.disc`) by at most
`2·η + 1/d`.

In fact the estimate below proves the stronger bound `2·η` (without the `1/d`); the statement
carries the extra `1/d` for use downstream.

The argument is the standard "boundary layer" estimate: the points that can enter or leave a
half-open interval `[a,b)` are those within `η` of `a` or of `b`.  The two directions use
`cnt u a b ≤ cnt t (max (a-η) 0) (b+η)` (points entering) and `cnt t (a+η) (b-η) ≤ cnt u a b`
(points leaving).  The right endpoint `1` needs care: it is not counted by `disc` at all (the
intervals are half-open) but `t` may have points exactly there, and those are handled by the
complement count `cnt u a b + cnt t 0 (max (a-η) 0) ≤ d`.
-/

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

attribute [local instance] Classical.propDecidable

/-- `cnt` vanishes on an empty (inverted) interval. -/
lemma cnt_eq_zero_of_le {n : ℕ} (t : Fin n → ℝ) {a b : ℝ} (h : b ≤ a) : cnt t a b = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.mpr fun i _ => ?_
  simp only [Set.mem_Ico, not_and]
  intro h1 h2
  linarith

/-- **The Lipschitz estimate, pointwise form.**  If `t` has all of its values in `[0,1]` and `u`
is obtained from `t` by moving every point by at most `η ≥ 0`, then for every half-open interval
`[a,b) ⊆ [0,1]` the deviation of the empirical count of `u` on `[a,b)` differs from that of `t`
by at most `2η`.  (The hypothesis that `u` takes its values in `[0,1]` is not needed here; it is
kept so that the lemma reads symmetrically.) -/
lemma abs_sub_cnt_div_le_disc_add {n : ℕ} (t u : Fin n → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (hu : ∀ j, u j ∈ Set.Icc 0 1)
    {η : ℝ} (hη : 0 ≤ η) (h : ∀ j, |u j - t j| ≤ η)
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    |(b - a) - (cnt u a b : ℝ) / (n : ℝ)| ≤ disc t + 2 * η := by
  have hdt : 0 ≤ disc t := disc_nonneg t
  -- Direction 1: the length exceeds the count by at most `disc t + 2η`.
  -- Points of `t` in `[a+η, b-η)` are counted by `u` on `[a,b)`.
  have lower : (b - a) - (cnt u a b : ℝ) / (n : ℝ) ≤ disc t + 2 * η := by
    have hnat : cnt t (a + η) (b - η) ≤ cnt u a b :=
      cnt_le_cnt_of u t fun i hi => by
        simp only [Set.mem_Ico] at hi ⊢
        obtain ⟨hi1, hi2⟩ := hi
        have habs := abs_le.mp (h i)
        exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have hdiv : (cnt t (a + η) (b - η) : ℝ) / (n : ℝ) ≤ (cnt u a b : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hnat) (Nat.cast_nonneg n)
    have hstep : (b - a) - (cnt u a b : ℝ) / (n : ℝ)
        ≤ (b - a) - (cnt t (a + η) (b - η) : ℝ) / (n : ℝ) := by linarith
    refine le_trans hstep ?_
    by_cases hcase : a + η ≤ b - η
    · have hbnd := abs_sub_cnt_div_le_disc (disc t) t le_rfl (a := a + η) (b := b - η)
        (by linarith) hcase (by linarith)
      have hbd := (abs_le.mp hbnd).2
      linarith
    · have hzero : cnt t (a + η) (b - η) = 0 :=
        cnt_eq_zero_of_le t (le_of_lt (not_le.mp hcase))
      rw [hzero]
      simp only [Nat.cast_zero, zero_div, sub_zero]
      linarith [not_le.mp hcase, hdt]
  -- Direction 2: the count exceeds the length by at most `disc t + 2η`.
  -- Points of `u` in `[a,b)` come from points of `t` in `[max (a-η) 0, b+η)`.
  have upper : (cnt u a b : ℝ) / (n : ℝ) - (b - a) ≤ disc t + 2 * η := by
    by_cases hb : b + η ≤ 1
    · -- No point of `t` can sit at the right endpoint: enlarge the interval.
      have hnat : cnt u a b ≤ cnt t (max (a - η) 0) (b + η) :=
        cnt_le_cnt_of t u fun i hi => by
          simp only [Set.mem_Ico] at hi ⊢
          obtain ⟨hi1, hi2⟩ := hi
          have habs := abs_le.mp (h i)
          exact ⟨max_le_iff.mpr ⟨by linarith [habs.1], (ht i).1⟩, by linarith [habs.2]⟩
      have hdiv : (cnt u a b : ℝ) / (n : ℝ)
          ≤ (cnt t (max (a - η) 0) (b + η) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hnat) (Nat.cast_nonneg n)
      have hA0 : 0 ≤ max (a - η) 0 := le_max_right _ _
      have hAB : max (a - η) 0 ≤ b + η := max_le_iff.mpr ⟨by linarith, by linarith⟩
      have hbnd := abs_sub_cnt_div_le_disc (disc t) t le_rfl (a := max (a - η) 0) (b := b + η)
        hA0 hAB hb
      have hbd := (abs_le.mp hbnd).1
      have hBA : (b + η) - max (a - η) 0 ≤ (b - a) + 2 * η := by
        rcases le_or_gt η a with ha | ha
        · rw [max_eq_left (by linarith : (0 : ℝ) ≤ a - η)]
          linarith
        · rw [max_eq_right (by linarith : a - η ≤ (0 : ℝ))]
          linarith
      linarith
    · -- Points of `t` may sit exactly at `1`; count them through the complement.
      rw [not_le] at hb
      have hkey : ∀ i : Fin n, u i ∈ Set.Ico a b → ¬ (t i ∈ Set.Ico 0 (max (a - η) 0)) := by
        intro i hi hj
        simp only [Set.mem_Ico] at hi hj
        obtain ⟨hi1, hi2⟩ := hi
        obtain ⟨hj1, hj2⟩ := hj
        have habs := abs_le.mp (h i)
        rcases le_or_gt η a with ha | ha
        · rw [max_eq_left (by linarith : (0 : ℝ) ≤ a - η)] at hj2
          linarith [habs.2]
        · rw [max_eq_right (by linarith : a - η ≤ (0 : ℝ))] at hj2
          linarith
      have hcard : cnt u a b + cnt t 0 (max (a - η) 0) ≤ n := by
        have hle := card_filter_add_card_filter_le
          (p := fun i : Fin n => u i ∈ Set.Ico a b)
          (q := fun i : Fin n => t i ∈ Set.Ico 0 (max (a - η) 0)) hkey
        simpa only [cnt] using hle
      have hreal : (cnt u a b : ℝ) + (cnt t 0 (max (a - η) 0) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hcard
      have hle : (cnt u a b : ℝ) / (n : ℝ)
          ≤ 1 - (cnt t 0 (max (a - η) 0) : ℝ) / (n : ℝ) := by
        have hsub : (cnt u a b : ℝ) ≤ (n : ℝ) - (cnt t 0 (max (a - η) 0) : ℝ) := by
          linarith
        have hdiv := div_le_div_of_nonneg_right hsub (Nat.cast_nonneg n)
        rw [sub_div] at hdiv
        have hnn : (n : ℝ) / (n : ℝ) ≤ 1 := div_self_le_one _
        linarith
      have hA0 : 0 ≤ max (a - η) 0 := le_max_right _ _
      have hA1 : max (a - η) 0 ≤ 1 := max_le_iff.mpr ⟨by linarith, by norm_num⟩
      have hbnd := abs_sub_cnt_div_le_disc (disc t) t le_rfl (a := 0) (b := max (a - η) 0)
        le_rfl hA0 hA1
      have hbd := (abs_le.mp hbnd).2
      have haux : 1 - max (a - η) 0 - (b - a) ≤ 2 * η := by
        rcases le_or_gt η a with ha | ha
        · rw [max_eq_left (by linarith : (0 : ℝ) ≤ a - η)]
          linarith
        · rw [max_eq_right (by linarith : a - η ≤ (0 : ℝ))]
          linarith
      linarith
  rw [abs_le]
  exact ⟨by linarith, lower⟩

/-- **The Lipschitz estimate, `disc` form.**  If `t` and `u` are configurations of `n` points of
`[0,1]` and `|u j - t j| ≤ η` for all `j`, then `disc u ≤ disc t + 2η`. -/
lemma disc_le_disc_add {n : ℕ} (t u : Fin n → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hu : ∀ j, u j ∈ Set.Icc 0 1) {η : ℝ} (hη : 0 ≤ η) (h : ∀ j, |u j - t j| ≤ η) :
    disc u ≤ disc t + 2 * η := by
  rw [disc]
  refine csSup_le (disc_nonempty u) ?_
  rintro y ⟨p, hp, rfl⟩
  exact abs_sub_cnt_div_le_disc_add t u ht hu hη h hp.1 hp.2.1 hp.2.2

/-- The box discrepancy (`Submission.CDT.Discrepancy.disc`) of `d` points of `[0,1]` changes by at
most `2·η + 1/d` when every point is moved by at most `η` (`0 ≤ η`). -/
theorem disc_shift_lipschitz {d : ℕ} (t u : Fin d → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hu : ∀ j, u j ∈ Set.Icc 0 1) {η : ℝ} (hη : 0 ≤ η) (h : ∀ j, |u j - t j| ≤ η) :
    |Submission.CDT.Discrepancy.disc u - Submission.CDT.Discrepancy.disc t| ≤ 2 * η + 1 / (d : ℝ) := by
  have h1 : disc u ≤ disc t + 2 * η := disc_le_disc_add t u ht hu hη h
  have h2 : disc t ≤ disc u + 2 * η :=
    disc_le_disc_add u t hu ht hη fun j => by rw [abs_sub_comm]; exact h j
  have hpos : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Work.Holonomy3
