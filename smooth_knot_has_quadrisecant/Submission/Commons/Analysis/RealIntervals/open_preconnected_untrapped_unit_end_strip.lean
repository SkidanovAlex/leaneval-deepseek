import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Analysis.RealIntervals

/-- An open subset of ℝ containing `m`, all of whose points are `≤ m`, is impossible. -/
lemma isOpen_not_sup_mem {S : Set ℝ} (hS : IsOpen S) {m : ℝ} (hm : m ∈ S)
    (hsu : ∀ x ∈ S, x ≤ m) : False := by
  rcases Metric.isOpen_iff.mp hS m hm with ⟨ε, hε, hball⟩
  let y : ℝ := m + ε / 2
  have hyS : y ∈ S := hball (by
    dsimp [y]
    rw [Metric.mem_ball, Real.dist_eq]
    have hε2 : 0 < ε / 2 := by positivity
    rw [abs_of_pos (by linarith)]
    linarith)
  have : m < y := by dsimp [y]; linarith
  exact (not_le_of_gt this) (hsu y hyS)

/-- An open subset of ℝ containing `m`, all of whose points are `≥ m`, is impossible. -/
lemma isOpen_not_inf_mem {S : Set ℝ} (hS : IsOpen S) {m : ℝ} (hm : m ∈ S)
    (hin : ∀ x ∈ S, m ≤ x) : False := by
  rcases Metric.isOpen_iff.mp hS m hm with ⟨ε, hε, hball⟩
  let y : ℝ := m - ε / 2
  have hyS : y ∈ S := hball (by
    dsimp [y]
    rw [Metric.mem_ball, Real.dist_eq]
    have hyneg : y - m < 0 := by dsimp [y]; linarith
    rw [abs_of_neg hyneg]
    dsimp [y]
    linarith)
  have : y < m := by dsimp [y]; linarith
  exact (not_le_of_gt this) (hin y hyS)

lemma isOpen_nonempty_not_Icc {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) {a b : ℝ}
    (h : S = Icc a b) : False := by
  by_cases hab : a ≤ b
  · have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have hbS : b ∈ S := by simpa [h] using hbI
    exact isOpen_not_sup_mem hS hbS (by
      intro x hx
      have hx' : x ∈ Icc a b := by simpa [h] using hx
      exact hx'.2)
  · have : S = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Icc a b := by simpa [h] using hx
        have hb : b < a := lt_of_not_ge hab
        rcases hx' with ⟨h1, h2⟩
        linarith
      · intro hx
        simpa using hx
    rw [this] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

lemma isOpen_nonempty_not_Ico {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) {a b : ℝ}
    (h : S = Ico a b) : False := by
  by_cases hab : a < b
  · have haI : a ∈ Ico a b := ⟨le_rfl, hab⟩
    have haS : a ∈ S := by simpa [h] using haI
    exact isOpen_not_inf_mem hS haS (by
      intro x hx
      have hx' : x ∈ Ico a b := by simpa [h] using hx
      exact hx'.1)
  · have : S = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Ico a b := by simpa [h] using hx
        have hb : b ≤ a := le_of_not_gt hab
        rcases hx' with ⟨h1, h2⟩
        linarith
      · intro hx
        simpa using hx
    rw [this] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

lemma isOpen_nonempty_not_Ioc {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) {a b : ℝ}
    (h : S = Ioc a b) : False := by
  by_cases hab : a < b
  · have hbI : b ∈ Ioc a b := ⟨hab, le_rfl⟩
    have hbS : b ∈ S := by simpa [h] using hbI
    exact isOpen_not_sup_mem hS hbS (by
      intro x hx
      have hx' : x ∈ Ioc a b := by simpa [h] using hx
      exact hx'.2)
  · have : S = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Ioc a b := by simpa [h] using hx
        have hb : b ≤ a := le_of_not_gt hab
        rcases hx' with ⟨h1, h2⟩
        linarith
      · intro hx
        simpa using hx
    rw [this] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

lemma isOpen_nonempty_not_Ici {S : Set ℝ} (hS : IsOpen S) (_hne : S.Nonempty) {a : ℝ}
    (h : S = Ici a) : False := by
  have haI : a ∈ Ici a := by simpa using (le_rfl : a ≤ a)
  have haS : a ∈ S := by simpa [h] using haI
  exact isOpen_not_inf_mem hS haS (by
    intro x hx
    have hx' : x ∈ Ici a := by simpa [h] using hx
    exact hx')

lemma isOpen_nonempty_not_Iic {S : Set ℝ} (hS : IsOpen S) (_hne : S.Nonempty) {b : ℝ}
    (h : S = Iic b) : False := by
  have hbI : b ∈ Iic b := by simpa using (le_rfl : b ≤ b)
  have hbS : b ∈ S := by simpa [h] using hbI
  exact isOpen_not_sup_mem hS hbS (by
    intro x hx
    have hx' : x ∈ Iic b := by simpa [h] using hx
    exact hx')

/-- **The clean prefix-end strip (iii-a, real model)**: a nonempty open
preconnected subset `T` of the open unit interval `(0,1)` that is NOT
trapped in any strict sub-interval `(ε, 1−ε)` (`0 < ε < 1/2`) is exactly
a TERMINAL strip `(a,1)` (`0 ≤ a < 1`) or an INITIAL strip `(0,b)`
(`0 < b ≤ 1`) of `(0,1)` — it reaches an end of the unit interval, and
being an interval it reaches it cleanly.

Proof outline: an open preconnected nonempty subset of ℝ is one of
`Ioo a b`, `Ioi a`, `Iio b`, `univ` (e.g. via
`open_preconnected_nonempty_ℝ_shape`/`IsPreconnected.mem_intervals`);
the last three contradict `T ⊆ (0,1)` (rays are unbounded, `univ`
contains `2`/points outside `(0,1)`) — so `T = Ioo a b` with, since
`T ⊆ (0,1)`: `0 ≤ a`, `b ≤ 1` (if `a < 0`, the interval contains a
negative point `z` (e.g. `a/2` when `b > 0`, or any element when
`b ≤ 0`), contradicting `T ⊆ (0,1)`; dually for `b > 1`); `a < b` from
nonemptiness.  If `0 < a` AND `b < 1` then `T = Ioo a b` is trapped in
`(ε, 1−ε)` for `ε := min a (1 − b) / 2` (check `0 < ε < 1/2`, `ε ≤ a`,
`b ≤ 1 − ε`), contradicting `huntrapped`; hence `a = 0` (second
disjunct, `b := b`, `0 < b` since `a = 0 < b`) or `b = 1` (first
disjunct, `a := a`, `a < 1` since `a < b = 1`). -/
theorem open_preconnected_untrapped_unit_end_strip {T : Set ℝ}
    (hT01 : T ⊆ Set.Ioo 0 1) (hTopen : IsOpen T) (hpc : IsPreconnected T)
    (hne : T.Nonempty)
    (huntrapped : ¬ ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ T ⊆ Set.Ioo ε (1 - ε)) :
    (∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ T = Set.Ioo a 1) ∨
      (∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ T = Set.Ioo 0 b) := by
  have hbdd_below : BddBelow T :=
    ⟨0, by intro x hx; exact le_of_lt (Set.mem_Ioo.mp (hT01 hx)).1⟩
  have hbdd_above : BddAbove T :=
    ⟨1, by intro x hx; exact le_of_lt (Set.mem_Ioo.mp (hT01 hx)).2⟩
  have hinf0 : 0 ≤ sInf T := by
    exact le_csInf hne (by intro x hx; exact le_of_lt (Set.mem_Ioo.mp (hT01 hx)).1)
  have hsup1 : sSup T ≤ 1 := by
    exact csSup_le hne (by intro x hx; exact le_of_lt (Set.mem_Ioo.mp (hT01 hx)).2)
  rcases hpc.mem_intervals with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact False.elim (isOpen_nonempty_not_Icc hTopen hne h1)
  · exact False.elim (isOpen_nonempty_not_Ico hTopen hne h2)
  · exact False.elim (isOpen_nonempty_not_Ioc hTopen hne h3)
  · have hab : sInf T < sSup T := by
      rcases hne with ⟨x, hx⟩
      have hx' : x ∈ Ioo (sInf T) (sSup T) := by
          rw [h4] at hx
          exact hx
      exact lt_trans (Set.mem_Ioo.mp hx').1 (Set.mem_Ioo.mp hx').2
    by_cases hb1 : sSup T = 1
    · left
      refine ⟨sInf T, hinf0, ?_, ?_⟩
      · rw [hb1] at hab
        exact hab
      · simpa [hb1] using h4
    · by_cases ha0 : sInf T = 0
      · right
        refine ⟨sSup T, ?_, hsup1, ?_⟩
        · rw [ha0] at hab
          exact hab
        · simpa [ha0] using h4
      · exfalso
        have h0inf : 0 < sInf T := lt_of_le_of_ne hinf0 (by intro h; exact ha0 h.symm)
        have hsup_lt : sSup T < 1 := lt_of_le_of_ne hsup1 hb1
        let ε : ℝ := min (sInf T) (1 - sSup T) / 2
        apply huntrapped
        refine ⟨ε, ?_, ?_, ?_⟩
        · have hminpos : 0 < min (sInf T) (1 - sSup T) := by
            exact lt_min h0inf (by linarith)
          dsimp [ε]
          exact div_pos hminpos (by norm_num : (0 : ℝ) < 2)
        · have hinf1 : sInf T < 1 := lt_of_lt_of_le hab hsup1
          have hmin1 : min (sInf T) (1 - sSup T) < 1 :=
            lt_of_le_of_lt (min_le_left _ _) hinf1
          dsimp [ε]
          exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hmin1
        · intro x hx
          have hε_inf : ε < sInf T := by
            dsimp [ε]
            have hma : min (sInf T) (1 - sSup T) ≤ sInf T := min_le_left _ _
            have hma2 : min (sInf T) (1 - sSup T) / 2 ≤ sInf T / 2 := by
              exact div_le_div_of_nonneg_right hma (by norm_num : (0 : ℝ) ≤ 2)
            exact lt_of_le_of_lt hma2 (half_lt_self h0inf)
          have hε_sup : ε < 1 - sSup T := by
            dsimp [ε]
            have hmb : min (sInf T) (1 - sSup T) ≤ 1 - sSup T := min_le_right _ _
            have hmb2 : min (sInf T) (1 - sSup T) / 2 ≤ (1 - sSup T) / 2 := by
              exact div_le_div_of_nonneg_right hmb (by norm_num : (0 : ℝ) ≤ 2)
            exact lt_of_le_of_lt hmb2 (half_lt_self (by linarith))
          have hxI : x ∈ Ioo (sInf T) (sSup T) := by
            rw [h4] at hx
            exact hx
          have hεx : ε < x := lt_trans hε_inf (Set.mem_Ioo.mp hxI).1
          have hxε : x < 1 - ε := by
            exact lt_trans (Set.mem_Ioo.mp hxI).2 (by linarith)
          exact ⟨hεx, hxε⟩
  · exact False.elim (isOpen_nonempty_not_Ici hTopen hne h5)
  · exfalso
    rcases hne with ⟨y, hy⟩
    have hyT01 : y ∈ Ioo 0 1 := hT01 hy
    have hyplusT : y + 1 ∈ T := by
      rw [h6]
      exact Set.mem_Ioi.mpr (by
        have hyinf : sInf T ≤ y := csInf_le hbdd_below hy
        linarith)
    have hyplus01 : y + 1 ∈ Ioo 0 1 := hT01 hyplusT
    have hy0 : 0 < y := (Set.mem_Ioo.mp hyT01).1
    have hyplus_lt1 : y + 1 < 1 := (Set.mem_Ioo.mp hyplus01).2
    linarith
  · exact False.elim (isOpen_nonempty_not_Iic hTopen hne h7)
  · exfalso
    rcases hne with ⟨y, hy⟩
    have hyT01 : y ∈ Ioo 0 1 := hT01 hy
    have hyminusT : y - 1 ∈ T := by
      rw [h8]
      exact Set.mem_Iio.mpr (by
        have hysup : y ≤ sSup T := le_csSup hbdd_above hy
        linarith)
    have hyminus01 : y - 1 ∈ Ioo 0 1 := hT01 hyminusT
    have hy1 : y < 1 := (Set.mem_Ioo.mp hyT01).2
    have hyminus_gt0 : 0 < y - 1 := (Set.mem_Ioo.mp hyminus01).1
    linarith
  · exfalso
    have h2T : (2 : ℝ) ∈ T := by rw [h9]; trivial
    have h201 : (2 : ℝ) ∈ Ioo 0 1 := hT01 h2T
    have hlt : (2 : ℝ) < 1 := (Set.mem_Ioo.mp h201).2
    norm_num at hlt
  · exfalso
    rw [h10] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

end Commons.Analysis.RealIntervals