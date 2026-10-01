import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.trig_low
import Submission.Work.OffAxis.Tf72One.exp_bounds
import Submission.Work.OffAxis.Tf72One.exp_bounds_lo

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables.OffAxis

/-! ## Rational enclosures of `exp (2s)`, `cos (2σ)`, `sin (2σ)` at the grid points

The nine `s`-values of the grid give `2s ∈ {0, 3/10, 3/5, 9/10, 6/5, 3/2, 9/5, 21/10, 17/8}`,
which are exactly the arguments of `exp_bounds_lo` (lower) and `exp_bounds` (upper); the three
`σ`-values give `2σ ∈ {3/2, 7/2, 5}`, the arguments of `trig_low`.  -/
private lemma corner_exp_0 :
    (1 : ℝ) ≤ Real.exp (2 * (0)) ∧ Real.exp (2 * (0)) ≤ (1 : ℝ) := by
  obtain ⟨l, _, _, _, _, _, _, _, _⟩ := exp_bounds_lo
  obtain ⟨u, _, _, _, _, _, _, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (0) = 0 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_1 :
    (134985/100000 : ℝ) ≤ Real.exp (2 * (3/20)) ∧ Real.exp (2 * (3/20)) ≤ (134986/100000 : ℝ) := by
  obtain ⟨_, l, _, _, _, _, _, _, _⟩ := exp_bounds_lo
  obtain ⟨_, u, _, _, _, _, _, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (3/20) = 3/10 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_2 :
    (182211/100000 : ℝ) ≤ Real.exp (2 * (3/10)) ∧ Real.exp (2 * (3/10)) ≤ (182212/100000 : ℝ) := by
  obtain ⟨_, _, l, _, _, _, _, _, _⟩ := exp_bounds_lo
  obtain ⟨_, _, u, _, _, _, _, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (3/10) = 3/5 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_3 :
    (245960/100000 : ℝ) ≤ Real.exp (2 * (9/20)) ∧ Real.exp (2 * (9/20)) ≤ (245961/100000 : ℝ) := by
  obtain ⟨_, _, _, l, _, _, _, _, _⟩ := exp_bounds_lo
  obtain ⟨_, _, _, u, _, _, _, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (9/20) = 9/10 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_4 :
    (332011/100000 : ℝ) ≤ Real.exp (2 * (3/5)) ∧ Real.exp (2 * (3/5)) ≤ (332012/100000 : ℝ) := by
  obtain ⟨_, _, _, _, l, _, _, _, _⟩ := exp_bounds_lo
  obtain ⟨_, _, _, _, u, _, _, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (3/5) = 6/5 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_5 :
    (448168/100000 : ℝ) ≤ Real.exp (2 * (3/4)) ∧ Real.exp (2 * (3/4)) ≤ (448170/100000 : ℝ) := by
  obtain ⟨_, _, _, _, _, l, _, _, _⟩ := exp_bounds_lo
  obtain ⟨_, _, _, _, _, u, _, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (3/4) = 3/2 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_6 :
    (604964/100000 : ℝ) ≤ Real.exp (2 * (9/10)) ∧ Real.exp (2 * (9/10)) ≤ (604965/100000 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, l, _, _⟩ := exp_bounds_lo
  obtain ⟨_, _, _, _, _, _, u, _, _⟩ := exp_bounds
  have h : (2:ℝ) * (9/10) = 9/5 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_7 :
    (816616/100000 : ℝ) ≤ Real.exp (2 * (21/20)) ∧ Real.exp (2 * (21/20)) ≤ (816618/100000 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, l, _⟩ := exp_bounds_lo
  obtain ⟨_, _, _, _, _, _, _, u, _⟩ := exp_bounds
  have h : (2:ℝ) * (21/20) = 21/10 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_exp_8 :
    (837289/100000 : ℝ) ≤ Real.exp (2 * (17/16)) ∧ Real.exp (2 * (17/16)) ≤ (83729/10000 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, l⟩ := exp_bounds_lo
  obtain ⟨_, _, _, _, _, _, _, _, u⟩ := exp_bounds
  have h : (2:ℝ) * (17/16) = 17/8 := by norm_num
  exact ⟨by rw [h]; exact l, by rw [h]; exact u⟩
private lemma corner_trig_1 :
    (707362/10000000 : ℝ) ≤ Real.cos (2 * (3/4)) ∧ Real.cos (2 * (3/4)) ≤ (707383/10000000 : ℝ) ∧
      (9974939/10000000 : ℝ) ≤ Real.sin (2 * (3/4)) ∧ Real.sin (2 * (3/4)) ≤ (498748/500000 : ℝ) := by
  obtain ⟨c0, c1, t0, t1, _, _, _, _, _, _, _, _⟩ := trig_low
  have h : (2:ℝ) * (3/4) = 3/2 := by norm_num
  exact ⟨by rw [h]; exact c0, by rw [h]; exact c1, by rw [h]; exact t0, by rw [h]; exact t1⟩
private lemma corner_trig_2 :
    (-9365567/10000000 : ℝ) ≤ Real.cos (2 * (7/4)) ∧ Real.cos (2 * (7/4)) ≤ (-9363566/10000000 : ℝ) ∧
      (-3508833/10000000 : ℝ) ≤ Real.sin (2 * (7/4)) ∧ Real.sin (2 * (7/4)) ≤ (-3506832/10000000 : ℝ) := by
  obtain ⟨_, _, _, _, c0, c1, t0, t1, _, _, _, _⟩ := trig_low
  have h : (2:ℝ) * (7/4) = 7/2 := by norm_num
  exact ⟨by rw [h]; exact c0, by rw [h]; exact c1, by rw [h]; exact t0, by rw [h]; exact t1⟩
private lemma corner_trig_3 :
    (2835621/10000000 : ℝ) ≤ Real.cos (2 * (5/2)) ∧ Real.cos (2 * (5/2)) ≤ (2837622/10000000 : ℝ) ∧
      (-9590243/10000000 : ℝ) ≤ Real.sin (2 * (5/2)) ∧ Real.sin (2 * (5/2)) ≤ (-9588242/10000000 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, c0, c1, t0, t1⟩ := trig_low
  have h : (2:ℝ) * (5/2) = 5 := by norm_num
  exact ⟨by rw [h]; exact c0, by rw [h]; exact c1, by rw [h]; exact t0, by rw [h]; exact t1⟩
/-- The certified corner bound plus a rational evaluation of the corner expression. -/
private lemma corner_case (s σ Elo Ehi c0 c1 t0 t1 : ℝ) (hs0 : 0 ≤ s) (hσ : σ ≠ 0)
    (hElo : Elo ≤ Real.exp (2 * s)) (hEhi : Real.exp (2 * s) ≤ Ehi)
    (hc0 : c0 ≤ Real.cos (2 * σ)) (hc1 : Real.cos (2 * σ) ≤ c1)
    (ht0 : t0 ≤ Real.sin (2 * σ)) (ht1 : Real.sin (2 * σ) ≤ t1)
    (hnum : cornerB s σ Elo Ehi c0 c1 t0 t1 ≤ (-193/1000 : ℝ)) :
    Isub s σ ≤ (-193/1000 : ℝ) :=
  (Isub_le_cornerB s σ Elo Ehi c0 c1 t0 t1 hs0 hσ hElo hEhi hc0 hc1 ht0 ht1).trans hnum

/-- Grid corner bound (small `σ`).  For `s` in the nine-point grid
`{0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16}` and `σ ∈ {3/4, 7/4, 5/2}` one has
`Isub s σ ≤ -193/1000`.

Proof route: `Isub_le_cornerB s σ Elo Ehi c0 c1 t0 t1` (from `Tf72One.Core`) with `Elo`, `Ehi` the
`exp_bounds_lo` / `exp_bounds` conjuncts for `2s`, and `c0,c1,t0,t1` the `trig_low` conjuncts for the
relevant `2σ ∈ {3/2, 7/2, 5}`; then `norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]`
(or `nlinarith`) closes the resulting rational inequality.  At `σ = 3/4` the coefficients are large,
so both the upper and the lower `exp` bound are needed for the bound to be sharp enough. -/
theorem corner_low (s σ : ℝ)
    (hs : s ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hσ : σ ∈ ({3/4, 7/4, 5/2} : Finset ℝ)) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ (-193/1000 : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs hσ
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- s = 0
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (0) (3/4) (1) (1) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_0.1 corner_exp_0.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (0) (7/4) (1) (1) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_0.1 corner_exp_0.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (0) (5/2) (1) (1) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_0.1 corner_exp_0.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 3/20
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (3/20) (3/4) (134985/100000) (134986/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_1.1 corner_exp_1.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/20) (7/4) (134985/100000) (134986/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_1.1 corner_exp_1.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/20) (5/2) (134985/100000) (134986/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_1.1 corner_exp_1.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 3/10
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (3/10) (3/4) (182211/100000) (182212/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_2.1 corner_exp_2.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/10) (7/4) (182211/100000) (182212/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_2.1 corner_exp_2.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/10) (5/2) (182211/100000) (182212/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_2.1 corner_exp_2.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 9/20
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (9/20) (3/4) (245960/100000) (245961/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_3.1 corner_exp_3.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (9/20) (7/4) (245960/100000) (245961/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_3.1 corner_exp_3.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (9/20) (5/2) (245960/100000) (245961/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_3.1 corner_exp_3.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 3/5
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (3/5) (3/4) (332011/100000) (332012/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_4.1 corner_exp_4.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/5) (7/4) (332011/100000) (332012/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_4.1 corner_exp_4.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/5) (5/2) (332011/100000) (332012/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_4.1 corner_exp_4.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 3/4
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (3/4) (3/4) (448168/100000) (448170/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_5.1 corner_exp_5.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/4) (7/4) (448168/100000) (448170/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_5.1 corner_exp_5.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (3/4) (5/2) (448168/100000) (448170/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_5.1 corner_exp_5.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 9/10
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (9/10) (3/4) (604964/100000) (604965/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_6.1 corner_exp_6.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (9/10) (7/4) (604964/100000) (604965/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_6.1 corner_exp_6.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (9/10) (5/2) (604964/100000) (604965/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_6.1 corner_exp_6.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 21/20
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (21/20) (3/4) (816616/100000) (816618/100000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_7.1 corner_exp_7.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (21/20) (7/4) (816616/100000) (816618/100000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_7.1 corner_exp_7.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (21/20) (5/2) (816616/100000) (816618/100000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_7.1 corner_exp_7.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
  · -- s = 17/16
    rcases hσ with rfl | rfl | rfl
    · exact corner_case (17/16) (3/4) (837289/100000) (83729/10000) (707362/10000000) (707383/10000000) (9974939/10000000) (498748/500000)
        (by norm_num) (by norm_num) corner_exp_8.1 corner_exp_8.2
        corner_trig_1.1 corner_trig_1.2.1 corner_trig_1.2.2.1 corner_trig_1.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (17/16) (7/4) (837289/100000) (83729/10000) (-9365567/10000000) (-9363566/10000000) (-3508833/10000000) (-3506832/10000000)
        (by norm_num) (by norm_num) corner_exp_8.1 corner_exp_8.2
        corner_trig_2.1 corner_trig_2.2.1 corner_trig_2.2.2.1 corner_trig_2.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])
    · exact corner_case (17/16) (5/2) (837289/100000) (83729/10000) (2835621/10000000) (2837622/10000000) (-9590243/10000000) (-9588242/10000000)
        (by norm_num) (by norm_num) corner_exp_8.1 corner_exp_8.2
        corner_trig_3.1 corner_trig_3.2.1 corner_trig_3.2.2.1 corner_trig_3.2.2.2
        (by norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72])

end Work.OffAxis.Tf72One
