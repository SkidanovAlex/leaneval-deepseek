import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.trig_top
import Submission.Work.OffAxis.Tf72One.exp_bounds

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables.OffAxis

/-! ## Rational `exp` upper bounds at `2 * s` for the nine grid points -/

/-- `simpa`-friendly restatement of `exp_bounds` at the argument `2 * s`. -/

private lemma expHi_0 : Real.exp (2*((0:ℝ))) ≤ (1:ℝ) := by
  have h : (2:ℝ)*(0) = 0 := by norm_num
  rw [h]
  exact exp_bounds.1


private lemma expHi_3_20 : Real.exp (2*((3/20:ℝ))) ≤ (134986/100000:ℝ) := by
  have h : (2:ℝ)*(3/20) = 3/10 := by norm_num
  rw [h]
  exact exp_bounds.2.1


private lemma expHi_3_10 : Real.exp (2*((3/10:ℝ))) ≤ (182212/100000:ℝ) := by
  have h : (2:ℝ)*(3/10) = 3/5 := by norm_num
  rw [h]
  exact exp_bounds.2.2.1


private lemma expHi_9_20 : Real.exp (2*((9/20:ℝ))) ≤ (245961/100000:ℝ) := by
  have h : (2:ℝ)*(9/20) = 9/10 := by norm_num
  rw [h]
  exact exp_bounds.2.2.2.1


private lemma expHi_3_5 : Real.exp (2*((3/5:ℝ))) ≤ (332012/100000:ℝ) := by
  have h : (2:ℝ)*(3/5) = 6/5 := by norm_num
  rw [h]
  exact exp_bounds.2.2.2.2.1


private lemma expHi_3_4 : Real.exp (2*((3/4:ℝ))) ≤ (448170/100000:ℝ) := by
  have h : (2:ℝ)*(3/4) = 3/2 := by norm_num
  rw [h]
  exact exp_bounds.2.2.2.2.2.1


private lemma expHi_9_10 : Real.exp (2*((9/10:ℝ))) ≤ (604965/100000:ℝ) := by
  have h : (2:ℝ)*(9/10) = 9/5 := by norm_num
  rw [h]
  exact exp_bounds.2.2.2.2.2.2.1


private lemma expHi_21_20 : Real.exp (2*((21/20:ℝ))) ≤ (816618/100000:ℝ) := by
  have h : (2:ℝ)*(21/20) = 21/10 := by norm_num
  rw [h]
  exact exp_bounds.2.2.2.2.2.2.2.1


private lemma expHi_17_16 : Real.exp (2*((17/16:ℝ))) ≤ (83729/10000:ℝ) := by
  have h : (2:ℝ)*(17/16) = 17/8 := by norm_num
  rw [h]
  exact exp_bounds.2.2.2.2.2.2.2.2


/-! ## Rational `cos`/`sin` enclosures at `2 * σ` for the four `σ` -/


private lemma trigHi_22_5 :
    (-8111931/10000000 : ℝ) ≤ Real.cos (2*((22/5:ℝ))) ∧
      Real.cos (2*((22/5:ℝ))) ≤ (-810993/1000000 : ℝ) ∧
      (5848171/10000000 : ℝ) ≤ Real.sin (2*((22/5:ℝ))) ∧
      Real.sin (2*((22/5:ℝ))) ≤ (5850173/10000000 : ℝ) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ :=
    trig_top
  have h : (2:ℝ)*(22/5) = 44/5 := by norm_num
  rw [h]
  exact ⟨t1, t2, t3, t4⟩


private lemma trigHi_23_5 :
    (-9749437/10000000 : ℝ) ≤ Real.cos (2*((23/5:ℝ))) ∧
      Real.cos (2*((23/5:ℝ))) ≤ (-9747436/10000000 : ℝ) ∧
      (2227899/10000000 : ℝ) ≤ Real.sin (2*((23/5:ℝ))) ∧
      Real.sin (2*((23/5:ℝ))) ≤ (22299/100000 : ℝ) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ :=
    trig_top
  have h : (2:ℝ)*(23/5) = 46/5 := by norm_num
  rw [h]
  exact ⟨t5, t6, t7, t8⟩


private lemma trigHi_24_5 :
    (-9847879/10000000 : ℝ) ≤ Real.cos (2*((24/5:ℝ))) ∧
      Real.cos (2*((24/5:ℝ))) ≤ (-9845877/10000000 : ℝ) ∧
      (-1744269/10000000 : ℝ) ≤ Real.sin (2*((24/5:ℝ))) ∧
      Real.sin (2*((24/5:ℝ))) ≤ (-1742267/10000000 : ℝ) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ :=
    trig_top
  have h : (2:ℝ)*(24/5) = 48/5 := by norm_num
  rw [h]
  exact ⟨t9, t10, t11, t12⟩


private lemma trigHi_10 :
    (-8391716/10000000 : ℝ) ≤ Real.cos (2*((5:ℝ))) ∧
      Real.cos (2*((5:ℝ))) ≤ (-8389711/10000000 : ℝ) ∧
      (-5441213/10000000 : ℝ) ≤ Real.sin (2*((5:ℝ))) ∧
      Real.sin (2*((5:ℝ))) ≤ (-5439208/10000000 : ℝ) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ :=
    trig_top
  have h : (2:ℝ)*(5) = 10 := by norm_num
  rw [h]
  exact ⟨t13, t14, t15, t16⟩


/-- Grid corner bound (largest `σ`).  For `s` in the nine-point grid
`{0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16}` and `σ ∈ {22/5, 23/5, 24/5, 5}` one has
`Isub s σ ≤ 1/500`.

Same method as `corner_low`, with the `trig_top` conjuncts at `2σ ∈ {44/5, 46/5, 48/5, 10}`; the true
values here are tiny (down to `≈ -1.8·10⁻⁴`), so the `cos`/`sin` enclosures must be applied
faithfully (not replaced by `|cos|,|sin| ≤ 1`). -/
theorem corner_top (s σ : ℝ)
    (hs : s ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hσ : σ ∈ ({22/5, 23/5, 24/5, 5} : Finset ℝ)) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ (1/500 : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs hσ
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (0) (22/5) 1 (1)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_0
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (0) (23/5) 1 (1)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_0
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (0) (24/5) 1 (1)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_0
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (0) (5) 1 (1)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_0
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (3/20) (22/5) 1 (134986/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_20
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/20) (23/5) 1 (134986/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_20
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/20) (24/5) 1 (134986/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_20
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/20) (5) 1 (134986/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_20
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (3/10) (22/5) 1 (182212/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_10
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/10) (23/5) 1 (182212/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_10
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/10) (24/5) 1 (182212/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_10
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/10) (5) 1 (182212/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_10
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (9/20) (22/5) 1 (245961/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_20
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (9/20) (23/5) 1 (245961/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_20
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (9/20) (24/5) 1 (245961/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_20
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (9/20) (5) 1 (245961/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_20
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (3/5) (22/5) 1 (332012/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_5
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/5) (23/5) 1 (332012/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_5
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/5) (24/5) 1 (332012/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_5
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/5) (5) 1 (332012/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_5
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (3/4) (22/5) 1 (448170/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_4
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/4) (23/5) 1 (448170/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_4
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/4) (24/5) 1 (448170/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_4
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (3/4) (5) 1 (448170/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_3_4
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (9/10) (22/5) 1 (604965/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_10
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (9/10) (23/5) 1 (604965/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_10
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (9/10) (24/5) 1 (604965/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_10
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (9/10) (5) 1 (604965/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_9_10
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (21/20) (22/5) 1 (816618/100000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_21_20
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (21/20) (23/5) 1 (816618/100000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_21_20
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (21/20) (24/5) 1 (816618/100000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_21_20
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (21/20) (5) 1 (816618/100000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_21_20
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · rcases hσ with rfl | rfl | rfl | rfl
    · refine le_trans (Isub_le_cornerB (17/16) (22/5) 1 (83729/10000)
          (-8111931/10000000) (-810993/1000000) (5848171/10000000) (5850173/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_17_16
          (trigHi_22_5).1 (trigHi_22_5).2.1 (trigHi_22_5).2.2.1 (trigHi_22_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (17/16) (23/5) 1 (83729/10000)
          (-9749437/10000000) (-9747436/10000000) (2227899/10000000) (22299/100000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_17_16
          (trigHi_23_5).1 (trigHi_23_5).2.1 (trigHi_23_5).2.2.1 (trigHi_23_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (17/16) (24/5) 1 (83729/10000)
          (-9847879/10000000) (-9845877/10000000) (-1744269/10000000) (-1742267/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_17_16
          (trigHi_24_5).1 (trigHi_24_5).2.1 (trigHi_24_5).2.2.1 (trigHi_24_5).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
    · refine le_trans (Isub_le_cornerB (17/16) (5) 1 (83729/10000)
          (-8391716/10000000) (-8389711/10000000) (-5441213/10000000) (-5439208/10000000)
          (by norm_num) (by norm_num) (Real.one_le_exp (by norm_num)) expHi_17_16
          (trigHi_10).1 (trigHi_10).2.1 (trigHi_10).2.2.1 (trigHi_10).2.2.2) ?_
      norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]

end Work.OffAxis.Tf72One
