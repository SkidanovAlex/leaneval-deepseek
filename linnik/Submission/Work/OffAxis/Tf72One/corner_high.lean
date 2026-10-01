import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.trig_high
import Submission.Work.OffAxis.Tf72One.exp_bounds

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables.OffAxis

/-- Grid corner bound (larger `σ`).  For `s` in the nine-point grid
`{0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16}` and `σ ∈ {15/4, 4, 21/5}` one has
`Isub s σ ≤ -1/500`.

Same method as `corner_low`, with the `trig_high` conjuncts at `2σ ∈ {15/2, 8, 42/5}`. -/
theorem corner_high (s σ : ℝ)
    (hs : s ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hσ : σ ∈ ({15/4, 4, 21/5} : Finset ℝ)) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ (-1/500 : ℝ) := by
  obtain ⟨c15a, c15b, s15a, s15b, c8a, c8b, s8a, s8b, c42a, c42b, s42a, s42b⟩ := trig_high
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := exp_bounds
  have hA15 : (2:ℝ)*(15/4) = ((15:ℝ)/2) := by norm_num
  have hA4 : (2:ℝ)*4 = (8:ℝ) := by norm_num
  have hA42 : (2:ℝ)*(21/5) = ((42:ℝ)/5) := by norm_num
  have hB0 : (2:ℝ)*0 = (0:ℝ) := by norm_num
  have hB1 : (2:ℝ)*(3/20) = ((3:ℝ)/10) := by norm_num
  have hB2 : (2:ℝ)*(3/10) = ((3:ℝ)/5) := by norm_num
  have hB3 : (2:ℝ)*(9/20) = ((9:ℝ)/10) := by norm_num
  have hB4 : (2:ℝ)*(3/5) = ((6:ℝ)/5) := by norm_num
  have hB5 : (2:ℝ)*(3/4) = ((3:ℝ)/2) := by norm_num
  have hB6 : (2:ℝ)*(9/10) = ((9:ℝ)/5) := by norm_num
  have hB7 : (2:ℝ)*(21/20) = ((21:ℝ)/10) := by norm_num
  have hB8 : (2:ℝ)*(17/16) = ((17:ℝ)/8) := by norm_num
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs hσ
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hσ with rfl | rfl | rfl
  · refine le_trans (Isub_le_cornerB (0) (15/4) 1 (1)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (by rw [hB0]; exact le_of_eq Real.exp_zero.symm) (by rw [hB0]; exact e0)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (0) (4) 1 (1)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (by rw [hB0]; exact le_of_eq Real.exp_zero.symm) (by rw [hB0]; exact e0)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (0) (21/5) 1 (1)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (by rw [hB0]; exact le_of_eq Real.exp_zero.symm) (by rw [hB0]; exact e0)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/20) (15/4) 0 (134986/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB1]; exact e1)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/20) (4) 0 (134986/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB1]; exact e1)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/20) (21/5) 0 (134986/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB1]; exact e1)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/10) (15/4) 0 (182212/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB2]; exact e2)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/10) (4) 0 (182212/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB2]; exact e2)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/10) (21/5) 0 (182212/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB2]; exact e2)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (9/20) (15/4) 0 (245961/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB3]; exact e3)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (9/20) (4) 0 (245961/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB3]; exact e3)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (9/20) (21/5) 0 (245961/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB3]; exact e3)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/5) (15/4) 0 (332012/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB4]; exact e4)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/5) (4) 0 (332012/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB4]; exact e4)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/5) (21/5) 0 (332012/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB4]; exact e4)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/4) (15/4) 0 (448170/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB5]; exact e5)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/4) (4) 0 (448170/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB5]; exact e5)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (3/4) (21/5) 0 (448170/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB5]; exact e5)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (9/10) (15/4) 0 (604965/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB6]; exact e6)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (9/10) (4) 0 (604965/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB6]; exact e6)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (9/10) (21/5) 0 (604965/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB6]; exact e6)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (21/20) (15/4) 0 (816618/100000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB7]; exact e7)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (21/20) (4) 0 (816618/100000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB7]; exact e7)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (21/20) (21/5) 0 (816618/100000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB7]; exact e7)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (17/16) (15/4) 0 (83729/10000)
      (3465353/10000000) (3467354/10000000) (9378999/10000000) (9381/10000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB8]; exact e8)
      (by rw [hA15]; exact c15a) (by rw [hA15]; exact c15b)
      (by rw [hA15]; exact s15a) (by rw [hA15]; exact s15b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (17/16) (4) 0 (83729/10000)
      (-1456001/10000000) (-727/5000) (9892582/10000000) (9894583/10000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB8]; exact e8)
      (by rw [hA4]; exact c8a) (by rw [hA4]; exact c8b)
      (by rw [hA4]; exact s8a) (by rw [hA4]; exact s8b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
  · refine le_trans (Isub_le_cornerB (17/16) (21/5) 0 (83729/10000)
      (-5193887/10000000) (-5191886/10000000) (8544989/10000000) (854699/1000000)
      (by norm_num) (by norm_num)
      (Real.exp_nonneg _) (by rw [hB8]; exact e8)
      (by rw [hA42]; exact c42a) (by rw [hA42]; exact c42b)
      (by rw [hA42]; exact s42a) (by rw [hA42]; exact s42b)) ?_
    norm_num [cornerB, RcHi, RcLo, RsHi, RsLo, RA72, RB72, RI72]
end Work.OffAxis.Tf72One
