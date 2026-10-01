import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23Gclosed
import Submission.Work.ZeroFreeTables.t23ExpBounds

namespace Work.ZeroFreeTables

theorem t23RowDE : ∀ p : ℝ × ℝ × ℝ, p ∈ Work.ZeroFreeTables.rowD ++ Work.ZeroFreeTables.rowE →
    (1 / 15) * (Work.ZeroFreeTables.hb72G (p.2.2 / p.1) - Work.ZeroFreeTables.hb72G ((p.2.2 - p.2.1) / p.1))
      < 8 / 9 - Work.ZeroFreeTables.CertSlack * (16 * p.1 / 15) := by
  intro p hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · simp only [rowD, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h | h | h | h
    · rw [h]
      rw [show (5.18:ℝ)/(2.5:ℝ) = (259:ℝ)/125 by norm_num,
          show ((5.18:ℝ) - 0.086)/(2.5:ℝ) = (2547:ℝ)/1250 by norm_num]
      rw [hb72G_closed (by norm_num : ((259:ℝ)/125) ≠ 0),
          hb72G_closed (by norm_num : ((2547:ℝ)/1250) ≠ 0)]
      rw [show 2 * ((259:ℝ)/125) = (518:ℝ)/125 by norm_num,
          show 2 * ((2547:ℝ)/1250) = (2547:ℝ)/625 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (518:ℝ)/125 - 4) (lo := (3609/3125:ℝ)) (hi := (115489/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((518:ℝ)/125) ≤ (3152743/50000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (2547:ℝ)/625 - 4) (lo := (107809/100000:ℝ)) (hi := (10781/10000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (5886171/100000:ℝ) ≤ Real.exp ((2547:ℝ)/625) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (5.491:ℝ)/(2.55:ℝ) = (323:ℝ)/150 by norm_num,
          show ((5.491:ℝ) - 0.075)/(2.55:ℝ) = (2708:ℝ)/1275 by norm_num]
      rw [hb72G_closed (by norm_num : ((323:ℝ)/150) ≠ 0),
          hb72G_closed (by norm_num : ((2708:ℝ)/1275) ≠ 0)]
      rw [show 2 * ((323:ℝ)/150) = (323:ℝ)/75 by norm_num,
          show 2 * ((2708:ℝ)/1275) = (5416:ℝ)/1275 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (323:ℝ)/75 - 4) (lo := (8493/6250:ℝ)) (hi := (135889/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((323:ℝ)/75) ≤ (7419289/100000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (5416:ℝ)/1275 - 4) (lo := (41/32:ℝ)) (hi := (64063/50000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (6995387/100000:ℝ) ≤ Real.exp ((5416:ℝ)/1275) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (5.849:ℝ)/(2.55:ℝ) = (5849:ℝ)/2550 by norm_num,
          show ((5.849:ℝ) - 0.064)/(2.55:ℝ) = (1157:ℝ)/510 by norm_num]
      rw [hb72G_closed (by norm_num : ((5849:ℝ)/2550) ≠ 0),
          hb72G_closed (by norm_num : ((1157:ℝ)/510) ≠ 0)]
      rw [show 2 * ((5849:ℝ)/2550) = (5849:ℝ)/1275 by norm_num,
          show 2 * ((1157:ℝ)/510) = (1157:ℝ)/255 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (5849:ℝ)/1275 - 4) (lo := (179939/100000:ℝ)) (hi := (8997/5000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((5849:ℝ)/1275) ≤ (1228049/12500:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (1157:ℝ)/255 - 4) (lo := (17113/10000:ℝ)) (hi := (171131/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (9343381/100000:ℝ) ≤ Real.exp ((1157:ℝ)/255) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (6.259:ℝ)/(2.6:ℝ) = (6259:ℝ)/2600 by norm_num,
          show ((6.259:ℝ) - 0.054)/(2.6:ℝ) = (1241:ℝ)/520 by norm_num]
      rw [hb72G_closed (by norm_num : ((6259:ℝ)/2600) ≠ 0),
          hb72G_closed (by norm_num : ((1241:ℝ)/520) ≠ 0)]
      rw [show 2 * ((6259:ℝ)/2600) = (6259:ℝ)/1300 by norm_num,
          show 2 * ((1241:ℝ)/520) = (1241:ℝ)/260 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (6259:ℝ)/1300 - 4) (lo := (22583/10000:ℝ)) (hi := (225831/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((6259:ℝ)/1300) ≤ (2465991/20000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (1241:ℝ)/260 - 4) (lo := (108321/50000:ℝ)) (hi := (216643/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (2957063/25000:ℝ) ≤ Real.exp ((1241:ℝ)/260) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (6.728:ℝ)/(2.6:ℝ) = (841:ℝ)/325 by norm_num,
          show ((6.728:ℝ) - 0.044)/(2.6:ℝ) = (1671:ℝ)/650 by norm_num]
      rw [hb72G_closed (by norm_num : ((841:ℝ)/325) ≠ 0),
          hb72G_closed (by norm_num : ((1671:ℝ)/650) ≠ 0)]
      rw [show 2 * ((841:ℝ)/325) = (1682:ℝ)/325 by norm_num,
          show 2 * ((1671:ℝ)/650) = (1671:ℝ)/325 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (1682:ℝ)/325 - 4) (lo := (161969/50000:ℝ)) (hi := (323939/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((1682:ℝ)/325) ≤ (17686471/100000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (1671:ℝ)/325 - 4) (lo := (156579/50000:ℝ)) (hi := (313159/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (17097847/100000:ℝ) ≤ Real.exp ((1671:ℝ)/325) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (7.262:ℝ)/(2.65:ℝ) = (3631:ℝ)/1325 by norm_num,
          show ((7.262:ℝ) - 0.035)/(2.65:ℝ) = (7227:ℝ)/2650 by norm_num]
      rw [hb72G_closed (by norm_num : ((3631:ℝ)/1325) ≠ 0),
          hb72G_closed (by norm_num : ((7227:ℝ)/2650) ≠ 0)]
      rw [show 2 * ((3631:ℝ)/1325) = (7262:ℝ)/1325 by norm_num,
          show 2 * ((7227:ℝ)/2650) = (7227:ℝ)/1325 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (7262:ℝ)/1325 - 4) (lo := (219813/50000:ℝ)) (hi := (439627/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((7262:ℝ)/1325) ≤ (24002821/100000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (7227:ℝ)/1325 - 4) (lo := (85633/20000:ℝ)) (hi := (214083/50000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (2922127/12500:ℝ) ≤ Real.exp ((7227:ℝ)/1325) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
  · simp only [rowE, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h | h | h | h
    · rw [h]
      rw [show (7.867:ℝ)/(2.7:ℝ) = (7867:ℝ)/2700 by norm_num,
          show ((7.867:ℝ) - 0.026)/(2.7:ℝ) = (7841:ℝ)/2700 by norm_num]
      rw [hb72G_closed (by norm_num : ((7867:ℝ)/2700) ≠ 0),
          hb72G_closed (by norm_num : ((7841:ℝ)/2700) ≠ 0)]
      rw [show 2 * ((7867:ℝ)/2700) = (7867:ℝ)/1350 by norm_num,
          show 2 * ((7841:ℝ)/2700) = (7841:ℝ)/1350 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (7867:ℝ)/1350 - 4) (lo := (310887/50000:ℝ)) (hi := (24871/4000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((7867:ℝ)/1350) ≤ (6789553/20000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (7841:ℝ)/1350 - 4) (lo := (304957/50000:ℝ)) (hi := (121983/20000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (2081261/6250:ℝ) ≤ Real.exp ((7841:ℝ)/1350) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (8.5:ℝ)/(2.7:ℝ) = (85:ℝ)/27 by norm_num,
          show ((8.5:ℝ) - 0.02)/(2.7:ℝ) = (424:ℝ)/135 by norm_num]
      rw [hb72G_closed (by norm_num : ((85:ℝ)/27) ≠ 0),
          hb72G_closed (by norm_num : ((424:ℝ)/135) ≠ 0)]
      rw [show 2 * ((85:ℝ)/27) = (170:ℝ)/27 by norm_num,
          show 2 * ((424:ℝ)/135) = (848:ℝ)/135 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (170:ℝ)/27 - 4) (lo := (99373/10000:ℝ)) (hi := (993731/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((170:ℝ)/27) ≤ (434047/800:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (848:ℝ)/135 - 4) (lo := (979117/100000:ℝ)) (hi := (489559/50000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (6682247/12500:ℝ) ≤ Real.exp ((848:ℝ)/135) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (9.24:ℝ)/(549/200:ℝ) = (616:ℝ)/183 by norm_num,
          show ((9.24:ℝ) - 0.0145)/(549/200:ℝ) = (18451:ℝ)/5490 by norm_num]
      rw [hb72G_closed (by norm_num : ((616:ℝ)/183) ≠ 0),
          hb72G_closed (by norm_num : ((18451:ℝ)/5490) ≠ 0)]
      rw [show 2 * ((616:ℝ)/183) = (1232:ℝ)/183 by norm_num,
          show 2 * ((18451:ℝ)/5490) = (18451:ℝ)/2745 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (1232:ℝ)/183 - 4) (lo := (1536727/100000:ℝ)) (hi := (192091/12500:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((1232:ℝ)/183) ≤ (83902507/100000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (18451:ℝ)/2745 - 4) (lo := (760289/50000:ℝ)) (hi := (1520579/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (16604149/20000:ℝ) ≤ Real.exp ((18451:ℝ)/2745) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (10.0:ℝ)/(139/50:ℝ) = (500:ℝ)/139 by norm_num,
          show ((10.0:ℝ) - 0.0102)/(139/50:ℝ) = (49949:ℝ)/13900 by norm_num]
      rw [hb72G_closed (by norm_num : ((500:ℝ)/139) ≠ 0),
          hb72G_closed (by norm_num : ((49949:ℝ)/13900) ≠ 0)]
      rw [show 2 * ((500:ℝ)/139) = (1000:ℝ)/139 by norm_num,
          show 2 * ((49949:ℝ)/13900) = (49949:ℝ)/6950 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (1000:ℝ)/139 - 4) (lo := (1219587/50000:ℝ)) (hi := (97567/4000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((1000:ℝ)/139) ≤ (133174443/100000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (49949:ℝ)/6950 - 4) (lo := (121067/5000:ℝ)) (hi := (2421341/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (33050171/25000:ℝ) ≤ Real.exp ((49949:ℝ)/6950) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (10.9:ℝ)/(113/40:ℝ) = (436:ℝ)/113 by norm_num,
          show ((10.9:ℝ) - 0.0068)/(113/40:ℝ) = (482:ℝ)/125 by norm_num]
      rw [hb72G_closed (by norm_num : ((436:ℝ)/113) ≠ 0),
          hb72G_closed (by norm_num : ((482:ℝ)/125) ≠ 0)]
      rw [show 2 * ((436:ℝ)/113) = (872:ℝ)/113 by norm_num,
          show 2 * ((482:ℝ)/125) = (964:ℝ)/125 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (872:ℝ)/113 - 4) (lo := (2056657/50000:ℝ)) (hi := (822663/20000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((872:ℝ)/113) ≤ (22457939/10000:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (964:ℝ)/125 - 4) (lo := (4093559/100000:ℝ)) (hi := (102339/2500:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (55875187/25000:ℝ) ≤ Real.exp ((964:ℝ)/125) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · rw [h]
      rw [show (11.071:ℝ)/(2.8:ℝ) = (11071:ℝ)/2800 by norm_num,
          show ((11.071:ℝ) - 0.006)/(2.8:ℝ) = (2213:ℝ)/560 by norm_num]
      rw [hb72G_closed (by norm_num : ((11071:ℝ)/2800) ≠ 0),
          hb72G_closed (by norm_num : ((2213:ℝ)/560) ≠ 0)]
      rw [show 2 * ((11071:ℝ)/2800) = (11071:ℝ)/1400 by norm_num,
          show 2 * ((2213:ℝ)/560) = (2213:ℝ)/280 by norm_num]
      obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (11071:ℝ)/1400 - 4) (lo := (4979213/100000:ℝ)) (hi := (995843/20000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h1hi : Real.exp ((11071:ℝ)/1400) ≤ (33981991/12500:ℝ) :=
        exp_le_of_quart_sub h1quart (by norm_num)
      obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (2213:ℝ)/280 - 4) (lo := (30987/625:ℝ)) (hi := (4957921/100000:ℝ))
          (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
      have h2lo : (270693259/100000:ℝ) ≤ Real.exp ((2213:ℝ)/280) :=
        le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
      norm_num [CertSlack]
      linarith [h1hi, h2lo]

end Work.ZeroFreeTables
