import Mathlib
import Submission.Work.LinnikAreas.A7.ValueLemmas
import Submission.Work.LinnikAreas.A7.NumPoints
import Submission.Work.LinnikAreas.Density4.wHB_antitone

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

-- row 0 (0.348..0.36), case cx: Lambda = 49/40, s = 0
theorem rowA_0_cx {lam1 : ℝ}
    (h1 : ((87:ℝ)/(250)) ≤ lam1) (h2 : lam1 ≤ ((9:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(250)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((87:ℝ)/(250)))))/((87:ℝ)/(250)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((327:ℝ)/(250)) lam1 ≤ ((3646547:ℝ)/(25000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((327:ℝ)/(250)) := by linarith
  have hpa : ((87:ℝ)/(250)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((87:ℝ)/(250)))) ≤ ((4543401:ℝ)/(25000000)) := exF_a_87_250
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((87:ℝ)/(250)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(250)) ≤ ((193666723:ℝ)/(100000000)) := (v_87_250).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((87:ℝ)/(250)))))/((87:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((90168359:ℝ)/(100000000)) := (v_87_250).2.2.2.2.2.2
  have hPbA : ((7715967:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((9:ℝ)/(25)) := (v_9_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((9:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((87:ℝ)/(250))) (b := ((9:ℝ)/(25))) hp_c0 hpc hBF (exF_a_327_250) (exG_a_327_250)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_0_cx {lam1 : ℝ}
    (h1 : ((327:ℝ)/(250)) ≤ lam1) (h2 : lam1 ≤ ((9:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((327:ℝ)/(250))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((0:ℝ)/(1)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((327:ℝ)/(250)) ≤ ((255597:ℝ)/(100000000)) := (v_327_250).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((3257231:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((327:ℝ)/(250)) := (v_327_250).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((327:ℝ)/(250))) (Pc := ((255597:ℝ)/(100000000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((3257231:ℝ)/(50000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((0:ℝ)/(1)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 0 (0.348..0.36), case rr: Lambda = 49/40, s = 0
theorem rowA_0_rr {lam1 : ℝ}
    (h1 : ((87:ℝ)/(250)) ≤ lam1) (h2 : lam1 ≤ ((9:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(250)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((87:ℝ)/(250)))))/((87:ℝ)/(250)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((327:ℝ)/(250)) lam1 ≤ ((3646547:ℝ)/(25000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((327:ℝ)/(250)) := by linarith
  have hpa : ((87:ℝ)/(250)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((87:ℝ)/(250)))) ≤ ((4543401:ℝ)/(25000000)) := exF_a_87_250
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((87:ℝ)/(250)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(250)) ≤ ((193666723:ℝ)/(100000000)) := (v_87_250).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((87:ℝ)/(250)))))/((87:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((90168359:ℝ)/(100000000)) := (v_87_250).2.2.2.2.2.2
  have hPbA : ((7715967:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((9:ℝ)/(25)) := (v_9_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((9:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((87:ℝ)/(250))) (b := ((9:ℝ)/(25))) hp_c0 hpc hBF (exF_a_327_250) (exG_a_327_250)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_0_rr {lam1 : ℝ}
    (h1 : ((327:ℝ)/(250)) ≤ lam1) (h2 : lam1 ≤ ((9:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((327:ℝ)/(250))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((0:ℝ)/(1)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((327:ℝ)/(250)) ≤ ((255597:ℝ)/(100000000)) := (v_327_250).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((3257231:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((327:ℝ)/(250)) := (v_327_250).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((327:ℝ)/(250))) (Pc := ((255597:ℝ)/(100000000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((3257231:ℝ)/(50000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((0:ℝ)/(1)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 1 (0.36..0.38), case cx: Lambda = 6/5, s = 0
theorem rowA_1_cx {lam1 : ℝ}
    (h1 : ((9:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((19:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(25)))))/((9:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((1249:ℝ)/(1000)) lam1 ≤ ((13564633:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((1249:ℝ)/(1000)) := by linarith
  have hpa : ((9:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((9:ℝ)/(25)))) ≤ ((8567903:ℝ)/(50000000)) := exF_a_9_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((9:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(25)) ≤ ((193103027:ℝ)/(100000000)) := (v_9_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(25)))))/((9:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((17970011:ℝ)/(20000000)) := (v_9_25).2.2.2.2.2.2
  have hPbA : ((9302549:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Wf ((19:ℝ)/(50)) := (v_19_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((19:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((9:ℝ)/(25))) (b := ((19:ℝ)/(50))) hp_c0 hpc hBF (exF_a_1249_1000) (exG_a_1249_1000)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_1_cx {lam1 : ℝ}
    (h1 : ((1249:ℝ)/(1000)) ≤ lam1) (h2 : lam1 ≤ ((19:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((1249:ℝ)/(1000))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((0:ℝ)/(1)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((1249:ℝ)/(1000)) ≤ ((345709:ℝ)/(100000000)) := (v_1249_1000).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((7304263:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((1249:ℝ)/(1000)) := (v_1249_1000).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((1249:ℝ)/(1000))) (Pc := ((345709:ℝ)/(100000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((7304263:ℝ)/(100000000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((0:ℝ)/(1)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 1 (0.36..0.38), case rr: Lambda = 6/5, s = 0
theorem rowA_1_rr {lam1 : ℝ}
    (h1 : ((9:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((19:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(25)))))/((9:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((1249:ℝ)/(1000)) lam1 ≤ ((13564633:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((1249:ℝ)/(1000)) := by linarith
  have hpa : ((9:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((9:ℝ)/(25)))) ≤ ((8567903:ℝ)/(50000000)) := exF_a_9_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((9:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(25)) ≤ ((193103027:ℝ)/(100000000)) := (v_9_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(25)))))/((9:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((17970011:ℝ)/(20000000)) := (v_9_25).2.2.2.2.2.2
  have hPbA : ((9302549:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Wf ((19:ℝ)/(50)) := (v_19_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((19:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((9:ℝ)/(25))) (b := ((19:ℝ)/(50))) hp_c0 hpc hBF (exF_a_1249_1000) (exG_a_1249_1000)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_1_rr {lam1 : ℝ}
    (h1 : ((1249:ℝ)/(1000)) ≤ lam1) (h2 : lam1 ≤ ((19:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((1249:ℝ)/(1000))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((0:ℝ)/(1)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((1249:ℝ)/(1000)) ≤ ((345709:ℝ)/(100000000)) := (v_1249_1000).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((7304263:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((1249:ℝ)/(1000)) := (v_1249_1000).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((1249:ℝ)/(1000))) (Pc := ((345709:ℝ)/(100000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((7304263:ℝ)/(100000000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((0:ℝ)/(1)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 2 (0.38..0.4), case cx: Lambda = 6/5, s = 2
theorem rowA_2_cx {lam1 : ℝ}
    (h1 : ((19:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((2:ℝ)/(5)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((19:ℝ)/(50)))))/((19:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((239:ℝ)/(200)) lam1 ≤ ((3046547:ℝ)/(25000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((239:ℝ)/(200)) := by linarith
  have hpa : ((19:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((19:ℝ)/(50)))) ≤ ((97101:ℝ)/(625000)) := exF_a_19_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((19:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(50)) ≤ ((48042207:ℝ)/(25000000)) := (v_19_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((19:ℝ)/(50)))))/((19:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((89322479:ℝ)/(100000000)) := (v_19_50).2.2.2.2.2.2
  have hPbA : ((35886977:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((2:ℝ)/(5)) := (v_2_5).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((2:ℝ)/(5)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((19:ℝ)/(50))) (b := ((2:ℝ)/(5))) hp_c0 hpc hBF (exF_a_239_200) (exG_a_239_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_2_cx {lam1 : ℝ}
    (h1 : ((239:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((2:ℝ)/(5)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((239:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((7221:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((239:ℝ)/(200)) ≤ ((113953:ℝ)/(25000000)) := (v_239_200).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((1013429:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((239:ℝ)/(200)) := (v_239_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((239:ℝ)/(200))) (Pc := ((113953:ℝ)/(25000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((1013429:ℝ)/(12500000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((7221:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 2 (0.38..0.4), case rr: Lambda = 6/5, s = 2
theorem rowA_2_rr {lam1 : ℝ}
    (h1 : ((19:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((2:ℝ)/(5)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((19:ℝ)/(50)))))/((19:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((239:ℝ)/(200)) lam1 ≤ ((3046547:ℝ)/(25000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((239:ℝ)/(200)) := by linarith
  have hpa : ((19:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((19:ℝ)/(50)))) ≤ ((97101:ℝ)/(625000)) := exF_a_19_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((19:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(50)) ≤ ((48042207:ℝ)/(25000000)) := (v_19_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((19:ℝ)/(50)))))/((19:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((89322479:ℝ)/(100000000)) := (v_19_50).2.2.2.2.2.2
  have hPbA : ((35886977:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((2:ℝ)/(5)) := (v_2_5).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((2:ℝ)/(5)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((19:ℝ)/(50))) (b := ((2:ℝ)/(5))) hp_c0 hpc hBF (exF_a_239_200) (exG_a_239_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_2_rr {lam1 : ℝ}
    (h1 : ((239:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((2:ℝ)/(5)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((239:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((7221:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((239:ℝ)/(200)) ≤ ((113953:ℝ)/(25000000)) := (v_239_200).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((1013429:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((239:ℝ)/(200)) := (v_239_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((239:ℝ)/(200))) (Pc := ((113953:ℝ)/(25000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((1013429:ℝ)/(12500000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((7221:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 3 (0.4..0.42), case cx: Lambda = 6/5, s = 4
theorem rowA_3_cx {lam1 : ℝ}
    (h1 : ((2:ℝ)/(5)) ≤ lam1) (h2 : lam1 ≤ ((21:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((2:ℝ)/(5)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((2:ℝ)/(5)))))/((2:ℝ)/(5)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((143:ℝ)/(125)) lam1 ≤ ((10969797:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((143:ℝ)/(125)) := by linarith
  have hpa : ((2:ℝ)/(5)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((2:ℝ)/(5)))) ≤ ((14085843:ℝ)/(100000000)) := exF_a_2_5
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((2:ℝ)/(5)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((2:ℝ)/(5)) ≤ ((191241281:ℝ)/(100000000)) := (v_2_5).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((2:ℝ)/(5)))))/((2:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((11099817:ℝ)/(12500000)) := (v_2_5).2.2.2.2.2.2
  have hPbA : ((3460869:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Wf ((21:ℝ)/(50)) := (v_21_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((21:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((2:ℝ)/(5))) (b := ((21:ℝ)/(50))) hp_c0 hpc hBF (exF_a_143_125) (exG_a_143_125)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_3_cx {lam1 : ℝ}
    (h1 : ((143:ℝ)/(125)) ≤ lam1) (h2 : lam1 ≤ ((21:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((143:ℝ)/(125))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((97001:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((143:ℝ)/(125)) ≤ ((29593:ℝ)/(5000000)) := (v_143_125).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((8943633:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((143:ℝ)/(125)) := (v_143_125).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((143:ℝ)/(125))) (Pc := ((29593:ℝ)/(5000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((8943633:ℝ)/(100000000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((97001:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 3 (0.4..0.42), case rr: Lambda = 6/5, s = 4
theorem rowA_3_rr {lam1 : ℝ}
    (h1 : ((2:ℝ)/(5)) ≤ lam1) (h2 : lam1 ≤ ((21:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((2:ℝ)/(5)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((2:ℝ)/(5)))))/((2:ℝ)/(5)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((143:ℝ)/(125)) lam1 ≤ ((10969797:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((143:ℝ)/(125)) := by linarith
  have hpa : ((2:ℝ)/(5)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((2:ℝ)/(5)))) ≤ ((14085843:ℝ)/(100000000)) := exF_a_2_5
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((2:ℝ)/(5)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((2:ℝ)/(5)) ≤ ((191241281:ℝ)/(100000000)) := (v_2_5).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((2:ℝ)/(5)))))/((2:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((11099817:ℝ)/(12500000)) := (v_2_5).2.2.2.2.2.2
  have hPbA : ((3460869:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Wf ((21:ℝ)/(50)) := (v_21_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((21:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((2:ℝ)/(5))) (b := ((21:ℝ)/(50))) hp_c0 hpc hBF (exF_a_143_125) (exG_a_143_125)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_3_rr {lam1 : ℝ}
    (h1 : ((143:ℝ)/(125)) ≤ lam1) (h2 : lam1 ≤ ((21:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((143:ℝ)/(125))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((97001:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((143:ℝ)/(125)) ≤ ((29593:ℝ)/(5000000)) := (v_143_125).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((8943633:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((143:ℝ)/(125)) := (v_143_125).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((143:ℝ)/(125))) (Pc := ((29593:ℝ)/(5000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((8943633:ℝ)/(100000000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((97001:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 4 (0.42..0.44), case cx: Lambda = 6/5, s = 5
theorem rowA_4_cx {lam1 : ℝ}
    (h1 : ((21:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((11:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((21:ℝ)/(50)))))/((21:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((549:ℝ)/(500)) lam1 ≤ ((618589:ℝ)/(6250000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((549:ℝ)/(500)) := by linarith
  have hpa : ((21:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((21:ℝ)/(50)))) ≤ ((6385457:ℝ)/(50000000)) := exF_a_21_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((21:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(50)) ≤ ((7612809:ℝ)/(4000000)) := (v_21_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((21:ℝ)/(50)))))/((21:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((17655639:ℝ)/(20000000)) := (v_21_50).2.2.2.2.2.2
  have hPbA : ((33373891:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((11:ℝ)/(25)) := (v_11_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((11:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((21:ℝ)/(50))) (b := ((11:ℝ)/(25))) hp_c0 hpc hBF (exF_a_549_500) (exG_a_549_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_4_cx {lam1 : ℝ}
    (h1 : ((549:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((11:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((549:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((1669:ℝ)/(800000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((549:ℝ)/(500)) ≤ ((749129:ℝ)/(100000000)) := (v_549_500).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((390743:ℝ)/(4000000)) ≤ Work.LinnikAreas.A7.Wf ((549:ℝ)/(500)) := (v_549_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((549:ℝ)/(500))) (Pc := ((749129:ℝ)/(100000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((390743:ℝ)/(4000000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((1669:ℝ)/(800000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 4 (0.42..0.44), case rr: Lambda = 6/5, s = 5
theorem rowA_4_rr {lam1 : ℝ}
    (h1 : ((21:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((11:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((21:ℝ)/(50)))))/((21:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 - Work.LinnikAreas.A7.Aref ((549:ℝ)/(500)) lam1 ≤ ((618589:ℝ)/(6250000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((549:ℝ)/(500)) := by linarith
  have hpa : ((21:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((21:ℝ)/(50)))) ≤ ((6385457:ℝ)/(50000000)) := exF_a_21_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((21:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(50)) ≤ ((7612809:ℝ)/(4000000)) := (v_21_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((21:ℝ)/(50)))))/((21:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((17655639:ℝ)/(20000000)) := (v_21_50).2.2.2.2.2.2
  have hPbA : ((33373891:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((11:ℝ)/(25)) := (v_11_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((11:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst1_le (a := ((21:ℝ)/(50))) (b := ((11:ℝ)/(25))) hp_c0 hpc hBF (exF_a_549_500) (exG_a_549_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_4_rr {lam1 : ℝ}
    (h1 : ((549:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((11:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) ((549:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((6:ℝ)/(5)) lam1 ≤ ((1669:ℝ)/(800000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((549:ℝ)/(500)) ≤ ((749129:ℝ)/(100000000)) := (v_549_500).1
  have hPL : ((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) := (v_6_5).2.1
  have hWlc : ((390743:ℝ)/(4000000)) ≤ Work.LinnikAreas.A7.Wf ((549:ℝ)/(500)) := (v_549_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500)) := (v_6_5).2.2.1
  have hWL : ((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) := (v_6_5).2.2.2.1
  exact Cst2_le (L := ((6:ℝ)/(5))) (p := lam1) (c := ((549:ℝ)/(500))) (Pc := ((749129:ℝ)/(100000000)))
    (PLl := ((444287:ℝ)/(100000000))) (Wlc := ((390743:ℝ)/(4000000))) (WLu := ((125463:ℝ)/(1562500))) (r := ((1669:ℝ)/(800000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((8029629:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 5 (0.44..0.46), case cx: Lambda = 49/40, s = 8
theorem rowA_5_cx {lam1 : ℝ}
    (h1 : ((11:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((23:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((11:ℝ)/(25)))))/((11:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((527:ℝ)/(500)) lam1 ≤ ((1137307:ℝ)/(12500000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((527:ℝ)/(500)) := by linarith
  have hpa : ((11:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((11:ℝ)/(25)))) ≤ ((2315747:ℝ)/(20000000)) := exF_a_11_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((11:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(25)) ≤ ((94702837:ℝ)/(50000000)) := (v_11_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((11:ℝ)/(25)))))/((11:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((43880713:ℝ)/(50000000)) := (v_11_25).2.2.2.2.2.2
  have hPbA : ((32181179:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((23:ℝ)/(50)) := (v_23_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((23:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((11:ℝ)/(25))) (b := ((23:ℝ)/(50))) hp_c0 hpc hBF (exF_a_527_500) (exG_a_527_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_5_cx {lam1 : ℝ}
    (h1 : ((527:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((23:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((527:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((197847:ℝ)/(50000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((527:ℝ)/(500)) ≤ ((117321:ℝ)/(12500000)) := (v_527_500).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((531291:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((527:ℝ)/(500)) := (v_527_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((527:ℝ)/(500))) (Pc := ((117321:ℝ)/(12500000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((531291:ℝ)/(5000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((197847:ℝ)/(50000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 5 (0.44..0.46), case rr: Lambda = 49/40, s = 8
theorem rowA_5_rr {lam1 : ℝ}
    (h1 : ((11:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((23:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((11:ℝ)/(25)))))/((11:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((527:ℝ)/(500)) lam1 ≤ ((1137307:ℝ)/(12500000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((527:ℝ)/(500)) := by linarith
  have hpa : ((11:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((11:ℝ)/(25)))) ≤ ((2315747:ℝ)/(20000000)) := exF_a_11_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((11:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(25)) ≤ ((94702837:ℝ)/(50000000)) := (v_11_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((11:ℝ)/(25)))))/((11:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((43880713:ℝ)/(50000000)) := (v_11_25).2.2.2.2.2.2
  have hPbA : ((32181179:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((23:ℝ)/(50)) := (v_23_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((23:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((11:ℝ)/(25))) (b := ((23:ℝ)/(50))) hp_c0 hpc hBF (exF_a_527_500) (exG_a_527_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_5_rr {lam1 : ℝ}
    (h1 : ((527:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((23:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((527:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((197847:ℝ)/(50000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((527:ℝ)/(500)) ≤ ((117321:ℝ)/(12500000)) := (v_527_500).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((531291:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((527:ℝ)/(500)) := (v_527_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((527:ℝ)/(500))) (Pc := ((117321:ℝ)/(12500000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((531291:ℝ)/(5000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((197847:ℝ)/(50000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 6 (0.46..0.48), case cx: Lambda = 49/40, s = 9
theorem rowA_6_cx {lam1 : ℝ}
    (h1 : ((23:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((12:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((23:ℝ)/(50)))))/((23:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((507:ℝ)/(500)) lam1 ≤ ((8277873:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((507:ℝ)/(500)) := by linarith
  have hpa : ((23:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((23:ℝ)/(50)))) ≤ ((10497847:ℝ)/(100000000)) := exF_a_23_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((23:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(50)) ≤ ((94248789:ℝ)/(50000000)) := (v_23_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((23:ℝ)/(50)))))/((23:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((87248203:ℝ)/(100000000)) := (v_23_50).2.2.2.2.2.2
  have hPbA : ((31029199:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((12:ℝ)/(25)) := (v_12_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((12:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((23:ℝ)/(50))) (b := ((12:ℝ)/(25))) hp_c0 hpc hBF (exF_a_507_500) (exG_a_507_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_6_cx {lam1 : ℝ}
    (h1 : ((507:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((12:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((507:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((566233:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((507:ℝ)/(500)) ≤ ((115211:ℝ)/(10000000)) := (v_507_500).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((5733767:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((507:ℝ)/(500)) := (v_507_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((507:ℝ)/(500))) (Pc := ((115211:ℝ)/(10000000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((5733767:ℝ)/(50000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((566233:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 6 (0.46..0.48), case rr: Lambda = 49/40, s = 9
theorem rowA_6_rr {lam1 : ℝ}
    (h1 : ((23:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((12:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((23:ℝ)/(50)))))/((23:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((507:ℝ)/(500)) lam1 ≤ ((8277873:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((507:ℝ)/(500)) := by linarith
  have hpa : ((23:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((23:ℝ)/(50)))) ≤ ((10497847:ℝ)/(100000000)) := exF_a_23_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((23:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(50)) ≤ ((94248789:ℝ)/(50000000)) := (v_23_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((23:ℝ)/(50)))))/((23:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((87248203:ℝ)/(100000000)) := (v_23_50).2.2.2.2.2.2
  have hPbA : ((31029199:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((12:ℝ)/(25)) := (v_12_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((12:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((23:ℝ)/(50))) (b := ((12:ℝ)/(25))) hp_c0 hpc hBF (exF_a_507_500) (exG_a_507_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_6_rr {lam1 : ℝ}
    (h1 : ((507:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((12:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((507:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((566233:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((507:ℝ)/(500)) ≤ ((115211:ℝ)/(10000000)) := (v_507_500).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((5733767:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((507:ℝ)/(500)) := (v_507_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((507:ℝ)/(500))) (Pc := ((115211:ℝ)/(10000000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((5733767:ℝ)/(50000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((566233:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 7 (0.48..0.5), case cx: Lambda = 49/40, s = 10
theorem rowA_7_cx {lam1 : ℝ}
    (h1 : ((12:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((1:ℝ)/(2)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((12:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((12:ℝ)/(25)))))/((12:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((122:ℝ)/(125)) lam1 ≤ ((3785989:ℝ)/(50000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((122:ℝ)/(125)) := by linarith
  have hpa : ((12:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((12:ℝ)/(25)))) ≤ ((4758931:ℝ)/(50000000)) := exF_a_12_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((12:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((12:ℝ)/(25)) ≤ ((93797919:ℝ)/(50000000)) := (v_12_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((12:ℝ)/(25)))))/((12:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((17347703:ℝ)/(20000000)) := (v_12_25).2.2.2.2.2.2
  have hPbA : ((3739579:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((1:ℝ)/(2)) := (v_1_2).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((1:ℝ)/(2)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((12:ℝ)/(25))) (b := ((1:ℝ)/(2))) hp_c0 hpc hBF (exF_a_122_125) (exG_a_122_125)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_7_cx {lam1 : ℝ}
    (h1 : ((122:ℝ)/(125)) ≤ lam1) (h2 : lam1 ≤ ((1:ℝ)/(2)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((122:ℝ)/(125))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((770119:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((122:ℝ)/(125)) ≤ ((349967:ℝ)/(25000000)) := (v_122_125).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((12326251:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((122:ℝ)/(125)) := (v_122_125).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((122:ℝ)/(125))) (Pc := ((349967:ℝ)/(25000000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((12326251:ℝ)/(100000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((770119:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 7 (0.48..0.5), case rr: Lambda = 49/40, s = 10
theorem rowA_7_rr {lam1 : ℝ}
    (h1 : ((12:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((1:ℝ)/(2)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((12:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((12:ℝ)/(25)))))/((12:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((122:ℝ)/(125)) lam1 ≤ ((3785989:ℝ)/(50000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((122:ℝ)/(125)) := by linarith
  have hpa : ((12:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((12:ℝ)/(25)))) ≤ ((4758931:ℝ)/(50000000)) := exF_a_12_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((12:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((12:ℝ)/(25)) ≤ ((93797919:ℝ)/(50000000)) := (v_12_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((12:ℝ)/(25)))))/((12:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((17347703:ℝ)/(20000000)) := (v_12_25).2.2.2.2.2.2
  have hPbA : ((3739579:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((1:ℝ)/(2)) := (v_1_2).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((1:ℝ)/(2)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst1_le (a := ((12:ℝ)/(25))) (b := ((1:ℝ)/(2))) hp_c0 hpc hBF (exF_a_122_125) (exG_a_122_125)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) (by norm_num) (by norm_num)

theorem rowB_7_rr {lam1 : ℝ}
    (h1 : ((122:ℝ)/(125)) ≤ lam1) (h2 : lam1 ≤ ((1:ℝ)/(2)))
    (hCf : Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) ((122:ℝ)/(125))) :
    Work.LinnikAreas.A7.Cf ((49:ℝ)/(40)) lam1 ≤ ((770119:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((122:ℝ)/(125)) ≤ ((349967:ℝ)/(25000000)) := (v_122_125).1
  have hPL : ((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) := (v_49_40).2.1
  have hWlc : ((12326251:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((122:ℝ)/(125)) := (v_122_125).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000)) := (v_49_40).2.2.1
  have hWL : ((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) := (v_49_40).2.2.2.1
  exact Cst2_le (L := ((49:ℝ)/(40))) (p := lam1) (c := ((122:ℝ)/(125))) (Pc := ((349967:ℝ)/(25000000)))
    (PLl := ((78181:ℝ)/(20000000))) (Wlc := ((12326251:ℝ)/(100000000))) (WLu := ((7651283:ℝ)/(100000000))) (r := ((770119:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((95641:ℝ)/(1250000))) hWL) hCf (by norm_num) (by norm_num)

-- row 8 (0.5..0.52), case cx: Lambda = 5/4, s = 13
theorem rowA_8_cx {lam1 : ℝ}
    (h1 : ((1:ℝ)/(2)) ≤ lam1) (h2 : lam1 ≤ ((13:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(2)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(2)))))/((1:ℝ)/(2)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((47:ℝ)/(50)) lam1 ≤ ((7084397:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((47:ℝ)/(50)) := by linarith
  have hpa : ((1:ℝ)/(2)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((1:ℝ)/(2)))) ≤ ((8629359:ℝ)/(100000000)) := exF_a_1_2
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((1:ℝ)/(2)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(2)) ≤ ((18670043:ℝ)/(10000000)) := (v_1_2).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(2)))))/((1:ℝ)/(2)))^2/((9:ℝ)/100) ≤ ((8623231:ℝ)/(10000000)) := (v_1_2).2.2.2.2.2.2
  have hPbA : ((28842203:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((13:ℝ)/(25)) := (v_13_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((13:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((1:ℝ)/(2))) (b := ((13:ℝ)/(25))) hp_c0 hpc hBF (exF_a_47_50) (exG_a_47_50)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_8_cx {lam1 : ℝ}
    (h1 : ((47:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((13:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((47:ℝ)/(50))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((530509:ℝ)/(50000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((47:ℝ)/(50)) ≤ ((52613:ℝ)/(3125000)) := (v_47_50).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((13196501:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((47:ℝ)/(50)) := (v_47_50).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((47:ℝ)/(50))) (Pc := ((52613:ℝ)/(3125000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((13196501:ℝ)/(100000000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((530509:ℝ)/(50000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 8 (0.5..0.52), case rr: Lambda = 5/4, s = 13
theorem rowA_8_rr {lam1 : ℝ}
    (h1 : ((1:ℝ)/(2)) ≤ lam1) (h2 : lam1 ≤ ((13:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(2)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(2)))))/((1:ℝ)/(2)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((47:ℝ)/(50)) lam1 ≤ ((7084397:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((47:ℝ)/(50)) := by linarith
  have hpa : ((1:ℝ)/(2)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((1:ℝ)/(2)))) ≤ ((8629359:ℝ)/(100000000)) := exF_a_1_2
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((1:ℝ)/(2)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(2)) ≤ ((18670043:ℝ)/(10000000)) := (v_1_2).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(2)))))/((1:ℝ)/(2)))^2/((9:ℝ)/100) ≤ ((8623231:ℝ)/(10000000)) := (v_1_2).2.2.2.2.2.2
  have hPbA : ((28842203:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((13:ℝ)/(25)) := (v_13_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((13:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((1:ℝ)/(2))) (b := ((13:ℝ)/(25))) hp_c0 hpc hBF (exF_a_47_50) (exG_a_47_50)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_8_rr {lam1 : ℝ}
    (h1 : ((47:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((13:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((47:ℝ)/(50))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((530509:ℝ)/(50000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((47:ℝ)/(50)) ≤ ((52613:ℝ)/(3125000)) := (v_47_50).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((13196501:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((47:ℝ)/(50)) := (v_47_50).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((47:ℝ)/(50))) (Pc := ((52613:ℝ)/(3125000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((13196501:ℝ)/(100000000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((530509:ℝ)/(50000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 9 (0.52..0.54), case cx: Lambda = 5/4, s = 14
theorem rowA_9_cx {lam1 : ℝ}
    (h1 : ((13:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((27:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((13:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((13:ℝ)/(25)))))/((13:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((453:ℝ)/(500)) lam1 ≤ ((6576779:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((453:ℝ)/(500)) := by linarith
  have hpa : ((13:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((13:ℝ)/(25)))) ≤ ((7823799:ℝ)/(100000000)) := exF_a_13_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((13:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((13:ℝ)/(25)) ≤ ((185811281:ℝ)/(100000000)) := (v_13_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((13:ℝ)/(25)))))/((13:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((2679049:ℝ)/(3125000)) := (v_13_25).2.2.2.2.2.2
  have hPbA : ((108612:ℝ)/(390625)) ≤ Work.LinnikAreas.A7.Wf ((27:ℝ)/(50)) := (v_27_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((27:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((13:ℝ)/(25))) (b := ((27:ℝ)/(50))) hp_c0 hpc hBF (exF_a_453_500) (exG_a_453_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_9_cx {lam1 : ℝ}
    (h1 : ((453:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((27:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((453:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((335091:ℝ)/(25000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((453:ℝ)/(500)) ≤ ((2004283:ℝ)/(100000000)) := (v_453_500).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((1759043:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((453:ℝ)/(500)) := (v_453_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((453:ℝ)/(500))) (Pc := ((2004283:ℝ)/(100000000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((1759043:ℝ)/(12500000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((335091:ℝ)/(25000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 9 (0.52..0.54), case rr: Lambda = 5/4, s = 14
theorem rowA_9_rr {lam1 : ℝ}
    (h1 : ((13:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((27:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((13:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((13:ℝ)/(25)))))/((13:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((453:ℝ)/(500)) lam1 ≤ ((6576779:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((453:ℝ)/(500)) := by linarith
  have hpa : ((13:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((13:ℝ)/(25)))) ≤ ((7823799:ℝ)/(100000000)) := exF_a_13_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((13:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((13:ℝ)/(25)) ≤ ((185811281:ℝ)/(100000000)) := (v_13_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((13:ℝ)/(25)))))/((13:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((2679049:ℝ)/(3125000)) := (v_13_25).2.2.2.2.2.2
  have hPbA : ((108612:ℝ)/(390625)) ≤ Work.LinnikAreas.A7.Wf ((27:ℝ)/(50)) := (v_27_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((27:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((13:ℝ)/(25))) (b := ((27:ℝ)/(50))) hp_c0 hpc hBF (exF_a_453_500) (exG_a_453_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_9_rr {lam1 : ℝ}
    (h1 : ((453:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((27:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((453:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((335091:ℝ)/(25000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((453:ℝ)/(500)) ≤ ((2004283:ℝ)/(100000000)) := (v_453_500).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((1759043:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((453:ℝ)/(500)) := (v_453_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((453:ℝ)/(500))) (Pc := ((2004283:ℝ)/(100000000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((1759043:ℝ)/(12500000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((335091:ℝ)/(25000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 10 (0.54..0.56), case cx: Lambda = 5/4, s = 15
theorem rowA_10_cx {lam1 : ℝ}
    (h1 : ((27:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((14:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((27:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((27:ℝ)/(50)))))/((27:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((437:ℝ)/(500)) lam1 ≤ ((615773:ℝ)/(10000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((437:ℝ)/(500)) := by linarith
  have hpa : ((27:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((27:ℝ)/(50)))) ≤ ((7093439:ℝ)/(100000000)) := exF_a_27_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((27:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((27:ℝ)/(50)) ≤ ((92464189:ℝ)/(50000000)) := (v_27_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((27:ℝ)/(50)))))/((27:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((2130757:ℝ)/(2500000)) := (v_27_50).2.2.2.2.2.2
  have hPbA : ((670071:ℝ)/(2500000)) ≤ Work.LinnikAreas.A7.Wf ((14:ℝ)/(25)) := (v_14_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((14:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((27:ℝ)/(50))) (b := ((14:ℝ)/(25))) hp_c0 hpc hBF (exF_a_437_500) (exG_a_437_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_10_cx {lam1 : ℝ}
    (h1 : ((437:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((14:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((437:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((1656543:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((437:ℝ)/(500)) ≤ ((590437:ℝ)/(25000000)) := (v_437_500).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((747371:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((437:ℝ)/(500)) := (v_437_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((437:ℝ)/(500))) (Pc := ((590437:ℝ)/(25000000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((747371:ℝ)/(5000000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((1656543:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 10 (0.54..0.56), case rr: Lambda = 5/4, s = 15
theorem rowA_10_rr {lam1 : ℝ}
    (h1 : ((27:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((14:ℝ)/(25)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((27:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((27:ℝ)/(50)))))/((27:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((437:ℝ)/(500)) lam1 ≤ ((615773:ℝ)/(10000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((437:ℝ)/(500)) := by linarith
  have hpa : ((27:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((27:ℝ)/(50)))) ≤ ((7093439:ℝ)/(100000000)) := exF_a_27_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((27:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((27:ℝ)/(50)) ≤ ((92464189:ℝ)/(50000000)) := (v_27_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((27:ℝ)/(50)))))/((27:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((2130757:ℝ)/(2500000)) := (v_27_50).2.2.2.2.2.2
  have hPbA : ((670071:ℝ)/(2500000)) ≤ Work.LinnikAreas.A7.Wf ((14:ℝ)/(25)) := (v_14_25).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((14:ℝ)/(25)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((27:ℝ)/(50))) (b := ((14:ℝ)/(25))) hp_c0 hpc hBF (exF_a_437_500) (exG_a_437_500)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_10_rr {lam1 : ℝ}
    (h1 : ((437:ℝ)/(500)) ≤ lam1) (h2 : lam1 ≤ ((14:ℝ)/(25)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((437:ℝ)/(500))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((1656543:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((437:ℝ)/(500)) ≤ ((590437:ℝ)/(25000000)) := (v_437_500).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((747371:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((437:ℝ)/(500)) := (v_437_500).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((437:ℝ)/(500))) (Pc := ((590437:ℝ)/(25000000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((747371:ℝ)/(5000000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((1656543:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 11 (0.56..0.58), case cx: Lambda = 5/4, s = 15
theorem rowA_11_cx {lam1 : ℝ}
    (h1 : ((14:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((29:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((14:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((211:ℝ)/(250)) lam1 ≤ ((5818981:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((211:ℝ)/(250)) := by linarith
  have hpa : ((14:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((14:ℝ)/(25)))) ≤ ((6431259:ℝ)/(100000000)) := exF_a_14_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((14:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((14:ℝ)/(25)) ≤ ((184051631:ℝ)/(100000000)) := (v_14_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((84734403:ℝ)/(100000000)) := (v_14_25).2.2.2.2.2.2
  have hPbA : ((12917771:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((29:ℝ)/(50)) := (v_29_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((29:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((14:ℝ)/(25))) (b := ((29:ℝ)/(50))) hp_c0 hpc hBF (exF_a_211_250) (exG_a_211_250)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_11_cx {lam1 : ℝ}
    (h1 : ((211:ℝ)/(250)) ≤ lam1) (h2 : lam1 ≤ ((29:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((211:ℝ)/(250))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((2008497:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((211:ℝ)/(250)) ≤ ((1377317:ℝ)/(50000000)) := (v_211_250).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((7907513:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((211:ℝ)/(250)) := (v_211_250).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((211:ℝ)/(250))) (Pc := ((1377317:ℝ)/(50000000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((7907513:ℝ)/(50000000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((2008497:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 11 (0.56..0.58), case rr: Lambda = 5/4, s = 15
theorem rowA_11_rr {lam1 : ℝ}
    (h1 : ((14:ℝ)/(25)) ≤ lam1) (h2 : lam1 ≤ ((29:ℝ)/(50)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((14:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 - Work.LinnikAreas.A7.Aref ((211:ℝ)/(250)) lam1 ≤ ((5818981:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((211:ℝ)/(250)) := by linarith
  have hpa : ((14:ℝ)/(25)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((14:ℝ)/(25)))) ≤ ((6431259:ℝ)/(100000000)) := exF_a_14_25
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((14:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((14:ℝ)/(25)) ≤ ((184051631:ℝ)/(100000000)) := (v_14_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((84734403:ℝ)/(100000000)) := (v_14_25).2.2.2.2.2.2
  have hPbA : ((12917771:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((29:ℝ)/(50)) := (v_29_50).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((29:ℝ)/(50)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst1_le (a := ((14:ℝ)/(25))) (b := ((29:ℝ)/(50))) hp_c0 hpc hBF (exF_a_211_250) (exG_a_211_250)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_11_rr {lam1 : ℝ}
    (h1 : ((211:ℝ)/(250)) ≤ lam1) (h2 : lam1 ≤ ((29:ℝ)/(50)))
    (hCf : Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) ((211:ℝ)/(250))) :
    Work.LinnikAreas.A7.Cf ((5:ℝ)/(4)) lam1 ≤ ((2008497:ℝ)/(100000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((211:ℝ)/(250)) ≤ ((1377317:ℝ)/(50000000)) := (v_211_250).1
  have hPL : ((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) := (v_5_4).2.1
  have hWlc : ((7907513:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((211:ℝ)/(250)) := (v_211_250).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) := (v_5_4).2.2.2.1
  exact Cst2_le (L := ((5:ℝ)/(4))) (p := lam1) (c := ((211:ℝ)/(250))) (Pc := ((1377317:ℝ)/(50000000)))
    (PLl := ((171971:ℝ)/(50000000))) (Wlc := ((7907513:ℝ)/(50000000))) (WLu := ((3645071:ℝ)/(50000000))) (r := ((2008497:ℝ)/(100000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 12 (0.58..0.6), case cx: Lambda = 51/40, s = 16
theorem rowA_12_cx {lam1 : ℝ}
    (h1 : ((29:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((3:ℝ)/(5)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((29:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((163:ℝ)/(200)) lam1 ≤ ((5651003:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((163:ℝ)/(200)) := by linarith
  have hpa : ((29:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((29:ℝ)/(50)))) ≤ ((2915447:ℝ)/(50000000)) := exF_a_29_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((29:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((29:ℝ)/(50)) ≤ ((18318101:ℝ)/(10000000)) := (v_29_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((84241919:ℝ)/(100000000)) := (v_29_50).2.2.2.2.2.2
  have hPbA : ((24901651:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((3:ℝ)/(5)) := (v_3_5).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((3:ℝ)/(5)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst1_le (a := ((29:ℝ)/(50))) (b := ((3:ℝ)/(5))) hp_c0 hpc hBF (exF_a_163_200) (exG_a_163_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_12_cx {lam1 : ℝ}
    (h1 : ((163:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((3:ℝ)/(5)))
    (hCf : Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) ((163:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ ((308611:ℝ)/(12500000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((163:ℝ)/(200)) ≤ ((3196511:ℝ)/(100000000)) := (v_163_200).1
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWlc : ((16699467:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((163:ℝ)/(200)) := (v_163_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst2_le (L := ((51:ℝ)/(40))) (p := lam1) (c := ((163:ℝ)/(200))) (Pc := ((3196511:ℝ)/(100000000)))
    (PLl := ((2421:ℝ)/(800000))) (Wlc := ((16699467:ℝ)/(100000000))) (WLu := ((6945459:ℝ)/(100000000))) (r := ((308611:ℝ)/(12500000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 12 (0.58..0.6), case rr: Lambda = 51/40, s = 16
theorem rowA_12_rr {lam1 : ℝ}
    (h1 : ((29:ℝ)/(50)) ≤ lam1) (h2 : lam1 ≤ ((3:ℝ)/(5)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((29:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((163:ℝ)/(200)) lam1 ≤ ((5651003:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((163:ℝ)/(200)) := by linarith
  have hpa : ((29:ℝ)/(50)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((29:ℝ)/(50)))) ≤ ((2915447:ℝ)/(50000000)) := exF_a_29_50
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((29:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((29:ℝ)/(50)) ≤ ((18318101:ℝ)/(10000000)) := (v_29_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((84241919:ℝ)/(100000000)) := (v_29_50).2.2.2.2.2.2
  have hPbA : ((24901651:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((3:ℝ)/(5)) := (v_3_5).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((3:ℝ)/(5)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst1_le (a := ((29:ℝ)/(50))) (b := ((3:ℝ)/(5))) hp_c0 hpc hBF (exF_a_163_200) (exG_a_163_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_12_rr {lam1 : ℝ}
    (h1 : ((163:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((3:ℝ)/(5)))
    (hCf : Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) ((163:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ ((308611:ℝ)/(12500000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((163:ℝ)/(200)) ≤ ((3196511:ℝ)/(100000000)) := (v_163_200).1
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWlc : ((16699467:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((163:ℝ)/(200)) := (v_163_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst2_le (L := ((51:ℝ)/(40))) (p := lam1) (c := ((163:ℝ)/(200))) (Pc := ((3196511:ℝ)/(100000000)))
    (PLl := ((2421:ℝ)/(800000))) (Wlc := ((16699467:ℝ)/(100000000))) (WLu := ((6945459:ℝ)/(100000000))) (r := ((308611:ℝ)/(12500000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 13 (0.6..inf), case cx: Lambda = 51/40, s = 16
theorem rowA_13_cx {lam1 : ℝ}
    (h1 : ((3:ℝ)/(5)) ≤ lam1) (h2 : lam1 ≤ ((139:ℝ)/(200)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((139:ℝ)/(200)) lam1 ≤ ((6788827:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((139:ℝ)/(200)) := by linarith
  have hpa : ((3:ℝ)/(5)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) ≤ ((5286573:ℝ)/(100000000)) := exF_a_3_5
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)) ≤ ((9115823:ℝ)/(5000000)) := (v_3_5).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((8375279:ℝ)/(10000000)) := (v_3_5).2.2.2.2.2.2
  have hPbA : ((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst1_le (a := ((3:ℝ)/(5))) (b := ((139:ℝ)/(200))) hp_c0 hpc hBF (exF_a_139_200) (exG_a_139_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_13_cx {lam1 : ℝ}
    (h1 : ((139:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((51:ℝ)/(40)))
    (hCf : Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) ((139:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ ((100147:ℝ)/(2000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((139:ℝ)/(200)) ≤ ((5917527:ℝ)/(100000000)) := (v_139_200).1
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWlc : ((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst2_le (L := ((51:ℝ)/(40))) (p := lam1) (c := ((139:ℝ)/(200))) (Pc := ((5917527:ℝ)/(100000000)))
    (PLl := ((2421:ℝ)/(800000))) (Wlc := ((20889217:ℝ)/(100000000))) (WLu := ((6945459:ℝ)/(100000000))) (r := ((100147:ℝ)/(2000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 13 (0.6..inf), case rr: Lambda = 51/40, s = 16
theorem rowA_13_rr {lam1 : ℝ}
    (h1 : ((3:ℝ)/(5)) ≤ lam1) (h2 : lam1 ≤ ((139:ℝ)/(200)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((139:ℝ)/(200)) lam1 ≤ ((6788827:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((139:ℝ)/(200)) := by linarith
  have hpa : ((3:ℝ)/(5)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) ≤ ((5286573:ℝ)/(100000000)) := exF_a_3_5
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)) ≤ ((9115823:ℝ)/(5000000)) := (v_3_5).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((8375279:ℝ)/(10000000)) := (v_3_5).2.2.2.2.2.2
  have hPbA : ((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst1_le (a := ((3:ℝ)/(5))) (b := ((139:ℝ)/(200))) hp_c0 hpc hBF (exF_a_139_200) (exG_a_139_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_13_rr {lam1 : ℝ}
    (h1 : ((139:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((51:ℝ)/(40)))
    (hCf : Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) ((139:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ ((100147:ℝ)/(2000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((139:ℝ)/(200)) ≤ ((5917527:ℝ)/(100000000)) := (v_139_200).1
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWlc : ((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst2_le (L := ((51:ℝ)/(40))) (p := lam1) (c := ((139:ℝ)/(200))) (Pc := ((5917527:ℝ)/(100000000)))
    (PLl := ((2421:ℝ)/(800000))) (Wlc := ((20889217:ℝ)/(100000000))) (WLu := ((6945459:ℝ)/(100000000))) (r := ((100147:ℝ)/(2000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)

-- row 13 (0.6..inf), case rc: Lambda = 51/40, s = 16
theorem rowA_13_rc {lam1 : ℝ}
    (h1 : ((3:ℝ)/(5)) ≤ lam1) (h2 : lam1 ≤ ((139:ℝ)/(200)))
    (hBfun_mono : Work.LinnikContract.Bfun ((3:ℝ)/10) lam1 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100))
    (hBF : ((1-Real.exp (-((3:ℝ)/10*lam1)))/lam1)^2/((9:ℝ)/100) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam1) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 - Work.LinnikAreas.A7.Aref ((139:ℝ)/(200)) lam1 ≤ ((6788827:ℝ)/(100000000)) := by
  have hp_c0 : (0:ℝ) < lam1 := by linarith
  have hpc : lam1 ≤ ((139:ℝ)/(200)) := by linarith
  have hpa : ((3:ℝ)/(5)) ≤ lam1 := h1
  have hEa : Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) ≤ ((5286573:ℝ)/(100000000)) := exF_a_3_5
  have hEaL : Real.exp (-((49:ℝ)/10*lam1)) ≤ Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)) ≤ ((9115823:ℝ)/(5000000)) := (v_3_5).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((8375279:ℝ)/(10000000)) := (v_3_5).2.2.2.2.2.2
  have hPbA : ((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWp : Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) ≤ Work.LinnikAreas.A7.Wf lam1 := Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst1_le (a := ((3:ℝ)/(5))) (b := ((139:ℝ)/(200))) hp_c0 hpc hBF (exF_a_139_200) (exG_a_139_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hPbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

theorem rowB_13_rc {lam1 : ℝ}
    (h1 : ((139:ℝ)/(200)) ≤ lam1) (h2 : lam1 ≤ ((51:ℝ)/(40)))
    (hCf : Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) ((139:ℝ)/(200))) :
    Work.LinnikAreas.A7.Cf ((51:ℝ)/(40)) lam1 ≤ ((100147:ℝ)/(2000000)) := by
  have hPc : Work.LinnikAreas.A7.Phi ((139:ℝ)/(200)) ≤ ((5917527:ℝ)/(100000000)) := (v_139_200).1
  have hPL : ((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) := (v_51_40).2.1
  have hWlc : ((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWU : Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) := (v_51_40).2.2.2.1
  exact Cst2_le (L := ((51:ℝ)/(40))) (p := lam1) (c := ((139:ℝ)/(200))) (Pc := ((5917527:ℝ)/(100000000)))
    (PLl := ((2421:ℝ)/(800000))) (Wlc := ((20889217:ℝ)/(100000000))) (WLu := ((6945459:ℝ)/(100000000))) (r := ((100147:ℝ)/(2000000)))
    hPc hPL (by norm_num) hWlc (by norm_num) hWU
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) hCf (by norm_num) (by norm_num)


end Work.LinnikAreas.A7
