import Mathlib
import Submission.Work.LinnikAreas.A7.ValueLemmas
import Submission.Work.LinnikAreas.A7.NumExp

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

lemma v_1_5 :
    (Work.LinnikAreas.A7.Phi ((1:ℝ)/(5)) ≤ ((37685087:ℝ)/(50000000))) ∧
    (((15074023:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((1:ℝ)/(5))) ∧
    (Work.LinnikAreas.A7.Wf ((1:ℝ)/(5)) ≤ ((25701191:ℝ)/(50000000))) ∧
    (((25701189:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((1:ℝ)/(5))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(5)) ≤ ((12551283:ℝ)/(6250000))) ∧
    (((200820379:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(5))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(5)))))/((1:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((47102361:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((1:ℝ)/(5)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1:ℝ)/(5)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((3753111:ℝ)/(10000000))) (B := ((12551283:ℝ)/(6250000))) hq exF_a_1_5 (Bfun_le (r := ((12551283:ℝ)/(6250000))) hq exG_b_1_5 exF_b_1_5 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((37531109:ℝ)/(100000000))) (B := ((200820379:ℝ)/(100000000))) hq exG_a_1_5 (Bfun_ge (r := ((200820379:ℝ)/(100000000))) hq exG_b_1_5 exF_b_1_5 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((61467189:ℝ)/(100000000))) (Qu := ((38041957:ℝ)/(50000000))) (r := ((25701191:ℝ)/(50000000))) hqle (by norm_num) exF_d_1_5 exF_e_1_5 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((15366797:ℝ)/(25000000))) (Ql := ((76083913:ℝ)/(100000000))) (r := ((25701189:ℝ)/(50000000))) hq exG_d_1_5 exG_e_1_5 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((12551283:ℝ)/(6250000))) hq exG_b_1_5 exF_b_1_5 (by norm_num)
  · exact Bfun_ge (r := ((200820379:ℝ)/(100000000))) hq exG_b_1_5 exF_b_1_5 (by norm_num)
  · exact F2K2_le (al := ((94176453:ℝ)/(100000000))) (r := ((47102361:ℝ)/(50000000))) hq exG_c_1_5 (by norm_num)

lemma v_1_4 :
    (Work.LinnikAreas.A7.Phi ((1:ℝ)/(4)) ≤ ((58270169:ℝ)/(100000000))) ∧
    (((29135069:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((1:ℝ)/(4))) ∧
    (Work.LinnikAreas.A7.Wf ((1:ℝ)/(4)) ≤ ((734587:ℝ)/(1562500))) ∧
    (((9402713:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((1:ℝ)/(4))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(4)) ≤ ((99180663:ℝ)/(50000000))) ∧
    (((198361229:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(4))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(4)))))/((1:ℝ)/(4)))^2/((9:ℝ)/100) ≤ ((46408931:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((1:ℝ)/(4)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1:ℝ)/(4)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((29375771:ℝ)/(100000000))) (B := ((99180663:ℝ)/(50000000))) hq exF_a_1_4 (Bfun_le (r := ((99180663:ℝ)/(50000000))) hq exG_b_1_4 exF_b_1_4 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((2937577:ℝ)/(10000000))) (B := ((198361229:ℝ)/(100000000))) hq exG_a_1_4 (Bfun_ge (r := ((198361229:ℝ)/(100000000))) hq exG_b_1_4 exF_b_1_4 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((54425721:ℝ)/(100000000))) (Qu := ((71058503:ℝ)/(100000000))) (r := ((734587:ℝ)/(1562500))) hqle (by norm_num) exF_d_1_4 exF_e_1_4 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1360643:ℝ)/(2500000))) (Ql := ((35529251:ℝ)/(50000000))) (r := ((9402713:ℝ)/(20000000))) hq exG_d_1_4 exG_e_1_4 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((99180663:ℝ)/(50000000))) hq exG_b_1_4 exF_b_1_4 (by norm_num)
  · exact Bfun_ge (r := ((198361229:ℝ)/(100000000))) hq exG_b_1_4 exF_b_1_4 (by norm_num)
  · exact F2K2_le (al := ((23193587:ℝ)/(25000000))) (r := ((46408931:ℝ)/(50000000))) hq exG_c_1_4 (by norm_num)

lemma v_3_10 :
    (Work.LinnikAreas.A7.Phi ((3:ℝ)/(10)) ≤ ((9010581:ℝ)/(20000000))) ∧
    (((45052887:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((3:ℝ)/(10))) ∧
    (Work.LinnikAreas.A7.Wf ((3:ℝ)/(10)) ≤ ((42982849:ℝ)/(100000000))) ∧
    (((21491423:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((3:ℝ)/(10))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(10)) ≤ ((195945673:ℝ)/(100000000))) ∧
    (((48986401:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(10))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(10)))))/((3:ℝ)/(10)))^2/((9:ℝ)/100) ≤ ((91454837:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((3:ℝ)/(10)) := by norm_num
  have hqle : (0:ℝ) ≤ ((3:ℝ)/(10)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((22992549:ℝ)/(100000000))) (B := ((195945673:ℝ)/(100000000))) hq exF_a_3_10 (Bfun_le (r := ((195945673:ℝ)/(100000000))) hq exG_b_3_10 exF_b_3_10 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((5748137:ℝ)/(25000000))) (B := ((48986401:ℝ)/(25000000))) hq exG_a_3_10 (Bfun_ge (r := ((48986401:ℝ)/(25000000))) hq exG_b_3_10 exF_b_3_10 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((481909:ℝ)/(1000000))) (Qu := ((33182513:ℝ)/(50000000))) (r := ((42982849:ℝ)/(100000000))) hqle (by norm_num) exF_d_3_10 exF_e_3_10 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((48190899:ℝ)/(100000000))) (Ql := ((2654601:ℝ)/(4000000))) (r := ((21491423:ℝ)/(50000000))) hq exG_d_3_10 exG_e_3_10 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((195945673:ℝ)/(100000000))) hq exG_b_3_10 exF_b_3_10 (by norm_num)
  · exact Bfun_ge (r := ((48986401:ℝ)/(25000000))) hq exG_b_3_10 exF_b_3_10 (by norm_num)
  · exact F2K2_le (al := ((45696559:ℝ)/(50000000))) (r := ((91454837:ℝ)/(100000000))) hq exG_c_3_10 (by norm_num)

lemma v_87_250 :
    (Work.LinnikAreas.A7.Phi ((87:ℝ)/(250)) ≤ ((549941:ℝ)/(1562500))) ∧
    (((35196211:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((87:ℝ)/(250))) ∧
    (Work.LinnikAreas.A7.Wf ((87:ℝ)/(250)) ≤ ((39424539:ℝ)/(100000000))) ∧
    (((4928067:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((87:ℝ)/(250))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(250)) ≤ ((193666723:ℝ)/(100000000))) ∧
    (((193666671:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(250))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((87:ℝ)/(250)))))/((87:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((90168359:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((87:ℝ)/(250)) := by norm_num
  have hqle : (0:ℝ) ≤ ((87:ℝ)/(250)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((4543401:ℝ)/(25000000))) (B := ((193666723:ℝ)/(100000000))) hq exF_a_87_250 (Bfun_le (r := ((193666723:ℝ)/(100000000))) hq exG_b_87_250 exF_b_87_250 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((18173603:ℝ)/(100000000))) (B := ((193666671:ℝ)/(100000000))) hq exG_a_87_250 (Bfun_ge (r := ((193666671:ℝ)/(100000000))) hq exG_b_87_250 exF_b_87_250 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((21439243:ℝ)/(50000000))) (Qu := ((15537801:ℝ)/(25000000))) (r := ((39424539:ℝ)/(100000000))) hqle (by norm_num) exF_d_87_250 exF_e_87_250 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((8575697:ℝ)/(20000000))) (Ql := ((62151203:ℝ)/(100000000))) (r := ((4928067:ℝ)/(12500000))) hq exG_d_87_250 exG_e_87_250 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((193666723:ℝ)/(100000000))) hq exG_b_87_250 exF_b_87_250 (by norm_num)
  · exact Bfun_ge (r := ((193666671:ℝ)/(100000000))) hq exG_b_87_250 exF_b_87_250 (by norm_num)
  · exact F2K2_le (al := ((90086487:ℝ)/(100000000))) (r := ((90168359:ℝ)/(100000000))) hq exG_c_87_250 (by norm_num)

lemma v_9_25 :
    (Work.LinnikAreas.A7.Phi ((9:ℝ)/(25)) ≤ ((33089761:ℝ)/(100000000))) ∧
    (((33089749:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((9:ℝ)/(25))) ∧
    (Work.LinnikAreas.A7.Wf ((9:ℝ)/(25)) ≤ ((19289919:ℝ)/(50000000))) ∧
    (((7715967:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((9:ℝ)/(25))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(25)) ≤ ((193103027:ℝ)/(100000000))) ∧
    (((96551489:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(25))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(25)))))/((9:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((17970011:ℝ)/(20000000))) := by
  have hq : (0:ℝ) < ((9:ℝ)/(25)) := by norm_num
  have hqle : (0:ℝ) ≤ ((9:ℝ)/(25)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((8567903:ℝ)/(50000000))) (B := ((193103027:ℝ)/(100000000))) hq exF_a_9_25 (Bfun_le (r := ((193103027:ℝ)/(100000000))) hq exG_b_9_25 exF_b_9_25 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((3427161:ℝ)/(20000000))) (B := ((96551489:ℝ)/(50000000))) hq exG_a_9_25 (Bfun_ge (r := ((96551489:ℝ)/(50000000))) hq exG_b_9_25 exF_b_9_25 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((41644537:ℝ)/(100000000))) (Qu := ((61140237:ℝ)/(100000000))) (r := ((19289919:ℝ)/(50000000))) hqle (by norm_num) exF_d_9_25 exF_e_9_25 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5205567:ℝ)/(12500000))) (Ql := ((15285059:ℝ)/(25000000))) (r := ((7715967:ℝ)/(20000000))) hq exG_d_9_25 exG_e_9_25 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((193103027:ℝ)/(100000000))) hq exG_b_9_25 exF_b_9_25 (by norm_num)
  · exact Bfun_ge (r := ((96551489:ℝ)/(50000000))) hq exG_b_9_25 exF_b_9_25 (by norm_num)
  · exact F2K2_le (al := ((89762759:ℝ)/(100000000))) (r := ((17970011:ℝ)/(20000000))) hq exG_c_9_25 (by norm_num)

lemma v_19_50 :
    (Work.LinnikAreas.A7.Phi ((19:ℝ)/(50)) ≤ ((29855657:ℝ)/(100000000))) ∧
    (((29855647:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((19:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((19:ℝ)/(50)) ≤ ((37210199:ℝ)/(100000000))) ∧
    (((9302549:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Wf ((19:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(50)) ≤ ((48042207:ℝ)/(25000000))) ∧
    (((12010549:ℝ)/(6250000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((19:ℝ)/(50)))))/((19:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((89322479:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((19:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((19:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((97101:ℝ)/(625000))) (B := ((48042207:ℝ)/(25000000))) hq exF_a_19_50 (Bfun_le (r := ((48042207:ℝ)/(25000000))) hq exG_b_19_50 exF_b_19_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((15536159:ℝ)/(100000000))) (B := ((12010549:ℝ)/(6250000))) hq exG_a_19_50 (Bfun_ge (r := ((12010549:ℝ)/(6250000))) hq exG_b_19_50 exF_b_19_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((19833181:ℝ)/(50000000))) (Qu := ((59491703:ℝ)/(100000000))) (r := ((37210199:ℝ)/(100000000))) hqle (by norm_num) exF_d_19_50 exF_e_19_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((39666361:ℝ)/(100000000))) (Ql := ((29745851:ℝ)/(50000000))) (r := ((9302549:ℝ)/(25000000))) hq exG_d_19_50 exG_e_19_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((48042207:ℝ)/(25000000))) hq exG_b_19_50 exF_b_19_50 (by norm_num)
  · exact Bfun_ge (r := ((12010549:ℝ)/(6250000))) hq exG_b_19_50 exF_b_19_50 (by norm_num)
  · exact F2K2_le (al := ((17845159:ℝ)/(20000000))) (r := ((89322479:ℝ)/(100000000))) hq exG_c_19_50 (by norm_num)

lemma v_2_5 :
    (Work.LinnikAreas.A7.Phi ((2:ℝ)/(5)) ≤ ((26937947:ℝ)/(100000000))) ∧
    (((13468969:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((2:ℝ)/(5))) ∧
    (Work.LinnikAreas.A7.Wf ((2:ℝ)/(5)) ≤ ((1794349:ℝ)/(5000000))) ∧
    (((35886977:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((2:ℝ)/(5))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((2:ℝ)/(5)) ≤ ((191241281:ℝ)/(100000000))) ∧
    (((4781031:ℝ)/(2500000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((2:ℝ)/(5))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((2:ℝ)/(5)))))/((2:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((11099817:ℝ)/(12500000))) := by
  have hq : (0:ℝ) < ((2:ℝ)/(5)) := by norm_num
  have hqle : (0:ℝ) ≤ ((2:ℝ)/(5)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((14085843:ℝ)/(100000000))) (B := ((191241281:ℝ)/(100000000))) hq exF_a_2_5 (Bfun_le (r := ((191241281:ℝ)/(100000000))) hq exG_b_2_5 exF_b_2_5 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((7042921:ℝ)/(50000000))) (B := ((4781031:ℝ)/(2500000))) hq exG_a_2_5 (Bfun_ge (r := ((4781031:ℝ)/(2500000))) hq exG_b_2_5 exF_b_2_5 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((18891077:ℝ)/(50000000))) (Qu := ((57887619:ℝ)/(100000000))) (r := ((1794349:ℝ)/(5000000))) hqle (by norm_num) exF_d_2_5 exF_e_2_5 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((37782153:ℝ)/(100000000))) (Ql := ((28943809:ℝ)/(50000000))) (r := ((35886977:ℝ)/(100000000))) hq exG_d_2_5 exG_e_2_5 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((191241281:ℝ)/(100000000))) hq exG_b_2_5 exF_b_2_5 (by norm_num)
  · exact Bfun_ge (r := ((4781031:ℝ)/(2500000))) hq exG_b_2_5 exF_b_2_5 (by norm_num)
  · exact F2K2_le (al := ((88692043:ℝ)/(100000000))) (r := ((11099817:ℝ)/(12500000))) hq exG_c_2_5 (by norm_num)

lemma v_21_50 :
    (Work.LinnikAreas.A7.Phi ((21:ℝ)/(50)) ≤ ((24305633:ℝ)/(100000000))) ∧
    (((38889:ℝ)/(160000)) ≤ Work.LinnikAreas.A7.Phi ((21:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((21:ℝ)/(50)) ≤ ((34608693:ℝ)/(100000000))) ∧
    (((3460869:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Wf ((21:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(50)) ≤ ((7612809:ℝ)/(4000000))) ∧
    (((47580047:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((21:ℝ)/(50)))))/((21:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((17655639:ℝ)/(20000000))) := by
  have hq : (0:ℝ) < ((21:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((21:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((6385457:ℝ)/(50000000))) (B := ((7612809:ℝ)/(4000000))) hq exF_a_21_50 (Bfun_le (r := ((7612809:ℝ)/(4000000))) hq exG_b_21_50 exF_b_21_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((12770913:ℝ)/(100000000))) (B := ((47580047:ℝ)/(25000000))) hq exG_a_21_50 (Bfun_ge (r := ((47580047:ℝ)/(25000000))) hq exG_b_21_50 exF_b_21_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((4498431:ℝ)/(12500000))) (Qu := ((28163393:ℝ)/(50000000))) (r := ((34608693:ℝ)/(100000000))) hqle (by norm_num) exF_d_21_50 exF_e_21_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((35987447:ℝ)/(100000000))) (Ql := ((11265357:ℝ)/(20000000))) (r := ((3460869:ℝ)/(10000000))) hq exG_d_21_50 exG_e_21_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((7612809:ℝ)/(4000000))) hq exG_b_21_50 exF_b_21_50 (by norm_num)
  · exact Bfun_ge (r := ((47580047:ℝ)/(25000000))) hq exG_b_21_50 exF_b_21_50 (by norm_num)
  · exact F2K2_le (al := ((22040371:ℝ)/(25000000))) (r := ((17655639:ℝ)/(20000000))) hq exG_c_21_50 (by norm_num)

lemma v_11_25 :
    (Work.LinnikAreas.A7.Phi ((11:ℝ)/(25)) ≤ ((10965391:ℝ)/(50000000))) ∧
    (((877231:ℝ)/(4000000)) ≤ Work.LinnikAreas.A7.Phi ((11:ℝ)/(25))) ∧
    (Work.LinnikAreas.A7.Wf ((11:ℝ)/(25)) ≤ ((33373893:ℝ)/(100000000))) ∧
    (((33373891:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((11:ℝ)/(25))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(25)) ≤ ((94702837:ℝ)/(50000000))) ∧
    (((4735141:ℝ)/(2500000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(25))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((11:ℝ)/(25)))))/((11:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((43880713:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((11:ℝ)/(25)) := by norm_num
  have hqle : (0:ℝ) ≤ ((11:ℝ)/(25)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((2315747:ℝ)/(20000000))) (B := ((94702837:ℝ)/(50000000))) hq exF_a_11_25 (Bfun_le (r := ((94702837:ℝ)/(50000000))) hq exG_b_11_25 exF_b_11_25 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((5789367:ℝ)/(50000000))) (B := ((4735141:ℝ)/(2500000))) hq exG_a_11_25 (Bfun_ge (r := ((4735141:ℝ)/(2500000))) hq exG_b_11_25 exF_b_11_25 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((34277993:ℝ)/(100000000))) (Qu := ((27404019:ℝ)/(50000000))) (r := ((33373893:ℝ)/(100000000))) hqle (by norm_num) exF_d_11_25 exF_e_11_25 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4284749:ℝ)/(12500000))) (Ql := ((54808037:ℝ)/(100000000))) (r := ((33373891:ℝ)/(100000000))) hq exG_d_11_25 exG_e_11_25 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((94702837:ℝ)/(50000000))) hq exG_b_11_25 exF_b_11_25 (by norm_num)
  · exact Bfun_ge (r := ((4735141:ℝ)/(2500000))) hq exG_b_11_25 exF_b_11_25 (by norm_num)
  · exact F2K2_le (al := ((87634099:ℝ)/(100000000))) (r := ((43880713:ℝ)/(50000000))) hq exG_c_11_25 (by norm_num)

lemma v_23_50 :
    (Work.LinnikAreas.A7.Phi ((23:ℝ)/(50)) ≤ ((4947047:ℝ)/(25000000))) ∧
    (((9894091:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((23:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((23:ℝ)/(50)) ≤ ((16090591:ℝ)/(50000000))) ∧
    (((32181179:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((23:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(50)) ≤ ((94248789:ℝ)/(50000000))) ∧
    (((188497547:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((23:ℝ)/(50)))))/((23:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((87248203:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((23:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((23:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((10497847:ℝ)/(100000000))) (B := ((94248789:ℝ)/(50000000))) hq exF_a_23_50 (Bfun_le (r := ((94248789:ℝ)/(50000000))) hq exG_b_23_50 exF_b_23_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((5248923:ℝ)/(50000000))) (B := ((188497547:ℝ)/(100000000))) hq exG_a_23_50 (Bfun_ge (r := ((188497547:ℝ)/(100000000))) hq exG_b_23_50 exF_b_23_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((32649739:ℝ)/(100000000))) (Qu := ((166657:ℝ)/(312500))) (r := ((16090591:ℝ)/(50000000))) hqle (by norm_num) exF_d_23_50 exF_e_23_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((16324869:ℝ)/(50000000))) (Ql := ((53330239:ℝ)/(100000000))) (r := ((32181179:ℝ)/(100000000))) hq exG_d_23_50 exG_e_23_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((94248789:ℝ)/(50000000))) hq exG_b_23_50 exF_b_23_50 (by norm_num)
  · exact Bfun_ge (r := ((188497547:ℝ)/(100000000))) hq exG_b_23_50 exF_b_23_50 (by norm_num)
  · exact F2K2_le (al := ((87109869:ℝ)/(100000000))) (r := ((87248203:ℝ)/(100000000))) hq exG_c_23_50 (by norm_num)

lemma v_12_25 :
    (Work.LinnikAreas.A7.Phi ((12:ℝ)/(25)) ≤ ((17855113:ℝ)/(100000000))) ∧
    (((4463777:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Phi ((12:ℝ)/(25))) ∧
    (Work.LinnikAreas.A7.Wf ((12:ℝ)/(25)) ≤ ((15514601:ℝ)/(50000000))) ∧
    (((31029199:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((12:ℝ)/(25))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((12:ℝ)/(25)) ≤ ((93797919:ℝ)/(50000000))) ∧
    (((187595809:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((12:ℝ)/(25))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((12:ℝ)/(25)))))/((12:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((17347703:ℝ)/(20000000))) := by
  have hq : (0:ℝ) < ((12:ℝ)/(25)) := by norm_num
  have hqle : (0:ℝ) ≤ ((12:ℝ)/(25)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((4758931:ℝ)/(50000000))) (B := ((93797919:ℝ)/(50000000))) hq exF_a_12_25 (Bfun_le (r := ((93797919:ℝ)/(50000000))) hq exG_b_12_25 exF_b_12_25 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((9517861:ℝ)/(100000000))) (B := ((187595809:ℝ)/(100000000))) hq exG_a_12_25 (Bfun_ge (r := ((187595809:ℝ)/(100000000))) hq exG_b_12_25 exF_b_12_25 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((3109883:ℝ)/(10000000))) (Qu := ((51892289:ℝ)/(100000000))) (r := ((15514601:ℝ)/(50000000))) hqle (by norm_num) exF_d_12_25 exF_e_12_25 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((31098829:ℝ)/(100000000))) (Ql := ((810817:ℝ)/(1562500))) (r := ((31029199:ℝ)/(100000000))) hq exG_d_12_25 exG_e_12_25 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((93797919:ℝ)/(50000000))) hq exG_b_12_25 exF_b_12_25 (by norm_num)
  · exact Bfun_ge (r := ((187595809:ℝ)/(100000000))) hq exG_b_12_25 exF_b_12_25 (by norm_num)
  · exact F2K2_le (al := ((43294387:ℝ)/(50000000))) (r := ((17347703:ℝ)/(20000000))) hq exG_c_12_25 (by norm_num)

lemma v_1_2 :
    (Work.LinnikAreas.A7.Phi ((1:ℝ)/(2)) ≤ ((16111051:ℝ)/(100000000))) ∧
    (((8055523:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((1:ℝ)/(2))) ∧
    (Work.LinnikAreas.A7.Wf ((1:ℝ)/(2)) ≤ ((5983327:ℝ)/(20000000))) ∧
    (((3739579:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((1:ℝ)/(2))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(2)) ≤ ((18670043:ℝ)/(10000000))) ∧
    (((186700403:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(2))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(2)))))/((1:ℝ)/(2)))^2/((9:ℝ)/100) ≤ ((8623231:ℝ)/(10000000))) := by
  have hq : (0:ℝ) < ((1:ℝ)/(2)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1:ℝ)/(2)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((8629359:ℝ)/(100000000))) (B := ((18670043:ℝ)/(10000000))) hq exF_a_1_2 (Bfun_le (r := ((18670043:ℝ)/(10000000))) hq exG_b_1_2 exF_b_1_2 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((4314679:ℝ)/(50000000))) (B := ((186700403:ℝ)/(100000000))) hq exG_a_1_2 (Bfun_ge (r := ((186700403:ℝ)/(100000000))) hq exG_b_1_2 exF_b_1_2 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((29621591:ℝ)/(100000000))) (Qu := ((50493109:ℝ)/(100000000))) (r := ((5983327:ℝ)/(20000000))) hqle (by norm_num) exF_d_1_2 exF_e_1_2 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((2962159:ℝ)/(10000000))) (Ql := ((12623277:ℝ)/(25000000))) (r := ((3739579:ℝ)/(12500000))) hq exG_d_1_2 exG_e_1_2 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((18670043:ℝ)/(10000000))) hq exG_b_1_2 exF_b_1_2 (by norm_num)
  · exact Bfun_ge (r := ((186700403:ℝ)/(100000000))) hq exG_b_1_2 exF_b_1_2 (by norm_num)
  · exact F2K2_le (al := ((86070797:ℝ)/(100000000))) (r := ((8623231:ℝ)/(10000000))) hq exG_c_1_2 (by norm_num)

lemma v_13_25 :
    (Work.LinnikAreas.A7.Phi ((13:ℝ)/(25)) ≤ ((7268751:ℝ)/(50000000))) ∧
    (((14537497:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((13:ℝ)/(25))) ∧
    (Work.LinnikAreas.A7.Wf ((13:ℝ)/(25)) ≤ ((14421103:ℝ)/(50000000))) ∧
    (((28842203:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((13:ℝ)/(25))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((13:ℝ)/(25)) ≤ ((185811281:ℝ)/(100000000))) ∧
    (((23226407:ℝ)/(12500000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((13:ℝ)/(25))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((13:ℝ)/(25)))))/((13:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((2679049:ℝ)/(3125000))) := by
  have hq : (0:ℝ) < ((13:ℝ)/(25)) := by norm_num
  have hqle : (0:ℝ) ≤ ((13:ℝ)/(25)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((7823799:ℝ)/(100000000))) (B := ((185811281:ℝ)/(100000000))) hq exF_a_13_25 (Bfun_le (r := ((185811281:ℝ)/(100000000))) hq exG_b_13_25 exF_b_13_25 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((3911899:ℝ)/(50000000))) (B := ((23226407:ℝ)/(12500000))) hq exG_a_13_25 (Bfun_ge (r := ((23226407:ℝ)/(12500000))) hq exG_b_13_25 exF_b_13_25 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((7053631:ℝ)/(25000000))) (Qu := ((9826331:ℝ)/(20000000))) (r := ((14421103:ℝ)/(50000000))) hqle (by norm_num) exF_d_13_25 exF_e_13_25 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((28214523:ℝ)/(100000000))) (Ql := ((24565827:ℝ)/(50000000))) (r := ((28842203:ℝ)/(100000000))) hq exG_d_13_25 exG_e_13_25 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((185811281:ℝ)/(100000000))) hq exG_b_13_25 exF_b_13_25 (by norm_num)
  · exact Bfun_ge (r := ((23226407:ℝ)/(12500000))) hq exG_b_13_25 exF_b_13_25 (by norm_num)
  · exact F2K2_le (al := ((85555919:ℝ)/(100000000))) (r := ((2679049:ℝ)/(3125000))) hq exG_c_13_25 (by norm_num)

lemma v_27_50 :
    (Work.LinnikAreas.A7.Phi ((27:ℝ)/(50)) ≤ ((6558891:ℝ)/(50000000))) ∧
    (((6558889:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((27:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((27:ℝ)/(50)) ≤ ((1112187:ℝ)/(4000000))) ∧
    (((108612:ℝ)/(390625)) ≤ Work.LinnikAreas.A7.Wf ((27:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((27:ℝ)/(50)) ≤ ((92464189:ℝ)/(50000000))) ∧
    (((36985671:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((27:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((27:ℝ)/(50)))))/((27:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((2130757:ℝ)/(2500000))) := by
  have hq : (0:ℝ) < ((27:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((27:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((7093439:ℝ)/(100000000))) (B := ((92464189:ℝ)/(50000000))) hq exF_a_27_50 (Bfun_le (r := ((92464189:ℝ)/(50000000))) hq exG_b_27_50 exF_b_27_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((3546719:ℝ)/(50000000))) (B := ((36985671:ℝ)/(20000000))) hq exG_a_27_50 (Bfun_ge (r := ((36985671:ℝ)/(20000000))) hq exG_b_27_50 exF_b_27_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((13437147:ℝ)/(50000000))) (Qu := ((4780691:ℝ)/(10000000))) (r := ((1112187:ℝ)/(4000000))) hqle (by norm_num) exF_d_27_50 exF_e_27_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((26874293:ℝ)/(100000000))) (Ql := ((47806909:ℝ)/(100000000))) (r := ((108612:ℝ)/(390625))) hq exG_d_27_50 exG_e_27_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((92464189:ℝ)/(50000000))) hq exG_b_27_50 exF_b_27_50 (by norm_num)
  · exact Bfun_ge (r := ((36985671:ℝ)/(20000000))) hq exG_b_27_50 exF_b_27_50 (by norm_num)
  · exact F2K2_le (al := ((2126103:ℝ)/(2500000))) (r := ((2130757:ℝ)/(2500000))) hq exG_c_27_50 (by norm_num)

lemma v_14_25 :
    (Work.LinnikAreas.A7.Phi ((14:ℝ)/(25)) ≤ ((5918419:ℝ)/(50000000))) ∧
    (((11836833:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((14:ℝ)/(25))) ∧
    (Work.LinnikAreas.A7.Wf ((14:ℝ)/(25)) ≤ ((13401421:ℝ)/(50000000))) ∧
    (((670071:ℝ)/(2500000)) ≤ Work.LinnikAreas.A7.Wf ((14:ℝ)/(25))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((14:ℝ)/(25)) ≤ ((184051631:ℝ)/(100000000))) ∧
    (((184051609:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((14:ℝ)/(25))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((84734403:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((14:ℝ)/(25)) := by norm_num
  have hqle : (0:ℝ) ≤ ((14:ℝ)/(25)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((6431259:ℝ)/(100000000))) (B := ((184051631:ℝ)/(100000000))) hq exF_a_14_25 (Bfun_le (r := ((184051631:ℝ)/(100000000))) hq exG_b_14_25 exF_b_14_25 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((3215629:ℝ)/(50000000))) (B := ((184051609:ℝ)/(100000000))) hq exG_a_14_25 (Bfun_ge (r := ((184051609:ℝ)/(100000000))) hq exG_b_14_25 exF_b_14_25 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12798863:ℝ)/(50000000))) (Qu := ((9303577:ℝ)/(20000000))) (r := ((13401421:ℝ)/(50000000))) hqle (by norm_num) exF_d_14_25 exF_e_14_25 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1023909:ℝ)/(4000000))) (Ql := ((11629471:ℝ)/(25000000))) (r := ((670071:ℝ)/(2500000))) hq exG_d_14_25 exG_e_14_25 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((184051631:ℝ)/(100000000))) hq exG_b_14_25 exF_b_14_25 (by norm_num)
  · exact Bfun_ge (r := ((184051609:ℝ)/(100000000))) hq exG_b_14_25 exF_b_14_25 (by norm_num)
  · exact F2K2_le (al := ((84535383:ℝ)/(100000000))) (r := ((84734403:ℝ)/(100000000))) hq exG_c_14_25 (by norm_num)

lemma v_29_50 :
    (Work.LinnikAreas.A7.Phi ((29:ℝ)/(50)) ≤ ((10681091:ℝ)/(100000000))) ∧
    (((10681087:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((29:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((29:ℝ)/(50)) ≤ ((5167109:ℝ)/(20000000))) ∧
    (((12917771:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((29:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((29:ℝ)/(50)) ≤ ((18318101:ℝ)/(10000000))) ∧
    (((18318099:ℝ)/(10000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((29:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((84241919:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((29:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((29:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((2915447:ℝ)/(50000000))) (B := ((18318101:ℝ)/(10000000))) hq exF_a_29_50 (Bfun_le (r := ((18318101:ℝ)/(10000000))) hq exG_b_29_50 exF_b_29_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((5830893:ℝ)/(100000000))) (B := ((18318099:ℝ)/(10000000))) hq exG_a_29_50 (Bfun_ge (r := ((18318099:ℝ)/(10000000))) hq exG_b_29_50 exF_b_29_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12190899:ℝ)/(50000000))) (Qu := ((176811:ℝ)/(390625))) (r := ((5167109:ℝ)/(20000000))) hqle (by norm_num) exF_d_29_50 exF_e_29_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((24381797:ℝ)/(100000000))) (Ql := ((9052723:ℝ)/(20000000))) (r := ((12917771:ℝ)/(50000000))) hq exG_d_29_50 exG_e_29_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((18318101:ℝ)/(10000000))) hq exG_b_29_50 exF_b_29_50 (by norm_num)
  · exact Bfun_ge (r := ((18318099:ℝ)/(10000000))) hq exG_b_29_50 exF_b_29_50 (by norm_num)
  · exact F2K2_le (al := ((84029689:ℝ)/(100000000))) (r := ((84241919:ℝ)/(100000000))) hq exG_c_29_50 (by norm_num)

lemma v_3_5 :
    (Work.LinnikAreas.A7.Phi ((3:ℝ)/(5)) ≤ ((9638293:ℝ)/(100000000))) ∧
    (((9638289:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((3:ℝ)/(5))) ∧
    (Work.LinnikAreas.A7.Wf ((3:ℝ)/(5)) ≤ ((12450827:ℝ)/(50000000))) ∧
    (((24901651:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((3:ℝ)/(5))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5)) ≤ ((9115823:ℝ)/(5000000))) ∧
    (((182316441:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((3:ℝ)/(5))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((8375279:ℝ)/(10000000))) := by
  have hq : (0:ℝ) < ((3:ℝ)/(5)) := by norm_num
  have hqle : (0:ℝ) ≤ ((3:ℝ)/(5)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((5286573:ℝ)/(100000000))) (B := ((9115823:ℝ)/(5000000))) hq exF_a_3_5 (Bfun_le (r := ((9115823:ℝ)/(5000000))) hq exG_b_3_5 exF_b_3_5 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1321643:ℝ)/(25000000))) (B := ((182316441:ℝ)/(100000000))) hq exG_a_3_5 (Bfun_ge (r := ((182316441:ℝ)/(100000000))) hq exG_b_3_5 exF_b_3_5 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5805907:ℝ)/(25000000))) (Qu := ((22021583:ℝ)/(50000000))) (r := ((12450827:ℝ)/(50000000))) hqle (by norm_num) exF_d_3_5 exF_e_3_5 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((23223627:ℝ)/(100000000))) (Ql := ((8808633:ℝ)/(20000000))) (r := ((24901651:ℝ)/(100000000))) hq exG_d_3_5 exG_e_3_5 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((9115823:ℝ)/(5000000))) hq exG_b_3_5 exF_b_3_5 (by norm_num)
  · exact Bfun_ge (r := ((182316441:ℝ)/(100000000))) hq exG_b_3_5 exF_b_3_5 (by norm_num)
  · exact F2K2_le (al := ((83527021:ℝ)/(100000000))) (r := ((8375279:ℝ)/(10000000))) hq exG_c_3_5 (by norm_num)

lemma v_139_200 :
    (Work.LinnikAreas.A7.Phi ((139:ℝ)/(200)) ≤ ((5917527:ℝ)/(100000000))) ∧
    (((1479381:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Phi ((139:ℝ)/(200))) ∧
    (Work.LinnikAreas.A7.Wf ((139:ℝ)/(200)) ≤ ((1044461:ℝ)/(5000000))) ∧
    (((20889217:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((139:ℝ)/(200))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((139:ℝ)/(200)) ≤ ((8914561:ℝ)/(5000000))) ∧
    (((35658241:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((139:ℝ)/(200))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((139:ℝ)/(200)))))/((139:ℝ)/(200)))^2/((9:ℝ)/100) ≤ ((651797:ℝ)/(800000))) := by
  have hq : (0:ℝ) < ((139:ℝ)/(200)) := by norm_num
  have hqle : (0:ℝ) ≤ ((139:ℝ)/(200)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((3319023:ℝ)/(100000000))) (B := ((8914561:ℝ)/(5000000))) hq exF_a_139_200 (Bfun_le (r := ((8914561:ℝ)/(5000000))) hq exG_b_139_200 exF_b_139_200 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1659511:ℝ)/(50000000))) (B := ((35658241:ℝ)/(20000000))) hq exG_a_139_200 (Bfun_ge (r := ((35658241:ℝ)/(20000000))) hq exG_b_139_200 exF_b_139_200 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((9215219:ℝ)/(50000000))) (Qu := ((38680549:ℝ)/(100000000))) (r := ((1044461:ℝ)/(5000000))) hqle (by norm_num) exF_d_139_200 exF_e_139_200 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((18430437:ℝ)/(100000000))) (Ql := ((9670137:ℝ)/(25000000))) (r := ((20889217:ℝ)/(100000000))) hq exG_d_139_200 exG_e_139_200 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((8914561:ℝ)/(5000000))) hq exG_b_139_200 exF_b_139_200 (by norm_num)
  · exact Bfun_ge (r := ((35658241:ℝ)/(20000000))) hq exG_b_139_200 exF_b_139_200 (by norm_num)
  · exact F2K2_le (al := ((81180103:ℝ)/(100000000))) (r := ((651797:ℝ)/(800000))) hq exG_c_139_200 (by norm_num)

lemma v_701_1000 :
    (Work.LinnikAreas.A7.Phi ((701:ℝ)/(1000)) ≤ ((2869017:ℝ)/(50000000))) ∧
    (((5738031:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((701:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((701:ℝ)/(1000)) ≤ ((20657761:ℝ)/(100000000))) ∧
    (((10328879:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((701:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((701:ℝ)/(1000)) ≤ ((89020717:ℝ)/(50000000))) ∧
    (((178041419:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((701:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((701:ℝ)/(1000)))))/((701:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((8133321:ℝ)/(10000000))) := by
  have hq : (0:ℝ) < ((701:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((701:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((201429:ℝ)/(6250000))) (B := ((89020717:ℝ)/(50000000))) hq exF_a_701_1000 (Bfun_le (r := ((89020717:ℝ)/(50000000))) hq exG_b_701_1000 exF_b_701_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((3222863:ℝ)/(100000000))) (B := ((178041419:ℝ)/(100000000))) hq exG_a_701_1000 (Bfun_ge (r := ((178041419:ℝ)/(100000000))) hq exG_b_701_1000 exF_b_701_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((18163309:ℝ)/(100000000))) (Qu := ((7672933:ℝ)/(20000000))) (r := ((20657761:ℝ)/(100000000))) hqle (by norm_num) exF_d_701_1000 exF_e_701_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4540827:ℝ)/(25000000))) (Ql := ((4795583:ℝ)/(12500000))) (r := ((10328879:ℝ)/(50000000))) hq exG_d_701_1000 exG_e_701_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((89020717:ℝ)/(50000000))) hq exG_b_701_1000 exF_b_701_1000 (by norm_num)
  · exact Bfun_ge (r := ((178041419:ℝ)/(100000000))) hq exG_b_701_1000 exF_b_701_1000 (by norm_num)
  · exact F2K2_le (al := ((8103411:ℝ)/(10000000))) (r := ((8133321:ℝ)/(10000000))) hq exG_c_701_1000 (by norm_num)

lemma v_187_250 :
    (Work.LinnikAreas.A7.Phi ((187:ℝ)/(250)) ≤ ((4508063:ℝ)/(100000000))) ∧
    (((225403:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Phi ((187:ℝ)/(250))) ∧
    (Work.LinnikAreas.A7.Wf ((187:ℝ)/(250)) ≤ ((3785537:ℝ)/(20000000))) ∧
    (((18927683:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((187:ℝ)/(250))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((187:ℝ)/(250)) ≤ ((176102663:ℝ)/(100000000))) ∧
    (((176102649:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((187:ℝ)/(250))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((187:ℝ)/(250)))))/((187:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((40117697:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((187:ℝ)/(250)) := by norm_num
  have hqle : (0:ℝ) ≤ ((187:ℝ)/(250)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1279953:ℝ)/(50000000))) (B := ((176102663:ℝ)/(100000000))) hq exF_a_187_250 (Bfun_le (r := ((176102663:ℝ)/(100000000))) hq exG_b_187_250 exF_b_187_250 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((511981:ℝ)/(20000000))) (B := ((176102649:ℝ)/(100000000))) hq exG_a_187_250 (Bfun_ge (r := ((176102649:ℝ)/(100000000))) hq exG_b_187_250 exF_b_187_250 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((3240083:ℝ)/(20000000))) (Qu := ((8994463:ℝ)/(25000000))) (r := ((3785537:ℝ)/(20000000))) hqle (by norm_num) exF_d_187_250 exF_e_187_250 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((8100207:ℝ)/(50000000))) (Ql := ((35977851:ℝ)/(100000000))) (r := ((18927683:ℝ)/(100000000))) hq exG_d_187_250 exG_e_187_250 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((176102663:ℝ)/(100000000))) hq exG_b_187_250 exF_b_187_250 (by norm_num)
  · exact Bfun_ge (r := ((176102649:ℝ)/(100000000))) hq exG_b_187_250 exF_b_187_250 (by norm_num)
  · exact F2K2_le (al := ((79899547:ℝ)/(100000000))) (r := ((40117697:ℝ)/(50000000))) hq exG_c_187_250 (by norm_num)

lemma v_379_500 :
    (Work.LinnikAreas.A7.Phi ((379:ℝ)/(500)) ≤ ((535317:ℝ)/(12500000))) ∧
    (((4282533:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((379:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((379:ℝ)/(500)) ≤ ((9288961:ℝ)/(50000000))) ∧
    (((18577919:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((379:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((379:ℝ)/(500)) ≤ ((175694217:ℝ)/(100000000))) ∧
    (((43923551:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((379:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((379:ℝ)/(500)))))/((379:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((80004081:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((379:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((379:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1218747:ℝ)/(50000000))) (B := ((175694217:ℝ)/(100000000))) hq exF_a_379_500 (Bfun_le (r := ((175694217:ℝ)/(100000000))) hq exG_b_379_500 exF_b_379_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((2437493:ℝ)/(100000000))) (B := ((43923551:ℝ)/(25000000))) hq exG_a_379_500 (Bfun_ge (r := ((43923551:ℝ)/(25000000))) hq exG_b_379_500 exF_b_379_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((15810963:ℝ)/(100000000))) (Qu := ((70979:ℝ)/(200000))) (r := ((9288961:ℝ)/(50000000))) hqle (by norm_num) exF_d_379_500 exF_e_379_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((7905481:ℝ)/(50000000))) (Ql := ((35489499:ℝ)/(100000000))) (r := ((18577919:ℝ)/(100000000))) hq exG_d_379_500 exG_e_379_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((175694217:ℝ)/(100000000))) hq exG_b_379_500 exF_b_379_500 (by norm_num)
  · exact Bfun_ge (r := ((43923551:ℝ)/(25000000))) hq exG_b_379_500 exF_b_379_500 (by norm_num)
  · exact F2K2_le (al := ((79660207:ℝ)/(100000000))) (r := ((80004081:ℝ)/(100000000))) hq exG_c_379_500 (by norm_num)

lemma v_96_125 :
    (Work.LinnikAreas.A7.Phi ((96:ℝ)/(125)) ≤ ((254269:ℝ)/(6250000))) ∧
    (((4068301:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((96:ℝ)/(125))) ∧
    (Work.LinnikAreas.A7.Wf ((96:ℝ)/(125)) ≤ ((1139647:ℝ)/(6250000))) ∧
    (((18234349:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((96:ℝ)/(125))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((96:ℝ)/(125)) ≤ ((175287179:ℝ)/(100000000))) ∧
    (((87643583:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((96:ℝ)/(125))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((96:ℝ)/(125)))))/((96:ℝ)/(125)))^2/((9:ℝ)/100) ≤ ((39886773:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((96:ℝ)/(125)) := by norm_num
  have hqle : (0:ℝ) ≤ ((96:ℝ)/(125)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((290117:ℝ)/(12500000))) (B := ((175287179:ℝ)/(100000000))) hq exF_a_96_125 (Bfun_le (r := ((175287179:ℝ)/(100000000))) hq exG_b_96_125 exF_b_96_125 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((464187:ℝ)/(20000000))) (B := ((87643583:ℝ)/(50000000))) hq exG_a_96_125 (Bfun_ge (r := ((87643583:ℝ)/(50000000))) hq exG_b_96_125 exF_b_96_125 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((15430873:ℝ)/(100000000))) (Qu := ((1093993:ℝ)/(3125000))) (r := ((1139647:ℝ)/(6250000))) hqle (by norm_num) exF_d_96_125 exF_e_96_125 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1928859:ℝ)/(12500000))) (Ql := ((1400311:ℝ)/(4000000))) (r := ((18234349:ℝ)/(100000000))) hq exG_d_96_125 exG_e_96_125 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((175287179:ℝ)/(100000000))) hq exG_b_96_125 exF_b_96_125 (by norm_num)
  · exact Bfun_ge (r := ((87643583:ℝ)/(50000000))) hq exG_b_96_125 exF_b_96_125 (by norm_num)
  · exact F2K2_le (al := ((15884317:ℝ)/(20000000))) (r := ((39886773:ℝ)/(50000000))) hq exG_c_96_125 (by norm_num)

lemma v_779_1000 :
    (Work.LinnikAreas.A7.Phi ((779:ℝ)/(1000)) ≤ ((480627:ℝ)/(12500000))) ∧
    (((3845013:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((779:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((779:ℝ)/(1000)) ≤ ((17863453:ℝ)/(100000000))) ∧
    (((17863451:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((779:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((779:ℝ)/(1000)) ≤ ((174841053:ℝ)/(100000000))) ∧
    (((2185513:ℝ)/(1250000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((779:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((779:ℝ)/(1000)))))/((779:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((2485027:ℝ)/(3125000))) := by
  have hq : (0:ℝ) < ((779:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((779:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((2199149:ℝ)/(100000000))) (B := ((174841053:ℝ)/(100000000))) hq exF_a_779_1000 (Bfun_le (r := ((174841053:ℝ)/(100000000))) hq exG_b_779_1000 exF_b_779_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((549787:ℝ)/(25000000))) (B := ((2185513:ℝ)/(1250000))) hq exG_a_779_1000 (Bfun_ge (r := ((2185513:ℝ)/(1250000))) hq exG_b_779_1000 exF_b_779_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((7511659:ℝ)/(50000000))) (Qu := ((8621357:ℝ)/(25000000))) (r := ((17863453:ℝ)/(100000000))) hqle (by norm_num) exF_d_779_1000 exF_e_779_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((15023317:ℝ)/(100000000))) (Ql := ((34485427:ℝ)/(100000000))) (r := ((17863451:ℝ)/(100000000))) hq exG_d_779_1000 exG_e_779_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((174841053:ℝ)/(100000000))) hq exG_b_779_1000 exF_b_779_1000 (by norm_num)
  · exact Bfun_ge (r := ((2185513:ℝ)/(1250000))) hq exG_b_779_1000 exF_b_779_1000 (by norm_num)
  · exact F2K2_le (al := ((39579963:ℝ)/(50000000))) (r := ((2485027:ℝ)/(3125000))) hq exG_c_779_1000 (by norm_num)

lemma v_79_100 :
    (Work.LinnikAreas.A7.Phi ((79:ℝ)/(100)) ≤ ((726799:ℝ)/(20000000))) ∧
    (((454249:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Phi ((79:ℝ)/(100))) ∧
    (Work.LinnikAreas.A7.Wf ((79:ℝ)/(100)) ≤ ((17499789:ℝ)/(100000000))) ∧
    (((8749893:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((79:ℝ)/(100))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((79:ℝ)/(100)) ≤ ((174396629:ℝ)/(100000000))) ∧
    (((21799577:ℝ)/(12500000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((79:ℝ)/(100))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((79:ℝ)/(100)))))/((79:ℝ)/(100)))^2/((9:ℝ)/100) ≤ ((15853827:ℝ)/(20000000))) := by
  have hq : (0:ℝ) < ((79:ℝ)/(100)) := by norm_num
  have hqle : (0:ℝ) ≤ ((79:ℝ)/(100)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((2083753:ℝ)/(100000000))) (B := ((174396629:ℝ)/(100000000))) hq exF_a_79_100 (Bfun_le (r := ((174396629:ℝ)/(100000000))) hq exG_b_79_100 exF_b_79_100 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((260469:ℝ)/(12500000))) (B := ((21799577:ℝ)/(12500000))) hq exG_a_79_100 (Bfun_ge (r := ((21799577:ℝ)/(12500000))) hq exG_b_79_100 exF_b_79_100 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((457079:ℝ)/(3125000))) (Qu := ((271767:ℝ)/(800000))) (r := ((17499789:ℝ)/(100000000))) hqle (by norm_num) exF_d_79_100 exF_e_79_100 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((14626527:ℝ)/(100000000))) (Ql := ((16985437:ℝ)/(50000000))) (r := ((8749893:ℝ)/(50000000))) hq exG_d_79_100 exG_e_79_100 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((174396629:ℝ)/(100000000))) hq exG_b_79_100 exF_b_79_100 (by norm_num)
  · exact Bfun_ge (r := ((21799577:ℝ)/(12500000))) hq exG_b_79_100 exF_b_79_100 (by norm_num)
  · exact F2K2_le (al := ((9862391:ℝ)/(12500000))) (r := ((15853827:ℝ)/(20000000))) hq exG_c_79_100 (by norm_num)

lemma v_401_500 :
    (Work.LinnikAreas.A7.Phi ((401:ℝ)/(500)) ≤ ((3416989:ℝ)/(100000000))) ∧
    (((1708493:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((401:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((401:ℝ)/(500)) ≤ ((3422231:ℝ)/(20000000))) ∧
    (((17111153:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((401:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((401:ℝ)/(500)) ≤ ((43478429:ℝ)/(25000000))) ∧
    (((21739213:ℝ)/(12500000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((401:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((401:ℝ)/(500)))))/((401:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((617153:ℝ)/(781250))) := by
  have hq : (0:ℝ) < ((401:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((401:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1964761:ℝ)/(100000000))) (B := ((43478429:ℝ)/(25000000))) hq exF_a_401_500 (Bfun_le (r := ((43478429:ℝ)/(25000000))) hq exG_b_401_500 exF_b_401_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((49119:ℝ)/(2500000))) (B := ((21739213:ℝ)/(12500000))) hq exG_a_401_500 (Bfun_ge (r := ((21739213:ℝ)/(12500000))) hq exG_b_401_500 exF_b_401_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((14205609:ℝ)/(100000000))) (Qu := ((4177287:ℝ)/(12500000))) (r := ((3422231:ℝ)/(20000000))) hqle (by norm_num) exF_d_401_500 exF_e_401_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1775701:ℝ)/(12500000))) (Ql := ((6683659:ℝ)/(20000000))) (r := ((17111153:ℝ)/(100000000))) hq exG_d_401_500 exG_e_401_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((43478429:ℝ)/(25000000))) hq exG_b_401_500 exF_b_401_500 (by norm_num)
  · exact Bfun_ge (r := ((21739213:ℝ)/(12500000))) hq exG_b_401_500 exF_b_401_500 (by norm_num)
  · exact F2K2_le (al := ((39307801:ℝ)/(50000000))) (r := ((617153:ℝ)/(781250))) hq exG_c_401_500 (by norm_num)

lemma v_163_200 :
    (Work.LinnikAreas.A7.Phi ((163:ℝ)/(200)) ≤ ((3196511:ℝ)/(100000000))) ∧
    (((799127:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Phi ((163:ℝ)/(200))) ∧
    (Work.LinnikAreas.A7.Wf ((163:ℝ)/(200)) ≤ ((1669947:ℝ)/(10000000))) ∧
    (((16699467:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((163:ℝ)/(200))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((163:ℝ)/(200)) ≤ ((86696407:ℝ)/(50000000))) ∧
    (((86696401:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((163:ℝ)/(200))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((163:ℝ)/(200)))))/((163:ℝ)/(200)))^2/((9:ℝ)/100) ≤ ((39350249:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((163:ℝ)/(200)) := by norm_num
  have hqle : (0:ℝ) ≤ ((163:ℝ)/(200)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((460877:ℝ)/(25000000))) (B := ((86696407:ℝ)/(50000000))) hq exF_a_163_200 (Bfun_le (r := ((86696407:ℝ)/(50000000))) hq exG_b_163_200 exF_b_163_200 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1843507:ℝ)/(100000000))) (B := ((86696401:ℝ)/(50000000))) hq exG_a_163_200 (Bfun_ge (r := ((86696401:ℝ)/(50000000))) hq exG_b_163_200 exF_b_163_200 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((13763271:ℝ)/(100000000))) (Qu := ((32829807:ℝ)/(100000000))) (r := ((1669947:ℝ)/(10000000))) hqle (by norm_num) exF_d_163_200 exF_e_163_200 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1376327:ℝ)/(10000000))) (Ql := ((16414903:ℝ)/(50000000))) (r := ((16699467:ℝ)/(100000000))) hq exG_d_163_200 exG_e_163_200 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((86696407:ℝ)/(50000000))) hq exG_b_163_200 exF_b_163_200 (by norm_num)
  · exact Bfun_ge (r := ((86696401:ℝ)/(50000000))) hq exG_b_163_200 exF_b_163_200 (by norm_num)
  · exact F2K2_le (al := ((39154799:ℝ)/(50000000))) (r := ((39350249:ℝ)/(50000000))) hq exG_c_163_200 (by norm_num)

lemma v_207_250 :
    (Work.LinnikAreas.A7.Phi ((207:ℝ)/(250)) ≤ ((1495137:ℝ)/(50000000))) ∧
    (((2990271:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((207:ℝ)/(250))) ∧
    (Work.LinnikAreas.A7.Wf ((207:ℝ)/(250)) ≤ ((2037161:ℝ)/(12500000))) ∧
    (((8148643:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((207:ℝ)/(250))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((207:ℝ)/(250)) ≤ ((172874241:ℝ)/(100000000))) ∧
    (((17287423:ℝ)/(10000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((207:ℝ)/(250))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((207:ℝ)/(250)))))/((207:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((15681341:ℝ)/(20000000))) := by
  have hq : (0:ℝ) < ((207:ℝ)/(250)) := by norm_num
  have hqle : (0:ℝ) ≤ ((207:ℝ)/(250)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1729739:ℝ)/(100000000))) (B := ((172874241:ℝ)/(100000000))) hq exF_a_207_250 (Bfun_le (r := ((172874241:ℝ)/(100000000))) hq exG_b_207_250 exF_b_207_250 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((864869:ℝ)/(50000000))) (B := ((17287423:ℝ)/(10000000))) hq exG_a_207_250 (Bfun_ge (r := ((17287423:ℝ)/(10000000))) hq exG_b_207_250 exF_b_207_250 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((3333677:ℝ)/(25000000))) (Qu := ((16125841:ℝ)/(50000000))) (r := ((2037161:ℝ)/(12500000))) hqle (by norm_num) exF_d_207_250 exF_e_207_250 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((13334707:ℝ)/(100000000))) (Ql := ((32251681:ℝ)/(100000000))) (r := ((8148643:ℝ)/(50000000))) hq exG_d_207_250 exG_e_207_250 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((172874241:ℝ)/(100000000))) hq exG_b_207_250 exF_b_207_250 (by norm_num)
  · exact Bfun_ge (r := ((17287423:ℝ)/(10000000))) hq exG_b_207_250 exF_b_207_250 (by norm_num)
  · exact F2K2_le (al := ((39002393:ℝ)/(50000000))) (r := ((15681341:ℝ)/(20000000))) hq exG_c_207_250 (by norm_num)

lemma v_841_1000 :
    (Work.LinnikAreas.A7.Phi ((841:ℝ)/(1000)) ≤ ((559471:ℝ)/(20000000))) ∧
    (((349669:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Phi ((841:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((841:ℝ)/(1000)) ≤ ((15904397:ℝ)/(100000000))) ∧
    (((3180879:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((841:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((841:ℝ)/(1000)) ≤ ((5386187:ℝ)/(3125000))) ∧
    (((172357973:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((841:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((841:ℝ)/(1000)))))/((841:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((78114217:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((841:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((841:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1622991:ℝ)/(100000000))) (B := ((5386187:ℝ)/(3125000))) hq exF_a_841_1000 (Bfun_le (r := ((5386187:ℝ)/(3125000))) hq exG_b_841_1000 exF_b_841_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((162299:ℝ)/(10000000))) (B := ((172357973:ℝ)/(100000000))) hq exG_a_841_1000 (Bfun_ge (r := ((172357973:ℝ)/(100000000))) hq exG_b_841_1000 exF_b_841_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((201867:ℝ)/(1562500))) (Qu := ((31683737:ℝ)/(100000000))) (r := ((15904397:ℝ)/(100000000))) hqle (by norm_num) exF_d_841_1000 exF_e_841_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((12919487:ℝ)/(100000000))) (Ql := ((3960467:ℝ)/(12500000))) (r := ((3180879:ℝ)/(20000000))) hq exG_d_841_1000 exG_e_841_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((5386187:ℝ)/(3125000))) hq exG_b_841_1000 exF_b_841_1000 (by norm_num)
  · exact Bfun_ge (r := ((172357973:ℝ)/(100000000))) hq exG_b_841_1000 exF_b_841_1000 (by norm_num)
  · exact F2K2_le (al := ((77701159:ℝ)/(100000000))) (r := ((78114217:ℝ)/(100000000))) hq exG_c_841_1000 (by norm_num)

lemma v_211_250 :
    (Work.LinnikAreas.A7.Phi ((211:ℝ)/(250)) ≤ ((1377317:ℝ)/(50000000))) ∧
    (((2754631:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((211:ℝ)/(250))) ∧
    (Work.LinnikAreas.A7.Wf ((211:ℝ)/(250)) ≤ ((3953757:ℝ)/(25000000))) ∧
    (((7907513:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((211:ℝ)/(250))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((211:ℝ)/(250)) ≤ ((86119587:ℝ)/(50000000))) ∧
    (((172239163:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((211:ℝ)/(250))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((211:ℝ)/(250)))))/((211:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((78046897:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((211:ℝ)/(250)) := by norm_num
  have hqle : (0:ℝ) ≤ ((211:ℝ)/(250)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1599307:ℝ)/(100000000))) (B := ((86119587:ℝ)/(50000000))) hq exF_a_211_250 (Bfun_le (r := ((86119587:ℝ)/(50000000))) hq exG_b_211_250 exF_b_211_250 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((799653:ℝ)/(50000000))) (B := ((172239163:ℝ)/(100000000))) hq exG_a_211_250 (Bfun_ge (r := ((172239163:ℝ)/(100000000))) hq exG_b_211_250 exF_b_211_250 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12825519:ℝ)/(100000000))) (Qu := ((315541:ℝ)/(1000000))) (r := ((3953757:ℝ)/(25000000))) hqle (by norm_num) exF_d_211_250 exF_e_211_250 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6412759:ℝ)/(50000000))) (Ql := ((31554099:ℝ)/(100000000))) (r := ((7907513:ℝ)/(50000000))) hq exG_d_211_250 exG_e_211_250 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((86119587:ℝ)/(50000000))) hq exG_b_211_250 exF_b_211_250 (by norm_num)
  · exact Bfun_ge (r := ((172239163:ℝ)/(100000000))) hq exG_b_211_250 exF_b_211_250 (by norm_num)
  · exact F2K2_le (al := ((3881563:ℝ)/(5000000))) (r := ((78046897:ℝ)/(100000000))) hq exG_c_211_250 (by norm_num)

lemma v_171_200 :
    (Work.LinnikAreas.A7.Phi ((171:ℝ)/(200)) ≤ ((2603503:ℝ)/(100000000))) ∧
    (((5207:ℝ)/(200000)) ≤ Work.LinnikAreas.A7.Phi ((171:ℝ)/(200))) ∧
    (Work.LinnikAreas.A7.Wf ((171:ℝ)/(200)) ≤ ((3098289:ℝ)/(20000000))) ∧
    (((7745721:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((171:ℝ)/(200))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((171:ℝ)/(200)) ≤ ((85902297:ℝ)/(50000000))) ∧
    (((171804583:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((171:ℝ)/(200))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((171:ℝ)/(200)))))/((171:ℝ)/(200)))^2/((9:ℝ)/100) ≤ ((3890033:ℝ)/(5000000))) := by
  have hq : (0:ℝ) < ((171:ℝ)/(200)) := by norm_num
  have hqle : (0:ℝ) ≤ ((171:ℝ)/(200)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((757693:ℝ)/(50000000))) (B := ((85902297:ℝ)/(50000000))) hq exF_a_171_200 (Bfun_le (r := ((85902297:ℝ)/(50000000))) hq exG_b_171_200 exF_b_171_200 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((303077:ℝ)/(20000000))) (B := ((171804583:ℝ)/(100000000))) hq exG_a_171_200 (Bfun_ge (r := ((171804583:ℝ)/(100000000))) hq exG_b_171_200 exF_b_171_200 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12486777:ℝ)/(100000000))) (Qu := ((6216657:ℝ)/(20000000))) (r := ((3098289:ℝ)/(20000000))) hqle (by norm_num) exF_d_171_200 exF_e_171_200 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1560847:ℝ)/(12500000))) (Ql := ((7770821:ℝ)/(25000000))) (r := ((7745721:ℝ)/(50000000))) hq exG_d_171_200 exG_e_171_200 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((85902297:ℝ)/(50000000))) hq exG_b_171_200 exF_b_171_200 (by norm_num)
  · exact Bfun_ge (r := ((171804583:ℝ)/(100000000))) hq exG_b_171_200 exF_b_171_200 (by norm_num)
  · exact F2K2_le (al := ((77375499:ℝ)/(100000000))) (r := ((3890033:ℝ)/(5000000))) hq exG_c_171_200 (by norm_num)

lemma v_107_125 :
    (Work.LinnikAreas.A7.Phi ((107:ℝ)/(125)) ≤ ((2590183:ℝ)/(100000000))) ∧
    (((129509:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Phi ((107:ℝ)/(125))) ∧
    (Work.LinnikAreas.A7.Wf ((107:ℝ)/(125)) ≤ ((1932793:ℝ)/(12500000))) ∧
    (((15462341:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((107:ℝ)/(125))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((107:ℝ)/(125)) ≤ ((10735323:ℝ)/(6250000))) ∧
    (((171765157:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((107:ℝ)/(125))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((107:ℝ)/(125)))))/((107:ℝ)/(125)))^2/((9:ℝ)/100) ≤ ((77778319:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((107:ℝ)/(125)) := by norm_num
  have hqle : (0:ℝ) ≤ ((107:ℝ)/(125)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1507979:ℝ)/(100000000))) (B := ((10735323:ℝ)/(6250000))) hq exF_a_107_125 (Bfun_le (r := ((10735323:ℝ)/(6250000))) hq exG_b_107_125 exF_b_107_125 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((753989:ℝ)/(50000000))) (B := ((171765157:ℝ)/(100000000))) hq exG_a_107_125 (Bfun_ge (r := ((171765157:ℝ)/(100000000))) hq exG_b_107_125 exF_b_107_125 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12456429:ℝ)/(100000000))) (Qu := ((31040833:ℝ)/(100000000))) (r := ((1932793:ℝ)/(12500000))) hqle (by norm_num) exF_d_107_125 exF_e_107_125 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((3114107:ℝ)/(25000000))) (Ql := ((485013:ℝ)/(1562500))) (r := ((15462341:ℝ)/(100000000))) hq exG_d_107_125 exG_e_107_125 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((10735323:ℝ)/(6250000))) hq exG_b_107_125 exF_b_107_125 (by norm_num)
  · exact Bfun_ge (r := ((171765157:ℝ)/(100000000))) hq exG_b_107_125 exF_b_107_125 (by norm_num)
  · exact F2K2_le (al := ((7735229:ℝ)/(10000000))) (r := ((77778319:ℝ)/(100000000))) hq exG_c_107_125 (by norm_num)

lemma v_173_200 :
    (Work.LinnikAreas.A7.Phi ((173:ℝ)/(200)) ≤ ((2473327:ℝ)/(100000000))) ∧
    (((618331:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Phi ((173:ℝ)/(200))) ∧
    (Work.LinnikAreas.A7.Wf ((173:ℝ)/(200)) ≤ ((15202793:ℝ)/(100000000))) ∧
    (((1520279:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Wf ((173:ℝ)/(200))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((173:ℝ)/(200)) ≤ ((85705469:ℝ)/(50000000))) ∧
    (((10713183:ℝ)/(6250000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((173:ℝ)/(200))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((173:ℝ)/(200)))))/((173:ℝ)/(200)))^2/((9:ℝ)/100) ≤ ((38788803:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((173:ℝ)/(200)) := by norm_num
  have hqle : (0:ℝ) ≤ ((173:ℝ)/(200)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((721461:ℝ)/(50000000))) (B := ((85705469:ℝ)/(50000000))) hq exF_a_173_200 (Bfun_le (r := ((85705469:ℝ)/(50000000))) hq exG_b_173_200 exF_b_173_200 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1442921:ℝ)/(100000000))) (B := ((10713183:ℝ)/(6250000))) hq exG_a_173_200 (Bfun_ge (r := ((10713183:ℝ)/(6250000))) hq exG_b_173_200 exF_b_173_200 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12186599:ℝ)/(100000000))) (Qu := ((30661369:ℝ)/(100000000))) (r := ((15202793:ℝ)/(100000000))) hqle (by norm_num) exF_d_173_200 exF_e_173_200 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6093299:ℝ)/(50000000))) (Ql := ((3832671:ℝ)/(12500000))) (r := ((1520279:ℝ)/(10000000))) hq exG_d_173_200 exG_e_173_200 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((85705469:ℝ)/(50000000))) hq exG_b_173_200 exF_b_173_200 (by norm_num)
  · exact Bfun_ge (r := ((10713183:ℝ)/(6250000))) hq exG_b_173_200 exF_b_173_200 (by norm_num)
  · exact F2K2_le (al := ((1928593:ℝ)/(2500000))) (r := ((38788803:ℝ)/(50000000))) hq exG_c_173_200 (by norm_num)

lemma v_87_100 :
    (Work.LinnikAreas.A7.Phi ((87:ℝ)/(100)) ≤ ((1205351:ℝ)/(50000000))) ∧
    (((2410699:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((87:ℝ)/(100))) ∧
    (Work.LinnikAreas.A7.Wf ((87:ℝ)/(100)) ≤ ((1882551:ℝ)/(12500000))) ∧
    (((7530203:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((87:ℝ)/(100))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(100)) ≤ ((171214619:ℝ)/(100000000))) ∧
    (((10700913:ℝ)/(6250000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((87:ℝ)/(100))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((87:ℝ)/(100)))))/((87:ℝ)/(100)))^2/((9:ℝ)/100) ≤ ((38733181:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((87:ℝ)/(100)) := by norm_num
  have hqle : (0:ℝ) ≤ ((87:ℝ)/(100)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((44:ℝ)/(3125))) (B := ((171214619:ℝ)/(100000000))) hq exF_a_87_100 (Bfun_le (r := ((171214619:ℝ)/(100000000))) hq exG_b_87_100 exF_b_87_100 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1407999:ℝ)/(100000000))) (B := ((10700913:ℝ)/(6250000))) hq exG_a_87_100 (Bfun_ge (r := ((10700913:ℝ)/(6250000))) hq exG_b_87_100 exF_b_87_100 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((12039227:ℝ)/(100000000))) (Qu := ((7613141:ℝ)/(25000000))) (r := ((1882551:ℝ)/(12500000))) hqle (by norm_num) exF_d_87_100 exF_e_87_100 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6019613:ℝ)/(50000000))) (Ql := ((30452563:ℝ)/(100000000))) (r := ((7530203:ℝ)/(50000000))) hq exG_d_87_100 exG_e_87_100 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((171214619:ℝ)/(100000000))) hq exG_b_87_100 exF_b_87_100 (by norm_num)
  · exact Bfun_ge (r := ((10700913:ℝ)/(6250000))) hq exG_b_87_100 exF_b_87_100 (by norm_num)
  · exact F2K2_le (al := ((77028091:ℝ)/(100000000))) (r := ((38733181:ℝ)/(50000000))) hq exG_c_87_100 (by norm_num)

lemma v_437_500 :
    (Work.LinnikAreas.A7.Phi ((437:ℝ)/(500)) ≤ ((590437:ℝ)/(25000000))) ∧
    (((472349:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((437:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((437:ℝ)/(500)) ≤ ((14947423:ℝ)/(100000000))) ∧
    (((747371:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((437:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((437:ℝ)/(500)) ≤ ((85528903:ℝ)/(50000000))) ∧
    (((34211559:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((437:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((437:ℝ)/(500)))))/((437:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((30951:ℝ)/(40000))) := by
  have hq : (0:ℝ) < ((437:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((437:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((21573:ℝ)/(1562500))) (B := ((85528903:ℝ)/(50000000))) hq exF_a_437_500 (Bfun_le (r := ((85528903:ℝ)/(50000000))) hq exG_b_437_500 exF_b_437_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1380671:ℝ)/(100000000))) (B := ((34211559:ℝ)/(20000000))) hq exG_a_437_500 (Bfun_ge (r := ((34211559:ℝ)/(20000000))) hq exG_b_437_500 exF_b_437_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5961307:ℝ)/(50000000))) (Qu := ((1892909:ℝ)/(6250000))) (r := ((14947423:ℝ)/(100000000))) hqle (by norm_num) exF_d_437_500 exF_e_437_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((11922613:ℝ)/(100000000))) (Ql := ((30286543:ℝ)/(100000000))) (r := ((747371:ℝ)/(5000000))) hq exG_d_437_500 exG_e_437_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((85528903:ℝ)/(50000000))) hq exG_b_437_500 exF_b_437_500 (by norm_num)
  · exact Bfun_ge (r := ((34211559:ℝ)/(20000000))) hq exG_b_437_500 exF_b_437_500 (by norm_num)
  · exact F2K2_le (al := ((76935713:ℝ)/(100000000))) (r := ((30951:ℝ)/(40000))) hq exG_c_437_500 (by norm_num)

lemma v_7_8 :
    (Work.LinnikAreas.A7.Phi ((7:ℝ)/(8)) ≤ ((2349667:ℝ)/(100000000))) ∧
    (((73427:ℝ)/(3125000)) ≤ Work.LinnikAreas.A7.Phi ((7:ℝ)/(8))) ∧
    (Work.LinnikAreas.A7.Wf ((7:ℝ)/(8)) ≤ ((14919303:ℝ)/(100000000))) ∧
    (((149193:ℝ)/(1000000)) ≤ Work.LinnikAreas.A7.Wf ((7:ℝ)/(8))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((7:ℝ)/(8)) ≤ ((42754659:ℝ)/(25000000))) ∧
    (((1368149:ℝ)/(800000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((7:ℝ)/(8))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((7:ℝ)/(8)))))/((7:ℝ)/(8)))^2/((9:ℝ)/100) ≤ ((38677651:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((7:ℝ)/(8)) := by norm_num
  have hqle : (0:ℝ) ≤ ((7:ℝ)/(8)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((343481:ℝ)/(25000000))) (B := ((42754659:ℝ)/(25000000))) hq exF_a_7_8 (Bfun_le (r := ((42754659:ℝ)/(25000000))) hq exG_b_7_8 exF_b_7_8 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1373923:ℝ)/(100000000))) (B := ((1368149:ℝ)/(800000))) hq exG_a_7_8 (Bfun_ge (r := ((1368149:ℝ)/(800000))) hq exG_b_7_8 exF_b_7_8 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((11893637:ℝ)/(100000000))) (Qu := ((30245181:ℝ)/(100000000))) (r := ((14919303:ℝ)/(100000000))) hqle (by norm_num) exF_d_7_8 exF_e_7_8 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((2973409:ℝ)/(25000000))) (Ql := ((1512259:ℝ)/(5000000))) (r := ((149193:ℝ)/(1000000))) hq exG_d_7_8 exG_e_7_8 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((42754659:ℝ)/(25000000))) hq exG_b_7_8 exF_b_7_8 (by norm_num)
  · exact Bfun_ge (r := ((1368149:ℝ)/(800000))) hq exG_b_7_8 exF_b_7_8 (by norm_num)
  · exact F2K2_le (al := ((19228159:ℝ)/(25000000))) (r := ((38677651:ℝ)/(50000000))) hq exG_c_7_8 (by norm_num)

lemma v_443_500 :
    (Work.LinnikAreas.A7.Phi ((443:ℝ)/(500)) ≤ ((2220773:ℝ)/(100000000))) ∧
    (((222077:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Phi ((443:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((443:ℝ)/(500)) ≤ ((14613321:ℝ)/(100000000))) ∧
    (((14613319:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((443:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((443:ℝ)/(500)) ≤ ((34117731:ℝ)/(20000000))) ∧
    (((42647161:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((443:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((443:ℝ)/(500)))))/((443:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((77111637:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((443:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((443:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1301829:ℝ)/(100000000))) (B := ((34117731:ℝ)/(20000000))) hq exF_a_443_500 (Bfun_le (r := ((34117731:ℝ)/(20000000))) hq exG_b_443_500 exF_b_443_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((325457:ℝ)/(25000000))) (B := ((42647161:ℝ)/(25000000))) hq exG_a_443_500 (Bfun_ge (r := ((42647161:ℝ)/(25000000))) hq exG_b_443_500 exF_b_443_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((11579507:ℝ)/(100000000))) (Qu := ((3724237:ℝ)/(12500000))) (r := ((14613321:ℝ)/(100000000))) hqle (by norm_num) exF_d_443_500 exF_e_443_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5789753:ℝ)/(50000000))) (Ql := ((5958779:ℝ)/(20000000))) (r := ((14613319:ℝ)/(100000000))) hq exG_d_443_500 exG_e_443_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((34117731:ℝ)/(20000000))) hq exG_b_443_500 exF_b_443_500 (by norm_num)
  · exact Bfun_ge (r := ((42647161:ℝ)/(25000000))) hq exG_b_443_500 exF_b_443_500 (by norm_num)
  · exact F2K2_le (al := ((76659243:ℝ)/(100000000))) (r := ((77111637:ℝ)/(100000000))) hq exG_c_443_500 (by norm_num)

lemma v_223_250 :
    (Work.LinnikAreas.A7.Phi ((223:ℝ)/(250)) ≤ ((1076739:ℝ)/(50000000))) ∧
    (((86139:ℝ)/(4000000)) ≤ Work.LinnikAreas.A7.Phi ((223:ℝ)/(250))) ∧
    (Work.LinnikAreas.A7.Wf ((223:ℝ)/(250)) ≤ ((1806121:ℝ)/(12500000))) ∧
    (((7224483:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((223:ℝ)/(250))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((223:ℝ)/(250)) ≤ ((170354801:ℝ)/(100000000))) ∧
    (((170354791:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((223:ℝ)/(250))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((223:ℝ)/(250)))))/((223:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((19244779:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((223:ℝ)/(250)) := by norm_num
  have hqle : (0:ℝ) ≤ ((223:ℝ)/(250)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((1264113:ℝ)/(100000000))) (B := ((170354801:ℝ)/(100000000))) hq exF_a_223_250 (Bfun_le (r := ((170354801:ℝ)/(100000000))) hq exG_b_223_250 exF_b_223_250 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((79007:ℝ)/(6250000))) (B := ((170354791:ℝ)/(100000000))) hq exG_a_223_250 (Bfun_ge (r := ((170354791:ℝ)/(100000000))) hq exG_b_223_250 exF_b_223_250 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5705837:ℝ)/(50000000))) (Qu := ((5910117:ℝ)/(20000000))) (r := ((1806121:ℝ)/(12500000))) hqle (by norm_num) exF_d_223_250 exF_e_223_250 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((11411673:ℝ)/(100000000))) (Ql := ((3693823:ℝ)/(12500000))) (r := ((7224483:ℝ)/(50000000))) hq exG_d_223_250 exG_e_223_250 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((170354801:ℝ)/(100000000))) hq exG_b_223_250 exF_b_223_250 (by norm_num)
  · exact Bfun_ge (r := ((170354791:ℝ)/(100000000))) hq exG_b_223_250 exF_b_223_250 (by norm_num)
  · exact F2K2_le (al := ((3826069:ℝ)/(5000000))) (r := ((19244779:ℝ)/(25000000))) hq exG_c_223_250 (by norm_num)

lemma v_9_10 :
    (Work.LinnikAreas.A7.Phi ((9:ℝ)/(10)) ≤ ((2066913:ℝ)/(100000000))) ∧
    (((206691:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Phi ((9:ℝ)/(10))) ∧
    (Work.LinnikAreas.A7.Wf ((9:ℝ)/(10)) ≤ ((3558147:ℝ)/(25000000))) ∧
    (((2846517:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((9:ℝ)/(10))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(10)) ≤ ((170043749:ℝ)/(100000000))) ∧
    (((170043739:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(10))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(10)))))/((9:ℝ)/(10)))^2/((9:ℝ)/100) ≤ ((38401417:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((9:ℝ)/(10)) := by norm_num
  have hqle : (0:ℝ) ≤ ((9:ℝ)/(10)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((607759:ℝ)/(50000000))) (B := ((170043749:ℝ)/(100000000))) hq exF_a_9_10 (Bfun_le (r := ((170043749:ℝ)/(100000000))) hq exG_b_9_10 exF_b_9_10 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1215517:ℝ)/(100000000))) (B := ((170043739:ℝ)/(100000000))) hq exG_a_9_10 (Bfun_ge (r := ((170043739:ℝ)/(100000000))) hq exG_b_9_10 exF_b_9_10 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((447667:ℝ)/(4000000))) (Qu := ((14614629:ℝ)/(50000000))) (r := ((3558147:ℝ)/(25000000))) hqle (by norm_num) exF_d_9_10 exF_e_9_10 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5595837:ℝ)/(50000000))) (Ql := ((29229257:ℝ)/(100000000))) (r := ((2846517:ℝ)/(20000000))) hq exG_d_9_10 exG_e_9_10 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((170043749:ℝ)/(100000000))) hq exG_b_9_10 exF_b_9_10 (by norm_num)
  · exact Bfun_ge (r := ((170043739:ℝ)/(100000000))) hq exG_b_9_10 exF_b_9_10 (by norm_num)
  · exact F2K2_le (al := ((76337949:ℝ)/(100000000))) (r := ((38401417:ℝ)/(50000000))) hq exG_c_9_10 (by norm_num)

lemma v_451_500 :
    (Work.LinnikAreas.A7.Phi ((451:ℝ)/(500)) ≤ ((2045821:ℝ)/(100000000))) ∧
    (((2045819:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((451:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((451:ℝ)/(500)) ≤ ((14178981:ℝ)/(100000000))) ∧
    (((14178979:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((451:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((451:ℝ)/(500)) ≤ ((169966117:ℝ)/(100000000))) ∧
    (((42491527:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((451:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((451:ℝ)/(500)))))/((451:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((38379419:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((451:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((451:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((75229:ℝ)/(6250000))) (B := ((169966117:ℝ)/(100000000))) hq exF_a_451_500 (Bfun_le (r := ((169966117:ℝ)/(100000000))) hq exG_b_451_500 exF_b_451_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1203663:ℝ)/(100000000))) (B := ((42491527:ℝ)/(25000000))) hq exG_a_451_500 (Bfun_ge (r := ((42491527:ℝ)/(25000000))) hq exG_b_451_500 exF_b_451_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5568671:ℝ)/(50000000))) (Qu := ((14574737:ℝ)/(50000000))) (r := ((14178981:ℝ)/(100000000))) hqle (by norm_num) exF_d_451_500 exF_e_451_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((11137341:ℝ)/(100000000))) (Ql := ((29149473:ℝ)/(100000000))) (r := ((14178979:ℝ)/(100000000))) hq exG_d_451_500 exG_e_451_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((169966117:ℝ)/(100000000))) hq exG_b_451_500 exF_b_451_500 (by norm_num)
  · exact Bfun_ge (r := ((42491527:ℝ)/(25000000))) hq exG_b_451_500 exF_b_451_500 (by norm_num)
  · exact F2K2_le (al := ((238413:ℝ)/(312500))) (r := ((38379419:ℝ)/(50000000))) hq exG_c_451_500 (by norm_num)

lemma v_453_500 :
    (Work.LinnikAreas.A7.Phi ((453:ℝ)/(500)) ≤ ((2004283:ℝ)/(100000000))) ∧
    (((2004281:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((453:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((453:ℝ)/(500)) ≤ ((14072347:ℝ)/(100000000))) ∧
    (((1759043:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((453:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((453:ℝ)/(500)) ≤ ((84905509:ℝ)/(50000000))) ∧
    (((2653297:ℝ)/(1562500)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((453:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((453:ℝ)/(500)))))/((453:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((38335469:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((453:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((453:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((590151:ℝ)/(50000000))) (B := ((84905509:ℝ)/(50000000))) hq exF_a_453_500 (Bfun_le (r := ((84905509:ℝ)/(50000000))) hq exG_b_453_500 exF_b_453_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1180301:ℝ)/(100000000))) (B := ((2653297:ℝ)/(1562500))) hq exG_a_453_500 (Bfun_ge (r := ((2653297:ℝ)/(1562500))) hq exG_b_453_500 exF_b_453_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1378683:ℝ)/(12500000))) (Qu := ((14495279:ℝ)/(50000000))) (r := ((14072347:ℝ)/(100000000))) hqle (by norm_num) exF_d_453_500 exF_e_453_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((11029463:ℝ)/(100000000))) (Ql := ((28990557:ℝ)/(100000000))) (r := ((1759043:ℝ)/(12500000))) hq exG_d_453_500 exG_e_453_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((84905509:ℝ)/(50000000))) hq exG_b_453_500 exF_b_453_500 (by norm_num)
  · exact Bfun_ge (r := ((2653297:ℝ)/(1562500))) hq exG_b_453_500 exF_b_453_500 (by norm_num)
  · exact F2K2_le (al := ((9525083:ℝ)/(12500000))) (r := ((38335469:ℝ)/(50000000))) hq exG_c_453_500 (by norm_num)

lemma v_921_1000 :
    (Work.LinnikAreas.A7.Phi ((921:ℝ)/(1000)) ≤ ((231987:ℝ)/(12500000))) ∧
    (((1855893:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((921:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((921:ℝ)/(1000)) ≤ ((170991:ℝ)/(1250000))) ∧
    (((6839639:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((921:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((921:ℝ)/(1000)) ≤ ((169231271:ℝ)/(100000000))) ∧
    (((84615631:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((921:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((921:ℝ)/(1000)))))/((921:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((1908559:ℝ)/(2500000))) := by
  have hq : (0:ℝ) < ((921:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((921:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((548331:ℝ)/(50000000))) (B := ((169231271:ℝ)/(100000000))) hq exF_a_921_1000 (Bfun_le (r := ((169231271:ℝ)/(100000000))) hq exG_b_921_1000 exF_b_921_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1096661:ℝ)/(100000000))) (B := ((84615631:ℝ)/(50000000))) hq exG_a_921_1000 (Bfun_ge (r := ((84615631:ℝ)/(50000000))) hq exG_b_921_1000 exF_b_921_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((10634147:ℝ)/(100000000))) (Qu := ((14201151:ℝ)/(50000000))) (r := ((170991:ℝ)/(1250000))) hqle (by norm_num) exF_d_921_1000 exF_e_921_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5317073:ℝ)/(50000000))) (Ql := ((28402301:ℝ)/(100000000))) (r := ((6839639:ℝ)/(50000000))) hq exG_d_921_1000 exG_e_921_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((169231271:ℝ)/(100000000))) hq exG_b_921_1000 exF_b_921_1000 (by norm_num)
  · exact Bfun_ge (r := ((84615631:ℝ)/(50000000))) hq exG_b_921_1000 exF_b_921_1000 (by norm_num)
  · exact F2K2_le (al := ((18964633:ℝ)/(25000000))) (r := ((1908559:ℝ)/(2500000))) hq exG_c_921_1000 (by norm_num)

lemma v_37_40 :
    (Work.LinnikAreas.A7.Phi ((37:ℝ)/(40)) ≤ ((227277:ℝ)/(12500000))) ∧
    (((1818213:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((37:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((37:ℝ)/(40)) ≤ ((2715251:ℝ)/(20000000))) ∧
    (((3394063:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Wf ((37:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((37:ℝ)/(40)) ≤ ((169077179:ℝ)/(100000000))) ∧
    (((16907717:ℝ)/(10000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((37:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((37:ℝ)/(40)))))/((37:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((4765939:ℝ)/(6250000))) := by
  have hq : (0:ℝ) < ((37:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((37:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((67211:ℝ)/(6250000))) (B := ((169077179:ℝ)/(100000000))) hq exF_a_37_40 (Bfun_le (r := ((169077179:ℝ)/(100000000))) hq exG_b_37_40 exF_b_37_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((8603:ℝ)/(800000))) (B := ((16907717:ℝ)/(10000000))) hq exG_a_37_40 (Bfun_ge (r := ((16907717:ℝ)/(10000000))) hq exG_b_37_40 exF_b_37_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((10531143:ℝ)/(100000000))) (Qu := ((1412373:ℝ)/(5000000))) (r := ((2715251:ℝ)/(20000000))) hqle (by norm_num) exF_d_37_40 exF_e_37_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5265571:ℝ)/(50000000))) (Ql := ((28247459:ℝ)/(100000000))) (r := ((3394063:ℝ)/(25000000))) hq exG_d_37_40 exG_e_37_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((169077179:ℝ)/(100000000))) hq exG_b_37_40 exF_b_37_40 (by norm_num)
  · exact Bfun_ge (r := ((16907717:ℝ)/(10000000))) hq exG_b_37_40 exF_b_37_40 (by norm_num)
  · exact F2K2_le (al := ((18941889:ℝ)/(25000000))) (r := ((4765939:ℝ)/(6250000))) hq exG_c_37_40 (by norm_num)

lemma v_47_50 :
    (Work.LinnikAreas.A7.Phi ((47:ℝ)/(50)) ≤ ((52613:ℝ)/(3125000))) ∧
    (((1683613:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((47:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((47:ℝ)/(50)) ≤ ((1649563:ℝ)/(12500000))) ∧
    (((13196501:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((47:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((47:ℝ)/(50)) ≤ ((33700239:ℝ)/(20000000))) ∧
    (((33700237:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((47:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((47:ℝ)/(50)))))/((47:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((18982139:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((47:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((47:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((999171:ℝ)/(100000000))) (B := ((33700239:ℝ)/(20000000))) hq exF_a_47_50 (Bfun_le (r := ((33700239:ℝ)/(20000000))) hq exG_b_47_50 exF_b_47_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((99917:ℝ)/(10000000))) (B := ((33700237:ℝ)/(20000000))) hq exG_a_47_50 (Bfun_ge (r := ((33700237:ℝ)/(20000000))) hq exG_b_47_50 exF_b_47_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((10153687:ℝ)/(100000000))) (Qu := ((13837141:ℝ)/(50000000))) (r := ((1649563:ℝ)/(12500000))) hqle (by norm_num) exF_d_47_50 exF_e_47_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5076843:ℝ)/(50000000))) (Ql := ((27674281:ℝ)/(100000000))) (r := ((13196501:ℝ)/(100000000))) hq exG_d_47_50 exG_e_47_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((33700239:ℝ)/(20000000))) hq exG_b_47_50 exF_b_47_50 (by norm_num)
  · exact Bfun_ge (r := ((33700237:ℝ)/(20000000))) hq exG_b_47_50 exF_b_47_50 (by norm_num)
  · exact F2K2_le (al := ((9428421:ℝ)/(12500000))) (r := ((18982139:ℝ)/(25000000))) hq exG_c_47_50 (by norm_num)

lemma v_19_20 :
    (Work.LinnikAreas.A7.Phi ((19:ℝ)/(20)) ≤ ((159947:ℝ)/(10000000))) ∧
    (((1599467:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((19:ℝ)/(20))) ∧
    (Work.LinnikAreas.A7.Wf ((19:ℝ)/(20)) ≤ ((404657:ℝ)/(3125000))) ∧
    (((6474511:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((19:ℝ)/(20))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(20)) ≤ ((168118839:ℝ)/(100000000))) ∧
    (((16811883:ℝ)/(10000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((19:ℝ)/(20))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((19:ℝ)/(20)))))/((19:ℝ)/(20)))^2/((9:ℝ)/100) ≤ ((18927957:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((19:ℝ)/(20)) := by norm_num
  have hqle : (0:ℝ) ≤ ((19:ℝ)/(20)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((29731:ℝ)/(3125000))) (B := ((168118839:ℝ)/(100000000))) hq exF_a_19_20 (Bfun_le (r := ((168118839:ℝ)/(100000000))) hq exG_b_19_20 exF_b_19_20 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((951391:ℝ)/(100000000))) (B := ((16811883:ℝ)/(10000000))) hq exG_a_19_20 (Bfun_ge (r := ((16811883:ℝ)/(10000000))) hq exG_b_19_20 exF_b_19_20 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((2477399:ℝ)/(25000000))) (Qu := ((341233:ℝ)/(1250000))) (r := ((404657:ℝ)/(3125000))) hqle (by norm_num) exF_d_19_20 exF_e_19_20 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1981919:ℝ)/(20000000))) (Ql := ((27298639:ℝ)/(100000000))) (r := ((6474511:ℝ)/(50000000))) hq exG_d_19_20 exG_e_19_20 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((168118839:ℝ)/(100000000))) hq exG_b_19_20 exF_b_19_20 (by norm_num)
  · exact Bfun_ge (r := ((16811883:ℝ)/(10000000))) hq exG_b_19_20 exF_b_19_20 (by norm_num)
  · exact F2K2_le (al := ((3008057:ℝ)/(4000000))) (r := ((18927957:ℝ)/(25000000))) hq exG_c_19_20 (by norm_num)

lemma v_951_1000 :
    (Work.LinnikAreas.A7.Phi ((951:ℝ)/(1000)) ≤ ((1591289:ℝ)/(100000000))) ∧
    (((795643:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((951:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((951:ℝ)/(1000)) ≤ ((6462261:ℝ)/(50000000))) ∧
    (((323113:ℝ)/(2500000)) ≤ Work.LinnikAreas.A7.Wf ((951:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((951:ℝ)/(1000)) ≤ ((84040339:ℝ)/(50000000))) ∧
    (((42020167:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((951:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((951:ℝ)/(1000)))))/((951:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((18922549:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((951:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((951:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((946741:ℝ)/(100000000))) (B := ((84040339:ℝ)/(50000000))) hq exF_a_951_1000 (Bfun_le (r := ((84040339:ℝ)/(50000000))) hq exG_b_951_1000 exF_b_951_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((47337:ℝ)/(5000000))) (B := ((42020167:ℝ)/(25000000))) hq exG_a_951_1000 (Bfun_ge (r := ((42020167:ℝ)/(25000000))) hq exG_b_951_1000 exF_b_951_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1235689:ℝ)/(12500000))) (Qu := ((27261357:ℝ)/(100000000))) (r := ((6462261:ℝ)/(50000000))) hqle (by norm_num) exF_d_951_1000 exF_e_951_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((9885511:ℝ)/(100000000))) (Ql := ((6815339:ℝ)/(25000000))) (r := ((323113:ℝ)/(2500000))) hq exG_d_951_1000 exG_e_951_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((84040339:ℝ)/(50000000))) hq exG_b_951_1000 exF_b_951_1000 (by norm_num)
  · exact Bfun_ge (r := ((42020167:ℝ)/(25000000))) hq exG_b_951_1000 exF_b_951_1000 (by norm_num)
  · exact F2K2_le (al := ((18794717:ℝ)/(25000000))) (r := ((18922549:ℝ)/(25000000))) hq exG_c_951_1000 (by norm_num)

lemma v_39_40 :
    (Work.LinnikAreas.A7.Phi ((39:ℝ)/(40)) ≤ ((703531:ℝ)/(50000000))) ∧
    (((70353:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Phi ((39:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((39:ℝ)/(40)) ≤ ((385927:ℝ)/(3125000))) ∧
    (((6174831:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((39:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((39:ℝ)/(40)) ≤ ((10448041:ℝ)/(6250000))) ∧
    (((167168647:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((39:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((39:ℝ)/(40)))))/((39:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((18793301:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((39:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((39:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((420851:ℝ)/(50000000))) (B := ((10448041:ℝ)/(6250000))) hq exF_a_39_40 (Bfun_le (r := ((10448041:ℝ)/(6250000))) hq exG_b_39_40 exF_b_39_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((841701:ℝ)/(100000000))) (B := ((167168647:ℝ)/(100000000))) hq exG_a_39_40 (Bfun_ge (r := ((167168647:ℝ)/(100000000))) hq exG_b_39_40 exF_b_39_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((2331183:ℝ)/(25000000))) (Qu := ((2638169:ℝ)/(10000000))) (r := ((385927:ℝ)/(3125000))) hqle (by norm_num) exF_d_39_40 exF_e_39_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((9324731:ℝ)/(100000000))) (Ql := ((26381689:ℝ)/(100000000))) (r := ((6174831:ℝ)/(50000000))) hq exG_d_39_40 exG_e_39_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((10448041:ℝ)/(6250000))) hq exG_b_39_40 exF_b_39_40 (by norm_num)
  · exact Bfun_ge (r := ((167168647:ℝ)/(100000000))) hq exG_b_39_40 exF_b_39_40 (by norm_num)
  · exact F2K2_le (al := ((18659881:ℝ)/(25000000))) (r := ((18793301:ℝ)/(25000000))) hq exG_c_39_40 (by norm_num)

lemma v_122_125 :
    (Work.LinnikAreas.A7.Phi ((122:ℝ)/(125)) ≤ ((349967:ℝ)/(25000000))) ∧
    (((279973:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((122:ℝ)/(125))) ∧
    (Work.LinnikAreas.A7.Wf ((122:ℝ)/(125)) ≤ ((6163127:ℝ)/(50000000))) ∧
    (((12326251:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((122:ℝ)/(125))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((122:ℝ)/(125)) ≤ ((83565407:ℝ)/(50000000))) ∧
    (((33426161:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((122:ℝ)/(125))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((122:ℝ)/(125)))))/((122:ℝ)/(125)))^2/((9:ℝ)/100) ≤ ((75151751:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((122:ℝ)/(125)) := by norm_num
  have hqle : (0:ℝ) ≤ ((122:ℝ)/(125)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((209397:ℝ)/(25000000))) (B := ((83565407:ℝ)/(50000000))) hq exF_a_122_125 (Bfun_le (r := ((83565407:ℝ)/(50000000))) hq exG_b_122_125 exF_b_122_125 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((837587:ℝ)/(100000000))) (B := ((33426161:ℝ)/(20000000))) hq exG_a_122_125 (Bfun_ge (r := ((33426161:ℝ)/(20000000))) hq exG_b_122_125 exF_b_122_125 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((930207:ℝ)/(10000000))) (Qu := ((1317283:ℝ)/(5000000))) (r := ((6163127:ℝ)/(50000000))) hqle (by norm_num) exF_d_122_125 exF_e_122_125 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((9302069:ℝ)/(100000000))) (Ql := ((26345659:ℝ)/(100000000))) (r := ((12326251:ℝ)/(100000000))) hq exG_d_122_125 exG_e_122_125 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((83565407:ℝ)/(50000000))) hq exG_b_122_125 exF_b_122_125 (by norm_num)
  · exact Bfun_ge (r := ((33426161:ℝ)/(20000000))) hq exG_b_122_125 exF_b_122_125 (by norm_num)
  · exact F2K2_le (al := ((4663571:ℝ)/(6250000))) (r := ((75151751:ℝ)/(100000000))) hq exG_c_122_125 (by norm_num)

lemma v_983_1000 :
    (Work.LinnikAreas.A7.Phi ((983:ℝ)/(1000)) ≤ ((675263:ℝ)/(50000000))) ∧
    (((337631:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Phi ((983:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((983:ℝ)/(1000)) ≤ ((6081781:ℝ)/(50000000))) ∧
    (((12163559:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((983:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((983:ℝ)/(1000)) ≤ ((1303643:ℝ)/(781250))) ∧
    (((20858287:ℝ)/(12500000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((983:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((983:ℝ)/(1000)))))/((983:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((75001803:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((983:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((983:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((404673:ℝ)/(50000000))) (B := ((1303643:ℝ)/(781250))) hq exF_a_983_1000 (Bfun_le (r := ((1303643:ℝ)/(781250))) hq exG_b_983_1000 exF_b_983_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((161869:ℝ)/(20000000))) (B := ((20858287:ℝ)/(12500000))) hq exG_a_983_1000 (Bfun_ge (r := ((20858287:ℝ)/(12500000))) hq exG_b_983_1000 exF_b_983_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((4572483:ℝ)/(50000000))) (Qu := ((26094821:ℝ)/(100000000))) (r := ((6081781:ℝ)/(50000000))) hqle (by norm_num) exF_d_983_1000 exF_e_983_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1828993:ℝ)/(20000000))) (Ql := ((1304741:ℝ)/(5000000))) (r := ((12163559:ℝ)/(100000000))) hq exG_d_983_1000 exG_e_983_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((1303643:ℝ)/(781250))) hq exG_b_983_1000 exF_b_983_1000 (by norm_num)
  · exact Bfun_ge (r := ((20858287:ℝ)/(12500000))) hq exG_b_983_1000 exF_b_983_1000 (by norm_num)
  · exact F2K2_le (al := ((18615151:ℝ)/(25000000))) (r := ((75001803:ℝ)/(100000000))) hq exG_c_983_1000 (by norm_num)

lemma v_1_1 :
    (Work.LinnikAreas.A7.Phi ((1:ℝ)/(1)) ≤ ((1237821:ℝ)/(100000000))) ∧
    (((1237819:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((1:ℝ)/(1))) ∧
    (Work.LinnikAreas.A7.Wf ((1:ℝ)/(1)) ≤ ((2944249:ℝ)/(25000000))) ∧
    (((5888497:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((1:ℝ)/(1))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(1)) ≤ ((20778317:ℝ)/(12500000))) ∧
    (((166226527:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1:ℝ)/(1))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1:ℝ)/(1)))))/((1:ℝ)/(1)))^2/((9:ℝ)/100) ≤ ((37319553:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((1:ℝ)/(1)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1:ℝ)/(1)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((744659:ℝ)/(100000000))) (B := ((20778317:ℝ)/(12500000))) hq exF_a_1_1 (Bfun_le (r := ((20778317:ℝ)/(12500000))) hq exG_b_1_1 exF_b_1_1 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((372329:ℝ)/(50000000))) (B := ((166226527:ℝ)/(100000000))) hq exG_a_1_1 (Bfun_ge (r := ((166226527:ℝ)/(100000000))) hq exG_b_1_1 exF_b_1_1 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((8774387:ℝ)/(100000000))) (Qu := ((1274777:ℝ)/(5000000))) (r := ((2944249:ℝ)/(25000000))) hqle (by norm_num) exF_d_1_1 exF_e_1_1 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4387193:ℝ)/(50000000))) (Ql := ((25495539:ℝ)/(100000000))) (r := ((5888497:ℝ)/(50000000))) hq exG_d_1_1 exG_e_1_1 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((20778317:ℝ)/(12500000))) hq exG_b_1_1 exF_b_1_1 (by norm_num)
  · exact Bfun_ge (r := ((166226527:ℝ)/(100000000))) hq exG_b_1_1 exF_b_1_1 (by norm_num)
  · exact F2K2_le (al := ((37040911:ℝ)/(50000000))) (r := ((37319553:ℝ)/(50000000))) hq exG_c_1_1 (by norm_num)

lemma v_507_500 :
    (Work.LinnikAreas.A7.Phi ((507:ℝ)/(500)) ≤ ((115211:ℝ)/(10000000))) ∧
    (((1152107:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((507:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((507:ℝ)/(500)) ≤ ((716721:ℝ)/(6250000))) ∧
    (((5733767:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((507:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((507:ℝ)/(500)) ≤ ((165702443:ℝ)/(100000000))) ∧
    (((33140487:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((507:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((507:ℝ)/(500)))))/((507:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((3717099:ℝ)/(5000000))) := by
  have hq : (0:ℝ) < ((507:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((507:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((86911:ℝ)/(12500000))) (B := ((165702443:ℝ)/(100000000))) hq exF_a_507_500 (Bfun_le (r := ((165702443:ℝ)/(100000000))) hq exG_b_507_500 exF_b_507_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((695287:ℝ)/(100000000))) (B := ((33140487:ℝ)/(20000000))) hq exG_a_507_500 (Bfun_ge (r := ((33140487:ℝ)/(20000000))) hq exG_b_507_500 exF_b_507_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((8480507:ℝ)/(100000000))) (Qu := ((25012363:ℝ)/(100000000))) (r := ((716721:ℝ)/(6250000))) hqle (by norm_num) exF_d_507_500 exF_e_507_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4240253:ℝ)/(50000000))) (Ql := ((12506181:ℝ)/(50000000))) (r := ((5733767:ℝ)/(50000000))) hq exG_d_507_500 exG_e_507_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((165702443:ℝ)/(100000000))) hq exG_b_507_500 exF_b_507_500 (by norm_num)
  · exact Bfun_ge (r := ((33140487:ℝ)/(20000000))) hq exG_b_507_500 exF_b_507_500 (by norm_num)
  · exact F2K2_le (al := ((7377133:ℝ)/(10000000))) (r := ((3717099:ℝ)/(5000000))) hq exG_c_507_500 (by norm_num)

lemma v_1017_1000 :
    (Work.LinnikAreas.A7.Phi ((1017:ℝ)/(1000)) ≤ ((113453:ℝ)/(10000000))) ∧
    (((17727:ℝ)/(1562500)) ≤ Work.LinnikAreas.A7.Phi ((1017:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((1017:ℝ)/(1000)) ≤ ((1425281:ℝ)/(12500000))) ∧
    (((2280449:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((1017:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1017:ℝ)/(1000)) ≤ ((8279523:ℝ)/(5000000))) ∧
    (((41397613:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1017:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1017:ℝ)/(1000)))))/((1017:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((74278489:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((1017:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1017:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((342571:ℝ)/(50000000))) (B := ((8279523:ℝ)/(5000000))) hq exF_a_1017_1000 (Bfun_le (r := ((8279523:ℝ)/(5000000))) hq exG_b_1017_1000 exF_b_1017_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((685141:ℝ)/(100000000))) (B := ((41397613:ℝ)/(25000000))) hq exG_a_1017_1000 (Bfun_ge (r := ((41397613:ℝ)/(25000000))) hq exG_b_1017_1000 exF_b_1017_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((336753:ℝ)/(4000000))) (Qu := ((12455011:ℝ)/(50000000))) (r := ((1425281:ℝ)/(12500000))) hqle (by norm_num) exF_d_1017_1000 exF_e_1017_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1052353:ℝ)/(12500000))) (Ql := ((24910021:ℝ)/(100000000))) (r := ((2280449:ℝ)/(20000000))) hq exG_d_1017_1000 exG_e_1017_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((8279523:ℝ)/(5000000))) hq exG_b_1017_1000 exF_b_1017_1000 (by norm_num)
  · exact Bfun_ge (r := ((41397613:ℝ)/(25000000))) hq exG_b_1017_1000 exF_b_1017_1000 (by norm_num)
  · exact F2K2_le (al := ((36852483:ℝ)/(50000000))) (r := ((74278489:ℝ)/(100000000))) hq exG_c_1017_1000 (by norm_num)

lemma v_41_40 :
    (Work.LinnikAreas.A7.Phi ((41:ℝ)/(40)) ≤ ((1088953:ℝ)/(100000000))) ∧
    (((1088951:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((41:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((41:ℝ)/(40)) ≤ ((2245977:ℝ)/(20000000))) ∧
    (((11229883:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((41:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((41:ℝ)/(40)) ≤ ((41323101:ℝ)/(25000000))) ∧
    (((41323099:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((41:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((41:ℝ)/(40)))))/((41:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((74109501:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((41:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((41:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((164701:ℝ)/(25000000))) (B := ((41323101:ℝ)/(25000000))) hq exF_a_41_40 (Bfun_le (r := ((41323101:ℝ)/(25000000))) hq exG_b_41_40 exF_b_41_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((658803:ℝ)/(100000000))) (B := ((41323099:ℝ)/(25000000))) hq exG_a_41_40 (Bfun_ge (r := ((41323099:ℝ)/(25000000))) hq exG_b_41_40 exF_b_41_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((8256523:ℝ)/(100000000))) (Qu := ((6159789:ℝ)/(25000000))) (r := ((2245977:ℝ)/(20000000))) hqle (by norm_num) exF_d_41_40 exF_e_41_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4128261:ℝ)/(50000000))) (Ql := ((4927831:ℝ)/(20000000))) (r := ((11229883:ℝ)/(100000000))) hq exG_d_41_40 exG_e_41_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((41323101:ℝ)/(25000000))) hq exG_b_41_40 exF_b_41_40 (by norm_num)
  · exact Bfun_ge (r := ((41323099:ℝ)/(25000000))) hq exG_b_41_40 exF_b_41_40 (by norm_num)
  · exact F2K2_le (al := ((36764143:ℝ)/(50000000))) (r := ((74109501:ℝ)/(100000000))) hq exG_c_41_40 (by norm_num)

lemma v_21_20 :
    (Work.LinnikAreas.A7.Phi ((21:ℝ)/(20)) ≤ ((191601:ℝ)/(20000000))) ∧
    (((958003:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((21:ℝ)/(20))) ∧
    (Work.LinnikAreas.A7.Wf ((21:ℝ)/(20)) ≤ ((2141449:ℝ)/(20000000))) ∧
    (((10707243:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((21:ℝ)/(20))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(20)) ≤ ((82183089:ℝ)/(50000000))) ∧
    (((164366171:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((21:ℝ)/(20))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((21:ℝ)/(20)))))/((21:ℝ)/(20)))^2/((9:ℝ)/100) ≤ ((36792167:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((21:ℝ)/(20)) := by norm_num
  have hqle : (0:ℝ) ≤ ((21:ℝ)/(20)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((9107:ℝ)/(1562500))) (B := ((82183089:ℝ)/(50000000))) hq exF_a_21_20 (Bfun_le (r := ((82183089:ℝ)/(50000000))) hq exG_b_21_20 exF_b_21_20 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((582847:ℝ)/(100000000))) (B := ((164366171:ℝ)/(100000000))) hq exG_a_21_20 (Bfun_ge (r := ((164366171:ℝ)/(100000000))) hq exG_b_21_20 exF_b_21_20 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((971153:ℝ)/(12500000))) (Qu := ((23811537:ℝ)/(100000000))) (r := ((2141449:ℝ)/(20000000))) hqle (by norm_num) exF_d_21_20 exF_e_21_20 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((7769223:ℝ)/(100000000))) (Ql := ((1488221:ℝ)/(6250000))) (r := ((10707243:ℝ)/(100000000))) hq exG_d_21_20 exG_e_21_20 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((82183089:ℝ)/(50000000))) hq exG_b_21_20 exF_b_21_20 (by norm_num)
  · exact Bfun_ge (r := ((164366171:ℝ)/(100000000))) hq exG_b_21_20 exF_b_21_20 (by norm_num)
  · exact F2K2_le (al := ((72978887:ℝ)/(100000000))) (r := ((36792167:ℝ)/(50000000))) hq exG_c_21_20 (by norm_num)

lemma v_527_500 :
    (Work.LinnikAreas.A7.Phi ((527:ℝ)/(500)) ≤ ((117321:ℝ)/(12500000))) ∧
    (((187713:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((527:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((527:ℝ)/(500)) ≤ ((10625823:ℝ)/(100000000))) ∧
    (((531291:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((527:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((527:ℝ)/(500)) ≤ ((16421871:ℝ)/(10000000))) ∧
    (((82109351:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((527:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((527:ℝ)/(500)))))/((527:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((18375179:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((527:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((527:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((114307:ℝ)/(20000000))) (B := ((16421871:ℝ)/(10000000))) hq exF_a_527_500 (Bfun_le (r := ((16421871:ℝ)/(10000000))) hq exG_b_527_500 exF_b_527_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((285767:ℝ)/(50000000))) (B := ((82109351:ℝ)/(50000000))) hq exG_a_527_500 (Bfun_ge (r := ((82109351:ℝ)/(50000000))) hq exG_b_527_500 exF_b_527_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((769397:ℝ)/(10000000))) (Qu := ((11840861:ℝ)/(50000000))) (r := ((10625823:ℝ)/(100000000))) hqle (by norm_num) exF_d_527_500 exF_e_527_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((7693969:ℝ)/(100000000))) (Ql := ((23681721:ℝ)/(100000000))) (r := ((531291:ℝ)/(5000000))) hq exG_d_527_500 exG_e_527_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((16421871:ℝ)/(10000000))) hq exG_b_527_500 exF_b_527_500 (by norm_num)
  · exact Bfun_ge (r := ((82109351:ℝ)/(50000000))) hq exG_b_527_500 exF_b_527_500 (by norm_num)
  · exact F2K2_le (al := ((14578273:ℝ)/(20000000))) (r := ((18375179:ℝ)/(25000000))) hq exG_c_527_500 (by norm_num)

lemma v_43_40 :
    (Work.LinnikAreas.A7.Phi ((43:ℝ)/(40)) ≤ ((842817:ℝ)/(100000000))) ∧
    (((168563:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((43:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((43:ℝ)/(40)) ≤ ((1020803:ℝ)/(10000000))) ∧
    (((10208027:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((43:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((43:ℝ)/(40)) ≤ ((163447777:ℝ)/(100000000))) ∧
    (((16344777:ℝ)/(10000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((43:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((43:ℝ)/(40)))))/((43:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((73063571:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((43:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((43:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((515649:ℝ)/(100000000))) (B := ((163447777:ℝ)/(100000000))) hq exF_a_43_40 (Bfun_le (r := ((163447777:ℝ)/(100000000))) hq exG_b_43_40 exF_b_43_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((8057:ℝ)/(1562500))) (B := ((16344777:ℝ)/(10000000))) hq exG_a_43_40 (Bfun_ge (r := ((16344777:ℝ)/(10000000))) hq exG_b_43_40 exF_b_43_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1462137:ℝ)/(20000000))) (Qu := ((23011717:ℝ)/(100000000))) (r := ((1020803:ℝ)/(10000000))) hqle (by norm_num) exF_d_43_40 exF_e_43_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1827671:ℝ)/(25000000))) (Ql := ((5752929:ℝ)/(25000000))) (r := ((10208027:ℝ)/(100000000))) hq exG_d_43_40 exG_e_43_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((163447777:ℝ)/(100000000))) hq exG_b_43_40 exF_b_43_40 (by norm_num)
  · exact Bfun_ge (r := ((16344777:ℝ)/(10000000))) hq exG_b_43_40 exF_b_43_40 (by norm_num)
  · exact F2K2_le (al := ((72433593:ℝ)/(100000000))) (r := ((73063571:ℝ)/(100000000))) hq exG_c_43_40 (by norm_num)

lemma v_1093_1000 :
    (Work.LinnikAreas.A7.Phi ((1093:ℝ)/(1000)) ≤ ((384283:ℝ)/(50000000))) ∧
    (((768563:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((1093:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((1093:ℝ)/(1000)) ≤ ((4931267:ℝ)/(50000000))) ∧
    (((2465633:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Wf ((1093:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1093:ℝ)/(1000)) ≤ ((162791329:ℝ)/(100000000))) ∧
    (((81395661:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1093:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1093:ℝ)/(1000)))))/((1093:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((7269133:ℝ)/(10000000))) := by
  have hq : (0:ℝ) < ((1093:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1093:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((472117:ℝ)/(100000000))) (B := ((162791329:ℝ)/(100000000))) hq exF_a_1093_1000 (Bfun_le (r := ((162791329:ℝ)/(100000000))) hq exG_b_1093_1000 exF_b_1093_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((118029:ℝ)/(25000000))) (B := ((81395661:ℝ)/(50000000))) hq exG_a_1093_1000 (Bfun_ge (r := ((81395661:ℝ)/(50000000))) hq exG_b_1093_1000 exF_b_1093_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1749347:ℝ)/(25000000))) (Qu := ((4490507:ℝ)/(20000000))) (r := ((4931267:ℝ)/(50000000))) hqle (by norm_num) exF_d_1093_1000 exF_e_1093_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6997387:ℝ)/(100000000))) (Ql := ((11226267:ℝ)/(50000000))) (r := ((2465633:ℝ)/(25000000))) hq exG_d_1093_1000 exG_e_1093_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((162791329:ℝ)/(100000000))) hq exG_b_1093_1000 exF_b_1093_1000 (by norm_num)
  · exact Bfun_ge (r := ((81395661:ℝ)/(50000000))) hq exG_b_1093_1000 exF_b_1093_1000 (by norm_num)
  · exact F2K2_le (al := ((14408701:ℝ)/(20000000))) (r := ((7269133:ℝ)/(10000000))) hq exG_c_1093_1000 (by norm_num)

lemma v_549_500 :
    (Work.LinnikAreas.A7.Phi ((549:ℝ)/(500)) ≤ ((749129:ℝ)/(100000000))) ∧
    (((374563:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((549:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((549:ℝ)/(500)) ≤ ((4884289:ℝ)/(50000000))) ∧
    (((390743:ℝ)/(4000000)) ≤ Work.LinnikAreas.A7.Wf ((549:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((549:ℝ)/(500)) ≤ ((162609691:ℝ)/(100000000))) ∧
    (((162609683:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((549:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((549:ℝ)/(500)))))/((549:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((36294163:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((549:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((549:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((460691:ℝ)/(100000000))) (B := ((162609691:ℝ)/(100000000))) hq exF_a_549_500 (Bfun_le (r := ((162609691:ℝ)/(100000000))) hq exG_b_549_500 exF_b_549_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((46069:ℝ)/(10000000))) (B := ((162609683:ℝ)/(100000000))) hq exG_a_549_500 (Bfun_ge (r := ((162609683:ℝ)/(100000000))) hq exG_b_549_500 exF_b_549_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((6912769:ℝ)/(100000000))) (Qu := ((22299633:ℝ)/(100000000))) (r := ((4884289:ℝ)/(50000000))) hqle (by norm_num) exF_d_549_500 exF_e_549_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((27003:ℝ)/(390625))) (Ql := ((1393727:ℝ)/(6250000))) (r := ((390743:ℝ)/(4000000))) hq exG_d_549_500 exG_e_549_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((162609691:ℝ)/(100000000))) hq exG_b_549_500 exF_b_549_500 (by norm_num)
  · exact Bfun_ge (r := ((162609683:ℝ)/(100000000))) hq exG_b_549_500 exF_b_549_500 (by norm_num)
  · exact F2K2_le (al := ((71935521:ℝ)/(100000000))) (r := ((36294163:ℝ)/(50000000))) hq exG_c_549_500 (by norm_num)

lemma v_11_10 :
    (Work.LinnikAreas.A7.Phi ((11:ℝ)/(10)) ≤ ((185373:ℝ)/(25000000))) ∧
    (((741489:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((11:ℝ)/(10))) ∧
    (Work.LinnikAreas.A7.Wf ((11:ℝ)/(10)) ≤ ((2432809:ℝ)/(25000000))) ∧
    (((9731233:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((11:ℝ)/(10))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(10)) ≤ ((162537123:ℝ)/(100000000))) ∧
    (((40634279:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((11:ℝ)/(10))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((11:ℝ)/(10)))))/((11:ℝ)/(10)))^2/((9:ℝ)/100) ≤ ((18136793:ℝ)/(25000000))) := by
  have hq : (0:ℝ) < ((11:ℝ)/(10)) := by norm_num
  have hqle : (0:ℝ) ≤ ((11:ℝ)/(10)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((228099:ℝ)/(50000000))) (B := ((162537123:ℝ)/(100000000))) hq exF_a_11_10 (Bfun_le (r := ((162537123:ℝ)/(100000000))) hq exG_b_11_10 exF_b_11_10 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((456197:ℝ)/(100000000))) (B := ((40634279:ℝ)/(25000000))) hq exG_a_11_10 (Bfun_ge (r := ((40634279:ℝ)/(25000000))) hq exG_b_11_10 exF_b_11_10 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((859901:ℝ)/(12500000))) (Qu := ((5559691:ℝ)/(25000000))) (r := ((2432809:ℝ)/(25000000))) hqle (by norm_num) exF_d_11_10 exF_e_11_10 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6879207:ℝ)/(100000000))) (Ql := ((22238763:ℝ)/(100000000))) (r := ((9731233:ℝ)/(100000000))) hq exG_d_11_10 exG_e_11_10 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((162537123:ℝ)/(100000000))) hq exG_b_11_10 exF_b_11_10 (by norm_num)
  · exact Bfun_ge (r := ((40634279:ℝ)/(25000000))) hq exG_b_11_10 exF_b_11_10 (by norm_num)
  · exact F2K2_le (al := ((71892373:ℝ)/(100000000))) (r := ((18136793:ℝ)/(25000000))) hq exG_c_11_10 (by norm_num)

lemma v_9_8 :
    (Work.LinnikAreas.A7.Phi ((9:ℝ)/(8)) ≤ ((326179:ℝ)/(50000000))) ∧
    (((130471:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((9:ℝ)/(8))) ∧
    (Work.LinnikAreas.A7.Wf ((9:ℝ)/(8)) ≤ ((36234:ℝ)/(390625))) ∧
    (((4637951:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((9:ℝ)/(8))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(8)) ≤ ((161634139:ℝ)/(100000000))) ∧
    (((40408533:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(8))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(8)))))/((9:ℝ)/(8)))^2/((9:ℝ)/100) ≤ ((36017547:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((9:ℝ)/(8)) := by norm_num
  have hqle : (0:ℝ) ≤ ((9:ℝ)/(8)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((403601:ℝ)/(100000000))) (B := ((161634139:ℝ)/(100000000))) hq exF_a_9_8 (Bfun_le (r := ((161634139:ℝ)/(100000000))) hq exG_b_9_8 exF_b_9_8 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((1009:ℝ)/(250000))) (B := ((40408533:ℝ)/(25000000))) hq exG_a_9_8 (Bfun_ge (r := ((40408533:ℝ)/(25000000))) hq exG_b_9_8 exF_b_9_8 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((3236599:ℝ)/(50000000))) (Qu := ((21491773:ℝ)/(100000000))) (r := ((36234:ℝ)/(390625))) hqle (by norm_num) exF_d_9_8 exF_e_9_8 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6473197:ℝ)/(100000000))) (Ql := ((5372943:ℝ)/(25000000))) (r := ((4637951:ℝ)/(50000000))) hq exG_d_9_8 exG_e_9_8 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((161634139:ℝ)/(100000000))) hq exG_b_9_8 exF_b_9_8 (by norm_num)
  · exact Bfun_ge (r := ((40408533:ℝ)/(25000000))) hq exG_b_9_8 exF_b_9_8 (by norm_num)
  · exact F2K2_le (al := ((71355197:ℝ)/(100000000))) (r := ((36017547:ℝ)/(50000000))) hq exG_c_9_8 (by norm_num)

lemma v_567_500 :
    (Work.LinnikAreas.A7.Phi ((567:ℝ)/(500)) ≤ ((311483:ℝ)/(50000000))) ∧
    (((622963:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((567:ℝ)/(500))) ∧
    (Work.LinnikAreas.A7.Wf ((567:ℝ)/(500)) ≤ ((455853:ℝ)/(5000000))) ∧
    (((9117057:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((567:ℝ)/(500))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((567:ℝ)/(500)) ≤ ((80655463:ℝ)/(50000000))) ∧
    (((161310919:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((567:ℝ)/(500))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((567:ℝ)/(500)))))/((567:ℝ)/(500)))^2/((9:ℝ)/100) ≤ ((14370359:ℝ)/(20000000))) := by
  have hq : (0:ℝ) < ((567:ℝ)/(500)) := by norm_num
  have hqle : (0:ℝ) ≤ ((567:ℝ)/(500)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((386189:ℝ)/(100000000))) (B := ((80655463:ℝ)/(50000000))) hq exF_a_567_500 (Bfun_le (r := ((80655463:ℝ)/(50000000))) hq exG_b_567_500 exF_b_567_500 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((96547:ℝ)/(25000000))) (B := ((161310919:ℝ)/(100000000))) hq exG_a_567_500 (Bfun_ge (r := ((161310919:ℝ)/(100000000))) hq exG_b_567_500 exF_b_567_500 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((395811:ℝ)/(6250000))) (Qu := ((21229043:ℝ)/(100000000))) (r := ((455853:ℝ)/(5000000))) hqle (by norm_num) exF_d_567_500 exF_e_567_500 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((253319:ℝ)/(4000000))) (Ql := ((10614521:ℝ)/(50000000))) (r := ((9117057:ℝ)/(100000000))) hq exG_d_567_500 exG_e_567_500 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((80655463:ℝ)/(50000000))) hq exG_b_567_500 exF_b_567_500 (by norm_num)
  · exact Bfun_ge (r := ((161310919:ℝ)/(100000000))) hq exG_b_567_500 exF_b_567_500 (by norm_num)
  · exact F2K2_le (al := ((35581399:ℝ)/(50000000))) (r := ((14370359:ℝ)/(20000000))) hq exG_c_567_500 (by norm_num)

lemma v_143_125 :
    (Work.LinnikAreas.A7.Phi ((143:ℝ)/(125)) ≤ ((29593:ℝ)/(5000000))) ∧
    (((591857:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((143:ℝ)/(125))) ∧
    (Work.LinnikAreas.A7.Wf ((143:ℝ)/(125)) ≤ ((2235909:ℝ)/(25000000))) ∧
    (((8943633:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((143:ℝ)/(125))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((143:ℝ)/(125)) ≤ ((160952951:ℝ)/(100000000))) ∧
    (((10059559:ℝ)/(6250000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((143:ℝ)/(125))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((143:ℝ)/(125)))))/((143:ℝ)/(125)))^2/((9:ℝ)/100) ≤ ((35824391:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((143:ℝ)/(125)) := by norm_num
  have hqle : (0:ℝ) ≤ ((143:ℝ)/(125)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((183861:ℝ)/(50000000))) (B := ((160952951:ℝ)/(100000000))) hq exF_a_143_125 (Bfun_le (r := ((160952951:ℝ)/(100000000))) hq exG_b_143_125 exF_b_143_125 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((367721:ℝ)/(100000000))) (B := ((10059559:ℝ)/(6250000))) hq exG_a_143_125 (Bfun_ge (r := ((10059559:ℝ)/(6250000))) hq exG_b_143_125 exF_b_143_125 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((6180733:ℝ)/(100000000))) (Qu := ((20940887:ℝ)/(100000000))) (r := ((2235909:ℝ)/(25000000))) hqle (by norm_num) exF_d_143_125 exF_e_143_125 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1545183:ℝ)/(25000000))) (Ql := ((10470443:ℝ)/(50000000))) (r := ((8943633:ℝ)/(100000000))) hq exG_d_143_125 exG_e_143_125 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((160952951:ℝ)/(100000000))) hq exG_b_143_125 exF_b_143_125 (by norm_num)
  · exact Bfun_ge (r := ((10059559:ℝ)/(6250000))) hq exG_b_143_125 exF_b_143_125 (by norm_num)
  · exact F2K2_le (al := ((70949629:ℝ)/(100000000))) (r := ((35824391:ℝ)/(50000000))) hq exG_c_143_125 (by norm_num)

lemma v_23_20 :
    (Work.LinnikAreas.A7.Phi ((23:ℝ)/(20)) ≤ ((573947:ℝ)/(100000000))) ∧
    (((71743:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Phi ((23:ℝ)/(20))) ∧
    (Work.LinnikAreas.A7.Wf ((23:ℝ)/(20)) ≤ ((884111:ℝ)/(10000000))) ∧
    (((2210277:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Wf ((23:ℝ)/(20))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(20)) ≤ ((32147749:ℝ)/(20000000))) ∧
    (((80369369:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((23:ℝ)/(20))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((23:ℝ)/(20)))))/((23:ℝ)/(20)))^2/((9:ℝ)/100) ≤ ((71527297:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((23:ℝ)/(20)) := by norm_num
  have hqle : (0:ℝ) ≤ ((23:ℝ)/(20)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((89267:ℝ)/(25000000))) (B := ((32147749:ℝ)/(20000000))) hq exF_a_23_20 (Bfun_le (r := ((32147749:ℝ)/(20000000))) hq exG_b_23_20 exF_b_23_20 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((357067:ℝ)/(100000000))) (B := ((80369369:ℝ)/(50000000))) hq exG_a_23_20 (Bfun_ge (r := ((80369369:ℝ)/(50000000))) hq exG_b_23_20 exF_b_23_20 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((121823:ℝ)/(2000000))) (Qu := ((20769873:ℝ)/(100000000))) (r := ((884111:ℝ)/(10000000))) hqle (by norm_num) exF_d_23_20 exF_e_23_20 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((6091149:ℝ)/(100000000))) (Ql := ((1298117:ℝ)/(6250000))) (r := ((2210277:ℝ)/(25000000))) hq exG_d_23_20 exG_e_23_20 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((32147749:ℝ)/(20000000))) hq exG_b_23_20 exF_b_23_20 (by norm_num)
  · exact Bfun_ge (r := ((80369369:ℝ)/(50000000))) hq exG_b_23_20 exF_b_23_20 (by norm_num)
  · exact F2K2_le (al := ((14164407:ℝ)/(20000000))) (r := ((71527297:ℝ)/(100000000))) hq exG_c_23_20 (by norm_num)

lemma v_47_40 :
    (Work.LinnikAreas.A7.Phi ((47:ℝ)/(40)) ≤ ((504969:ℝ)/(100000000))) ∧
    (((504967:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((47:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((47:ℝ)/(40)) ≤ ((842597:ℝ)/(10000000))) ∧
    (((8425967:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((47:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((47:ℝ)/(40)) ≤ ((159850869:ℝ)/(100000000))) ∧
    (((159850863:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((47:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((47:ℝ)/(40)))))/((47:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((554873:ℝ)/(781250))) := by
  have hq : (0:ℝ) < ((47:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((47:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((3159:ℝ)/(1000000))) (B := ((159850869:ℝ)/(100000000))) hq exF_a_47_40 (Bfun_le (r := ((159850869:ℝ)/(100000000))) hq exG_b_47_40 exF_b_47_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((315899:ℝ)/(100000000))) (B := ((159850863:ℝ)/(100000000))) hq exG_a_47_40 (Bfun_ge (r := ((159850863:ℝ)/(100000000))) hq exG_b_47_40 exF_b_47_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5731651:ℝ)/(100000000))) (Qu := ((10036111:ℝ)/(50000000))) (r := ((842597:ℝ)/(10000000))) hqle (by norm_num) exF_d_47_40 exF_e_47_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((114633:ℝ)/(2000000))) (Ql := ((20072221:ℝ)/(100000000))) (r := ((8425967:ℝ)/(100000000))) hq exG_d_47_40 exG_e_47_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((159850869:ℝ)/(100000000))) hq exG_b_47_40 exF_b_47_40 (by norm_num)
  · exact Bfun_ge (r := ((159850863:ℝ)/(100000000))) hq exG_b_47_40 exF_b_47_40 (by norm_num)
  · exact F2K2_le (al := ((8786607:ℝ)/(12500000))) (r := ((554873:ℝ)/(781250))) hq exG_c_47_40 (by norm_num)

lemma v_59_50 :
    (Work.LinnikAreas.A7.Phi ((59:ℝ)/(50)) ≤ ((123051:ℝ)/(25000000))) ∧
    (((246101:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((59:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((59:ℝ)/(50)) ≤ ((1043153:ℝ)/(12500000))) ∧
    (((8345221:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((59:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((59:ℝ)/(50)) ≤ ((39918547:ℝ)/(25000000))) ∧
    (((159674181:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((59:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((59:ℝ)/(50)))))/((59:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((70923537:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((59:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((59:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((61651:ℝ)/(20000000))) (B := ((39918547:ℝ)/(25000000))) hq exF_a_59_50 (Bfun_le (r := ((39918547:ℝ)/(25000000))) hq exG_b_59_50 exF_b_59_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((154127:ℝ)/(50000000))) (B := ((159674181:ℝ)/(100000000))) hq exG_a_59_50 (Bfun_ge (r := ((159674181:ℝ)/(100000000))) hq exG_b_59_50 exF_b_59_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((2831169:ℝ)/(50000000))) (Qu := ((1993553:ℝ)/(10000000))) (r := ((1043153:ℝ)/(12500000))) hqle (by norm_num) exF_d_59_50 exF_e_59_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((5662337:ℝ)/(100000000))) (Ql := ((19935529:ℝ)/(100000000))) (r := ((8345221:ℝ)/(100000000))) hq exG_d_59_50 exG_e_59_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((39918547:ℝ)/(25000000))) hq exG_b_59_50 exF_b_59_50 (by norm_num)
  · exact Bfun_ge (r := ((159674181:ℝ)/(100000000))) hq exG_b_59_50 exF_b_59_50 (by norm_num)
  · exact F2K2_le (al := ((8773437:ℝ)/(12500000))) (r := ((70923537:ℝ)/(100000000))) hq exG_c_59_50 (by norm_num)

lemma v_239_200 :
    (Work.LinnikAreas.A7.Phi ((239:ℝ)/(200)) ≤ ((113953:ℝ)/(25000000))) ∧
    (((455809:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((239:ℝ)/(200))) ∧
    (Work.LinnikAreas.A7.Wf ((239:ℝ)/(200)) ≤ ((4053717:ℝ)/(50000000))) ∧
    (((1013429:ℝ)/(12500000)) ≤ Work.LinnikAreas.A7.Wf ((239:ℝ)/(200))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((239:ℝ)/(200)) ≤ ((19893241:ℝ)/(12500000))) ∧
    (((79572961:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((239:ℝ)/(200))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((239:ℝ)/(200)))))/((239:ℝ)/(200)))^2/((9:ℝ)/100) ≤ ((2824957:ℝ)/(4000000))) := by
  have hq : (0:ℝ) < ((239:ℝ)/(200)) := by norm_num
  have hqle : (0:ℝ) ≤ ((239:ℝ)/(200)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((286411:ℝ)/(100000000))) (B := ((19893241:ℝ)/(12500000))) hq exF_a_239_200 (Bfun_le (r := ((19893241:ℝ)/(12500000))) hq exG_b_239_200 exF_b_239_200 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((28641:ℝ)/(10000000))) (B := ((79572961:ℝ)/(50000000))) hq exG_a_239_200 (Bfun_ge (r := ((79572961:ℝ)/(50000000))) hq exG_b_239_200 exF_b_239_200 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5459389:ℝ)/(100000000))) (Qu := ((4882753:ℝ)/(25000000))) (r := ((4053717:ℝ)/(50000000))) hqle (by norm_num) exF_d_239_200 exF_e_239_200 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1364847:ℝ)/(25000000))) (Ql := ((19531011:ℝ)/(100000000))) (r := ((1013429:ℝ)/(12500000))) hq exG_d_239_200 exG_e_239_200 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((19893241:ℝ)/(12500000))) hq exG_b_239_200 exF_b_239_200 (by norm_num)
  · exact Bfun_ge (r := ((79572961:ℝ)/(50000000))) hq exG_b_239_200 exF_b_239_200 (by norm_num)
  · exact F2K2_le (al := ((34936181:ℝ)/(50000000))) (r := ((2824957:ℝ)/(4000000))) hq exG_c_239_200 (by norm_num)

lemma v_6_5 :
    (Work.LinnikAreas.A7.Phi ((6:ℝ)/(5)) ≤ ((444289:ℝ)/(100000000))) ∧
    (((444287:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/(5))) ∧
    (Work.LinnikAreas.A7.Wf ((6:ℝ)/(5)) ≤ ((125463:ℝ)/(1562500))) ∧
    (((8029629:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((6:ℝ)/(5))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((6:ℝ)/(5)) ≤ ((158970433:ℝ)/(100000000))) ∧
    (((79485213:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((6:ℝ)/(5))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((6:ℝ)/(5)))))/((6:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((70524389:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((6:ℝ)/(5)) := by norm_num
  have hqle : (0:ℝ) ≤ ((6:ℝ)/(5)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((279479:ℝ)/(100000000))) (B := ((158970433:ℝ)/(100000000))) hq exF_a_6_5 (Bfun_le (r := ((158970433:ℝ)/(100000000))) hq exG_b_6_5 exF_b_6_5 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((139739:ℝ)/(50000000))) (B := ((79485213:ℝ)/(50000000))) hq exG_a_6_5 (Bfun_ge (r := ((79485213:ℝ)/(50000000))) hq exG_b_6_5 exF_b_6_5 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5393369:ℝ)/(100000000))) (Qu := ((3879601:ℝ)/(20000000))) (r := ((125463:ℝ)/(1562500))) hqle (by norm_num) exF_d_6_5 exF_e_6_5 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((674171:ℝ)/(12500000))) (Ql := ((4849501:ℝ)/(25000000))) (r := ((8029629:ℝ)/(100000000))) hq exG_d_6_5 exG_e_6_5 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((158970433:ℝ)/(100000000))) hq exG_b_6_5 exF_b_6_5 (by norm_num)
  · exact Bfun_ge (r := ((79485213:ℝ)/(50000000))) hq exG_b_6_5 exF_b_6_5 (by norm_num)
  · exact F2K2_le (al := ((4360477:ℝ)/(6250000))) (r := ((70524389:ℝ)/(100000000))) hq exG_c_6_5 (by norm_num)

lemma v_49_40 :
    (Work.LinnikAreas.A7.Phi ((49:ℝ)/(40)) ≤ ((390907:ℝ)/(100000000))) ∧
    (((78181:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((49:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((49:ℝ)/(40)) ≤ ((7651283:ℝ)/(100000000))) ∧
    (((95641:ℝ)/(1250000)) ≤ Work.LinnikAreas.A7.Wf ((49:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((49:ℝ)/(40)) ≤ ((79048681:ℝ)/(50000000))) ∧
    (((31619471:ℝ)/(20000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((49:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((49:ℝ)/(40)))))/((49:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((70029199:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((49:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((49:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((247257:ℝ)/(100000000))) (B := ((79048681:ℝ)/(50000000))) hq exF_a_49_40 (Bfun_le (r := ((79048681:ℝ)/(50000000))) hq exG_b_49_40 exF_b_49_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((30907:ℝ)/(12500000))) (B := ((31619471:ℝ)/(20000000))) hq exG_a_49_40 (Bfun_ge (r := ((31619471:ℝ)/(20000000))) hq exG_b_49_40 exF_b_49_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((5075053:ℝ)/(100000000))) (Qu := ((9373217:ℝ)/(50000000))) (r := ((7651283:ℝ)/(100000000))) hqle (by norm_num) exF_d_49_40 exF_e_49_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((1268763:ℝ)/(25000000))) (Ql := ((18746433:ℝ)/(100000000))) (r := ((95641:ℝ)/(1250000))) hq exG_d_49_40 exG_e_49_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((79048681:ℝ)/(50000000))) hq exG_b_49_40 exF_b_49_40 (by norm_num)
  · exact Bfun_ge (r := ((31619471:ℝ)/(20000000))) hq exG_b_49_40 exF_b_49_40 (by norm_num)
  · exact F2K2_le (al := ((17311583:ℝ)/(25000000))) (r := ((70029199:ℝ)/(100000000))) hq exG_c_49_40 (by norm_num)

lemma v_1249_1000 :
    (Work.LinnikAreas.A7.Phi ((1249:ℝ)/(1000)) ≤ ((345709:ℝ)/(100000000))) ∧
    (((172853:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((1249:ℝ)/(1000))) ∧
    (Work.LinnikAreas.A7.Wf ((1249:ℝ)/(1000)) ≤ ((3652133:ℝ)/(50000000))) ∧
    (((7304263:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((1249:ℝ)/(1000))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((1249:ℝ)/(1000)) ≤ ((39316519:ℝ)/(25000000))) ∧
    (((15726607:ℝ)/(10000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((1249:ℝ)/(1000))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((1249:ℝ)/(1000)))))/((1249:ℝ)/(1000)))^2/((9:ℝ)/100) ≤ ((69557697:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((1249:ℝ)/(1000)) := by norm_num
  have hqle : (0:ℝ) ≤ ((1249:ℝ)/(1000)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((13739:ℝ)/(6250000))) (B := ((39316519:ℝ)/(25000000))) hq exF_a_1249_1000 (Bfun_le (r := ((39316519:ℝ)/(25000000))) hq exG_b_1249_1000 exF_b_1249_1000 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((219823:ℝ)/(100000000))) (B := ((15726607:ℝ)/(10000000))) hq exG_a_1249_1000 (Bfun_ge (r := ((15726607:ℝ)/(10000000))) hq exG_b_1249_1000 exF_b_1249_1000 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((2393579:ℝ)/(50000000))) (Qu := ((9070763:ℝ)/(50000000))) (r := ((3652133:ℝ)/(50000000))) hqle (by norm_num) exF_d_1249_1000 exF_e_1249_1000 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4787157:ℝ)/(100000000))) (Ql := ((725661:ℝ)/(4000000))) (r := ((7304263:ℝ)/(100000000))) hq exG_d_1249_1000 exG_e_1249_1000 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((39316519:ℝ)/(25000000))) hq exG_b_1249_1000 exF_b_1249_1000 (by norm_num)
  · exact Bfun_ge (r := ((15726607:ℝ)/(10000000))) hq exG_b_1249_1000 exF_b_1249_1000 (by norm_num)
  · exact F2K2_le (al := ((68749549:ℝ)/(100000000))) (r := ((69557697:ℝ)/(100000000))) hq exG_c_1249_1000 (by norm_num)

lemma v_5_4 :
    (Work.LinnikAreas.A7.Phi ((5:ℝ)/(4)) ≤ ((68789:ℝ)/(20000000))) ∧
    (((171971:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Phi ((5:ℝ)/(4))) ∧
    (Work.LinnikAreas.A7.Wf ((5:ℝ)/(4)) ≤ ((3645071:ℝ)/(50000000))) ∧
    (((364507:ℝ)/(5000000)) ≤ Work.LinnikAreas.A7.Wf ((5:ℝ)/(4))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((5:ℝ)/(4)) ≤ ((31446317:ℝ)/(20000000))) ∧
    (((157231579:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((5:ℝ)/(4))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((5:ℝ)/(4)))))/((5:ℝ)/(4)))^2/((9:ℝ)/100) ≤ ((34769067:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((5:ℝ)/(4)) := by norm_num
  have hqle : (0:ℝ) ≤ ((5:ℝ)/(4)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((7:ℝ)/(3200))) (B := ((31446317:ℝ)/(20000000))) hq exF_a_5_4 (Bfun_le (r := ((31446317:ℝ)/(20000000))) hq exG_b_5_4 exF_b_5_4 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((218749:ℝ)/(100000000))) (B := ((157231579:ℝ)/(100000000))) hq exG_a_5_4 (Bfun_ge (r := ((157231579:ℝ)/(100000000))) hq exG_b_5_4 exF_b_5_4 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1193881:ℝ)/(25000000))) (Qu := ((18116749:ℝ)/(100000000))) (r := ((3645071:ℝ)/(50000000))) hqle (by norm_num) exF_d_5_4 exF_e_5_4 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4775523:ℝ)/(100000000))) (Ql := ((4529187:ℝ)/(25000000))) (r := ((364507:ℝ)/(5000000))) hq exG_d_5_4 exG_e_5_4 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((31446317:ℝ)/(20000000))) hq exG_b_5_4 exF_b_5_4 (by norm_num)
  · exact Bfun_ge (r := ((157231579:ℝ)/(100000000))) hq exG_b_5_4 exF_b_5_4 (by norm_num)
  · exact F2K2_le (al := ((68728927:ℝ)/(100000000))) (r := ((34769067:ℝ)/(50000000))) hq exG_c_5_4 (by norm_num)

lemma v_127_100 :
    (Work.LinnikAreas.A7.Phi ((127:ℝ)/(100)) ≤ ((310473:ℝ)/(100000000))) ∧
    (((31047:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Phi ((127:ℝ)/(100))) ∧
    (Work.LinnikAreas.A7.Wf ((127:ℝ)/(100)) ≤ ((7013113:ℝ)/(100000000))) ∧
    (((701311:ℝ)/(10000000)) ≤ Work.LinnikAreas.A7.Wf ((127:ℝ)/(100))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((127:ℝ)/(100)) ≤ ((78272081:ℝ)/(50000000))) ∧
    (((39136039:ℝ)/(25000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((127:ℝ)/(100))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((127:ℝ)/(100)))))/((127:ℝ)/(100)))^2/((9:ℝ)/100) ≤ ((34574113:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((127:ℝ)/(100)) := by norm_num
  have hqle : (0:ℝ) ≤ ((127:ℝ)/(100)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((198329:ℝ)/(100000000))) (B := ((78272081:ℝ)/(50000000))) hq exF_a_127_100 (Bfun_le (r := ((78272081:ℝ)/(50000000))) hq exG_b_127_100 exF_b_127_100 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((24791:ℝ)/(12500000))) (B := ((39136039:ℝ)/(25000000))) hq exG_a_127_100 (Bfun_ge (r := ((39136039:ℝ)/(25000000))) hq exG_b_127_100 exF_b_127_100 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((4548679:ℝ)/(100000000))) (Qu := ((2203533:ℝ)/(12500000))) (r := ((7013113:ℝ)/(100000000))) hqle (by norm_num) exF_d_127_100 exF_e_127_100 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((2274339:ℝ)/(50000000))) (Ql := ((17628263:ℝ)/(100000000))) (r := ((701311:ℝ)/(10000000))) hq exG_d_127_100 exG_e_127_100 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((78272081:ℝ)/(50000000))) hq exG_b_127_100 exF_b_127_100 (by norm_num)
  · exact Bfun_ge (r := ((39136039:ℝ)/(25000000))) hq exG_b_127_100 exF_b_127_100 (by norm_num)
  · exact F2K2_le (al := ((17079447:ℝ)/(25000000))) (r := ((34574113:ℝ)/(50000000))) hq exG_c_127_100 (by norm_num)

lemma v_51_40 :
    (Work.LinnikAreas.A7.Phi ((51:ℝ)/(40)) ≤ ((75657:ℝ)/(25000000))) ∧
    (((2421:ℝ)/(800000)) ≤ Work.LinnikAreas.A7.Phi ((51:ℝ)/(40))) ∧
    (Work.LinnikAreas.A7.Wf ((51:ℝ)/(40)) ≤ ((6945459:ℝ)/(100000000))) ∧
    (((6945457:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Wf ((51:ℝ)/(40))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((51:ℝ)/(40)) ≤ ((78186513:ℝ)/(50000000))) ∧
    (((7818651:ℝ)/(5000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((51:ℝ)/(40))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((51:ℝ)/(40)))))/((51:ℝ)/(40)))^2/((9:ℝ)/100) ≤ ((4315697:ℝ)/(6250000))) := by
  have hq : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hqle : (0:ℝ) ≤ ((51:ℝ)/(40)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((193529:ℝ)/(100000000))) (B := ((78186513:ℝ)/(50000000))) hq exF_a_51_40 (Bfun_le (r := ((78186513:ℝ)/(50000000))) hq exG_b_51_40 exF_b_51_40 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((24191:ℝ)/(12500000))) (B := ((7818651:ℝ)/(5000000))) hq exG_a_51_40 (Bfun_ge (r := ((7818651:ℝ)/(5000000))) hq exG_b_51_40 exF_b_51_40 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((4493673:ℝ)/(100000000))) (Qu := ((3501643:ℝ)/(20000000))) (r := ((6945459:ℝ)/(100000000))) hqle (by norm_num) exF_d_51_40 exF_e_51_40 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((561709:ℝ)/(12500000))) (Ql := ((8754107:ℝ)/(50000000))) (r := ((6945457:ℝ)/(100000000))) hq exG_d_51_40 exG_e_51_40 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((78186513:ℝ)/(50000000))) hq exG_b_51_40 exF_b_51_40 (by norm_num)
  · exact Bfun_ge (r := ((7818651:ℝ)/(5000000))) hq exG_b_51_40 exF_b_51_40 (by norm_num)
  · exact F2K2_le (al := ((68215389:ℝ)/(100000000))) (r := ((4315697:ℝ)/(6250000))) hq exG_c_51_40 (by norm_num)

lemma v_327_250 :
    (Work.LinnikAreas.A7.Phi ((327:ℝ)/(250)) ≤ ((255597:ℝ)/(100000000))) ∧
    (((51119:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Phi ((327:ℝ)/(250))) ∧
    (Work.LinnikAreas.A7.Wf ((327:ℝ)/(250)) ≤ ((1302893:ℝ)/(20000000))) ∧
    (((3257231:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((327:ℝ)/(250))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((327:ℝ)/(250)) ≤ ((7762533:ℝ)/(5000000))) ∧
    (((77625327:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((327:ℝ)/(250))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((327:ℝ)/(250)))))/((327:ℝ)/(250)))^2/((9:ℝ)/100) ≤ ((34207267:ℝ)/(50000000))) := by
  have hq : (0:ℝ) < ((327:ℝ)/(250)) := by norm_num
  have hqle : (0:ℝ) ≤ ((327:ℝ)/(250)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((32927:ℝ)/(20000000))) (B := ((7762533:ℝ)/(5000000))) hq exF_a_327_250 (Bfun_le (r := ((7762533:ℝ)/(5000000))) hq exG_b_327_250 exF_b_327_250 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((82317:ℝ)/(50000000))) (B := ((77625327:ℝ)/(50000000))) hq exG_a_327_250 (Bfun_ge (r := ((77625327:ℝ)/(50000000))) hq exG_b_327_250 exF_b_327_250 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((2073469:ℝ)/(50000000))) (Qu := ((2092017:ℝ)/(12500000))) (r := ((1302893:ℝ)/(20000000))) hqle (by norm_num) exF_d_327_250 exF_e_327_250 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((4146937:ℝ)/(100000000))) (Ql := ((3347227:ℝ)/(20000000))) (r := ((3257231:ℝ)/(50000000))) hq exG_d_327_250 exG_e_327_250 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((7762533:ℝ)/(5000000))) hq exG_b_327_250 exF_b_327_250 (by norm_num)
  · exact Bfun_ge (r := ((77625327:ℝ)/(50000000))) hq exG_b_327_250 exF_b_327_250 (by norm_num)
  · exact F2K2_le (al := ((16885847:ℝ)/(25000000))) (r := ((34207267:ℝ)/(50000000))) hq exG_c_327_250 (by norm_num)

lemma v_141_100 :
    (Work.LinnikAreas.A7.Phi ((141:ℝ)/(100)) ≤ ((151671:ℝ)/(100000000))) ∧
    (((37917:ℝ)/(25000000)) ≤ Work.LinnikAreas.A7.Phi ((141:ℝ)/(100))) ∧
    (Work.LinnikAreas.A7.Wf ((141:ℝ)/(100)) ≤ ((5339317:ℝ)/(100000000))) ∧
    (((2669657:ℝ)/(50000000)) ≤ Work.LinnikAreas.A7.Wf ((141:ℝ)/(100))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((141:ℝ)/(100)) ≤ ((75929259:ℝ)/(50000000))) ∧
    (((151858513:ℝ)/(100000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((141:ℝ)/(100))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((141:ℝ)/(100)))))/((141:ℝ)/(100)))^2/((9:ℝ)/100) ≤ ((66490481:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((141:ℝ)/(100)) := by norm_num
  have hqle : (0:ℝ) ≤ ((141:ℝ)/(100)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((24969:ℝ)/(25000000))) (B := ((75929259:ℝ)/(50000000))) hq exF_a_141_100 (Bfun_le (r := ((75929259:ℝ)/(50000000))) hq exG_b_141_100 exF_b_141_100 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((799:ℝ)/(800000))) (B := ((151858513:ℝ)/(100000000))) hq exG_a_141_100 (Bfun_ge (r := ((151858513:ℝ)/(100000000))) hq exG_b_141_100 exF_b_141_100 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1617729:ℝ)/(50000000))) (Qu := ((1455843:ℝ)/(10000000))) (r := ((5339317:ℝ)/(100000000))) hqle (by norm_num) exF_d_141_100 exF_e_141_100 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((3235457:ℝ)/(100000000))) (Ql := ((14558429:ℝ)/(100000000))) (r := ((2669657:ℝ)/(50000000))) hq exG_d_141_100 exG_e_141_100 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((75929259:ℝ)/(50000000))) hq exG_b_141_100 exF_b_141_100 (by norm_num)
  · exact Bfun_ge (r := ((151858513:ℝ)/(100000000))) hq exG_b_141_100 exF_b_141_100 (by norm_num)
  · exact F2K2_le (al := ((65507863:ℝ)/(100000000))) (r := ((66490481:ℝ)/(100000000))) hq exG_c_141_100 (by norm_num)

lemma v_79_50 :
    (Work.LinnikAreas.A7.Phi ((79:ℝ)/(50)) ≤ ((7949:ℝ)/(12500000))) ∧
    (((63589:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((79:ℝ)/(50))) ∧
    (Work.LinnikAreas.A7.Wf ((79:ℝ)/(50)) ≤ ((955287:ℝ)/(25000000))) ∧
    (((764229:ℝ)/(20000000)) ≤ Work.LinnikAreas.A7.Wf ((79:ℝ)/(50))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((79:ℝ)/(50)) ≤ ((73226621:ℝ)/(50000000))) ∧
    (((73226619:ℝ)/(50000000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((79:ℝ)/(50))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((79:ℝ)/(50)))))/((79:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((63425011:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((79:ℝ)/(50)) := by norm_num
  have hqle : (0:ℝ) ≤ ((79:ℝ)/(50)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((43421:ℝ)/(100000000))) (B := ((73226621:ℝ)/(50000000))) hq exF_a_79_50 (Bfun_le (r := ((73226621:ℝ)/(50000000))) hq exG_b_79_50 exF_b_79_50 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((2171:ℝ)/(5000000))) (B := ((73226619:ℝ)/(50000000))) hq exG_a_79_50 (Bfun_ge (r := ((73226619:ℝ)/(50000000))) hq exG_b_79_50 exF_b_79_50 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((1069677:ℝ)/(50000000))) (Qu := ((2885051:ℝ)/(25000000))) (r := ((955287:ℝ)/(25000000))) hqle (by norm_num) exF_d_79_50 exF_e_79_50 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((2139353:ℝ)/(100000000))) (Ql := ((11540203:ℝ)/(100000000))) (r := ((764229:ℝ)/(20000000))) hq exG_d_79_50 exG_e_79_50 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((73226621:ℝ)/(50000000))) hq exG_b_79_50 exF_b_79_50 (by norm_num)
  · exact Bfun_ge (r := ((73226619:ℝ)/(50000000))) hq exG_b_79_50 exF_b_79_50 (by norm_num)
  · exact F2K2_le (al := ((2490029:ℝ)/(4000000))) (r := ((63425011:ℝ)/(100000000))) hq exG_c_79_50 (by norm_num)

lemma v_9_5 :
    (Work.LinnikAreas.A7.Phi ((9:ℝ)/(5)) ≤ ((20669:ℝ)/(100000000))) ∧
    (((20667:ℝ)/(100000000)) ≤ Work.LinnikAreas.A7.Phi ((9:ℝ)/(5))) ∧
    (Work.LinnikAreas.A7.Wf ((9:ℝ)/(5)) ≤ ((1232589:ℝ)/(50000000))) ∧
    (((98607:ℝ)/(4000000)) ≤ Work.LinnikAreas.A7.Wf ((9:ℝ)/(5))) ∧
    (Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(5)) ≤ ((34972489:ℝ)/(25000000))) ∧
    (((4371561:ℝ)/(3125000)) ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) ((9:ℝ)/(5))) ∧
    (((1-Real.exp (-((3:ℝ)/10*((9:ℝ)/(5)))))/((9:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((59704741:ℝ)/(100000000))) := by
  have hq : (0:ℝ) < ((9:ℝ)/(5)) := by norm_num
  have hqle : (0:ℝ) ≤ ((9:ℝ)/(5)) := le_of_lt hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Phi_le (E := ((591:ℝ)/(4000000))) (B := ((34972489:ℝ)/(25000000))) hq exF_a_9_5 (Bfun_le (r := ((34972489:ℝ)/(25000000))) hq exG_b_9_5 exF_b_9_5 (by norm_num)) (by norm_num)
  · exact Phi_ge (E := ((7387:ℝ)/(50000000))) (B := ((4371561:ℝ)/(3125000))) hq exG_a_9_5 (Bfun_ge (r := ((4371561:ℝ)/(3125000))) hq exG_b_9_5 exF_b_9_5 (by norm_num)) (by norm_num) (by norm_num)
  · exact Wf_le (Pu := ((156567:ℝ)/(12500000))) (Qu := ((1067937:ℝ)/(12500000))) (r := ((1232589:ℝ)/(50000000))) hqle (by norm_num) exF_d_9_5 exF_e_9_5 (by norm_num) (by norm_num)
  · exact Wf_ge (Pl := ((250507:ℝ)/(20000000))) (Ql := ((1708699:ℝ)/(20000000))) (r := ((98607:ℝ)/(4000000))) hq exG_d_9_5 exG_e_9_5 (by norm_num) (by norm_num)
  · exact Bfun_le (r := ((34972489:ℝ)/(25000000))) hq exG_b_9_5 exF_b_9_5 (by norm_num)
  · exact Bfun_ge (r := ((4371561:ℝ)/(3125000))) hq exG_b_9_5 exF_b_9_5 (by norm_num)
  · exact F2K2_le (al := ((2330993:ℝ)/(4000000))) (r := ((59704741:ℝ)/(100000000))) hq exG_c_9_5 (by norm_num)


end Work.LinnikAreas.A7
