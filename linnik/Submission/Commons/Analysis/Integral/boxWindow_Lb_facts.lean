import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.Integral

/-! ## Numerical facts about the box-window lower bound `Lb` -/

noncomputable def at8f (y : ℝ) : ℝ :=
  y - y^3/3 + y^5/5 - y^7/7 + y^9/9 - y^11/11 + y^13/13 - y^15/15
noncomputable def S3f (y : ℝ) : ℝ := y - y^3/3 + y^5/5 - y^7/7
noncomputable def S1f (y : ℝ) : ℝ := y - y^3/3

/-- The degree-15 Taylor truncation of `arctan` dominates the degree-7 truncation on `[0,1]`. -/
lemma S3f_le_at8f {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : S3f y ≤ at8f y := by
  have hy2 : y^2 ≤ 1 := by nlinarith
  have hy4 : y^4 ≤ 1 := by nlinarith [sq_nonneg y]
  have hy6 : y^6 ≤ 1 := by nlinarith [hy2, sq_nonneg y]
  have hb : (0:ℝ) ≤ (1/9:ℝ) - y^2/11 + y^4/13 - y^6/15 := by
    have h1 : (1/9:ℝ) - y^2/11 ≥ 1/9 - 1/11 := by nlinarith
    have h2 : (0:ℝ) ≤ y^4 * ((1/13:ℝ) - y^2/15) := by
      apply mul_nonneg (by positivity)
      nlinarith
    nlinarith [h1, h2]
  have hy9 : (0:ℝ) ≤ y^9 := by positivity
  have hsplit : at8f y - S3f y = y^9 * ((1/9:ℝ) - y^2/11 + y^4/13 - y^6/15) := by
    unfold at8f S3f; ring
  nlinarith [mul_nonneg hy9 hb, hsplit]

lemma S1f_le_S3f {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : S1f y ≤ S3f y := by
  have hy2 : y^2 ≤ 1 := by nlinarith
  have hb : (0:ℝ) ≤ (1/5:ℝ) - y^2/7 := by nlinarith
  have hy5 : (0:ℝ) ≤ y^5 := by positivity
  have hsplit : S3f y - S1f y = y^5 * ((1/5:ℝ) - y^2/7) := by unfold S3f S1f; ring
  nlinarith [mul_nonneg hy5 hb, hsplit]

lemma S1f_le_at8f {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : S1f y ≤ at8f y :=
  le_trans (S1f_le_S3f hy0 hy1) (S3f_le_at8f hy0 hy1)

noncomputable def WPTf (b : ℝ) : ℝ :=
  (13/5)*(at8f ((1/2)/(3/2-b)) + at8f ((1/2)/(1+b)))
    + ((2-b)^2-b^2)/(2*(2-b)) * at8f ((1/2)/(2-b))
    + ((2-b)^2-b^2)^2/8 * ((at8f ((1/2)/(2-b)) + (2-b)*(1/2)/((2-b)^2+(1/2)^2))/(2*(2-b)^3))
    + ((2-b)^2-b^2)^3/16 * (3*at8f ((1/2)/(2-b))/(8*(2-b)^5)
        + (1/2)*(5*(2-b)^2+3*(1/2)^2)/(8*(2-b)^4*((2-b)^2+(1/2)^2)^2))

noncomputable def WPTfS (b : ℝ) : ℝ :=
  (13/5)*(S3f ((1/2)/(3/2-b)) + S1f ((1/2)/(1+b)))
    + ((2-b)^2-b^2)/(2*(2-b)) * S1f ((1/2)/(2-b))
    + ((2-b)^2-b^2)^2/8 * ((S1f ((1/2)/(2-b)) + (2-b)*(1/2)/((2-b)^2+(1/2)^2))/(2*(2-b)^3))
    + ((2-b)^2-b^2)^3/16 * (3*S1f ((1/2)/(2-b))/(8*(2-b)^5)
        + (1/2)*(5*(2-b)^2+3*(1/2)^2)/(8*(2-b)^4*((2-b)^2+(1/2)^2)^2))

noncomputable def WTStf (b : ℝ) : ℝ :=
  (13/5)*((3/2-b)/(((3/2-b)^2+1/4)^2) + (1+b)/(((1+b)^2+1/4)^2))
    + ((2-b)^2-b^2) * (1/(2*(((2-b)^2+1/4)^2)))
    + ((2-b)^2-b^2)^2 * (1/(2*(2-b)^5))
    + ((2-b)^2-b^2)^3 * (3/(8*(2-b)^7))

noncomputable def C1f (b : ℝ) : ℝ := WTStf b + 1/(4*(2-b)^2)

noncomputable def Lbfif (b : ℝ) : ℝ :=
  2*WPTf b - (3*(6931471808/10^10) - (1-b)^2 - (1-b)^4/2) - (6931471808/10^10) - 2
    - 1/(48*(2-b)^2) - 1/(48*b^2)
noncomputable def Lbfelse (b : ℝ) : ℝ :=
  2*WPTf b - (2*(6931471808/10^10) - b/2) - (6931471808/10^10) - 1 - 1/(48*(2-b)^2)
    - 2*b*((6931471808/10^10)+13/12) - (1-2*b)
noncomputable def Lbf (b : ℝ) : ℝ := if 1/2 ≤ b then Lbfif b else Lbfelse b
noncomputable def LbfSif (b : ℝ) : ℝ :=
  2*WPTfS b - (3*(6931471808/10^10) - (1-b)^2 - (1-b)^4/2) - (6931471808/10^10) - 2
    - 1/(48*(2-b)^2) - 1/(48*b^2)
noncomputable def LbfSelse (b : ℝ) : ℝ :=
  2*WPTfS b - (2*(6931471808/10^10) - b/2) - (6931471808/10^10) - 1 - 1/(48*(2-b)^2)
    - 2*b*((6931471808/10^10)+13/12) - (1-2*b)

/-- Replacing the `arctan` truncations by smaller truncations decreases `WPTlb`. -/
lemma WPTfS_le_WPTf {b : ℝ} (h0 : 0 < b) (h1 : b < 1) : WPTfS b ≤ WPTf b := by
  have hA : (0:ℝ) < 3/2 - b := by linarith
  have hB : (0:ℝ) < 1 + b := by linarith
  have hC : (0:ℝ) < 2 - b := by linarith
  have hD : (0:ℝ) ≤ (2-b)^2 - b^2 := by nlinarith
  have hD2 : (0:ℝ) ≤ ((2-b)^2 - b^2)^2 := by positivity
  have hD3 : (0:ℝ) ≤ ((2-b)^2 - b^2)^3 := pow_nonneg hD 3
  have e1 : (0:ℝ) ≤ (1/2)/(3/2-b) := by positivity
  have e1' : (1/2)/(3/2-b) ≤ 1 := by rw [div_le_one hA]; linarith
  have e2 : (0:ℝ) ≤ (1/2)/(1+b) := by positivity
  have e2' : (1/2)/(1+b) ≤ 1 := by rw [div_le_one hB]; linarith
  have e3 : (0:ℝ) ≤ (1/2)/(2-b) := by positivity
  have e3' : (1/2)/(2-b) ≤ 1 := by rw [div_le_one hC]; linarith
  have h1' := S3f_le_at8f e1 e1'
  have h2' := S1f_le_at8f e2 e2'
  have h3' := S1f_le_at8f e3 e3'
  unfold WPTfS WPTf
  have step1 : (13/5)*(S3f ((1/2)/(3/2-b)) + S1f ((1/2)/(1+b)))
      ≤ (13/5)*(at8f ((1/2)/(3/2-b)) + at8f ((1/2)/(1+b))) := by linarith
  have step2 : ((2-b)^2-b^2)/(2*(2-b)) * S1f ((1/2)/(2-b))
      ≤ ((2-b)^2-b^2)/(2*(2-b)) * at8f ((1/2)/(2-b)) := by
    apply mul_le_mul_of_nonneg_left h3'
    exact div_nonneg hD (by positivity)
  have step3 : ((2-b)^2-b^2)^2/8 * ((S1f ((1/2)/(2-b)) + (2-b)*(1/2)/((2-b)^2+(1/2)^2))/(2*(2-b)^3))
      ≤ ((2-b)^2-b^2)^2/8 * ((at8f ((1/2)/(2-b)) + (2-b)*(1/2)/((2-b)^2+(1/2)^2))/(2*(2-b)^3)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have step4 : ((2-b)^2-b^2)^3/16 * (3*S1f ((1/2)/(2-b))/(8*(2-b)^5)
        + (1/2)*(5*(2-b)^2+3*(1/2)^2)/(8*(2-b)^4*((2-b)^2+(1/2)^2)^2))
      ≤ ((2-b)^2-b^2)^3/16 * (3*at8f ((1/2)/(2-b))/(8*(2-b)^5)
        + (1/2)*(5*(2-b)^2+3*(1/2)^2)/(8*(2-b)^4*((2-b)^2+(1/2)^2)^2)) := by
    apply mul_le_mul_of_nonneg_left _ (by exact div_nonneg hD3 (by norm_num))
    have h33 : 3*S1f ((1/2)/(2-b))/(8*(2-b)^5) ≤ 3*at8f ((1/2)/(2-b))/(8*(2-b)^5) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    linarith
  linarith

lemma LbfSif_le_Lbfif {b : ℝ} (h0 : 0 < b) (h1 : b < 1) : LbfSif b ≤ Lbfif b := by
  have h := WPTfS_le_WPTf h0 h1
  unfold LbfSif Lbfif
  linarith

lemma LbfSelse_le_Lbfelse {b : ℝ} (h0 : 0 < b) (h1 : b < 1) : LbfSelse b ≤ Lbfelse b := by
  have h := WPTfS_le_WPTf h0 h1
  unfold LbfSelse Lbfelse
  linarith

noncomputable def QA (b : ℝ) : ℝ := 3281250000*(2-b)^8*(1+b)^3*(3-2*b)^7*(4*b^2-16*b+17)^2
noncomputable def QB (b : ℝ) : ℝ := 1640625000*b^2*(2-b)^8*(1+b)^3*(3-2*b)^7*(4*b^2-16*b+17)^2
noncomputable def QC (b : ℝ) : ℝ := 1640625000*(2-b)^8*(1+b)^3*(3-2*b)^7*(2*b^2-6*b+5)^2*(4*b^2-16*b+17)^2*(4*b^2+8*b+5)^2
noncomputable def QD (b : ℝ) : ℝ := 410156250*b^2*(2-b)^8*(1+b)^3*(3-2*b)^7*(2*b^2-6*b+5)^2*(4*b^2-16*b+17)^2*(4*b^2+8*b+5)^2
noncomputable def certSA (b : ℝ) : ℝ := 2806746718083389425975296*(1/2-b)^23 + 49536558872917104666869760*b*(1/2-b)^22 + 415124434291450739202981888*b^2*(1/2-b)^21 + 2198253250670864491326996480*b^3*(1/2-b)^20 + 8257367409931235531888263168*b^4*(1/2-b)^19 + 23411889793219627496767488000*b^5*(1/2-b)^18 + 52045631285785593658067255296*b^6*(1/2-b)^17 + 93013514022262348645094195200*b^7*(1/2-b)^16 + 135927867346369171637123809280*b^8*(1/2-b)^15 + 164328284382294871297495203840*b^9*(1/2-b)^14 + 165606224306238046085277458432*b^10*(1/2-b)^13 + 139750116045677363458380574720*b^11*(1/2-b)^12 + 98925675642851100601583886336*b^12*(1/2-b)^11 + 58696018174278546004213186560*b^13*(1/2-b)^10 + 29092244806312555563720933376*b^14*(1/2-b)^9 + 11969498692953282416670851072*b^15*(1/2-b)^8 + 4047981006835263748621893632*b^16*(1/2-b)^7 + 1109197281057927400839643136*b^17*(1/2-b)^6 + 241179397861039072400506880*b^18*(1/2-b)^5 + 40360172432114015345442816*b^19*(1/2-b)^4 + 4960593608017297853644800*b^20*(1/2-b)^3 + 414567919302030896136192*b^21*(1/2-b)^2 + 20376886527516884336640*b^22*(1/2-b) + 412048927556252467200*b^23
noncomputable def certSB (b : ℝ) : ℝ := 5457564798225009868800*(1-b)^28 + 104182044425421733232640*(b-1/2)*(1-b)^27 + 959324830785070351515648*(b-1/2)^2*(1-b)^26 + 5821234803753506604318720*(b-1/2)^3*(1-b)^25 + 27019061803033390134067200*(b-1/2)^4*(1-b)^24 + 104898164103584624739745792*(b-1/2)^5*(1-b)^23 + 355261349452661206552215552*(b-1/2)^6*(1-b)^22 + 1053595245435022201236455424*(b-1/2)^7*(1-b)^21 + 2700489715956492986803421184*(b-1/2)^8*(1-b)^20 + 5907873297610811600806445056*(b-1/2)^9*(1-b)^19 + 10964158487262021327710109696*(b-1/2)^10*(1-b)^18 + 17245077338145349390504419328*(b-1/2)^11*(1-b)^17 + 23027992149274001969607081984*(b-1/2)^12*(1-b)^16 + 26173059403364503400602828800*(b-1/2)^13*(1-b)^15 + 25377151307197682977502003200*(b-1/2)^14*(1-b)^14 + 21019574076727008093068722176*(b-1/2)^15*(1-b)^13 + 14875671743349460805469863936*(b-1/2)^16*(1-b)^12 + 8983707002015294923042324480*(b-1/2)^17*(1-b)^11 + 4616279930342240611975299072*(b-1/2)^18*(1-b)^10 + 2008473925856280519081197568*(b-1/2)^19*(1-b)^9 + 734548038786612677265326080*(b-1/2)^20*(1-b)^8 + 223498321671052203273486336*(b-1/2)^21*(1-b)^7 + 55766759190412365853097984*(b-1/2)^22*(1-b)^6 + 11182889948516258691416064*(b-1/2)^23*(1-b)^5 + 1750749767588030044962816*(b-1/2)^24*(1-b)^4 + 204885747358489689194496*(b-1/2)^25*(1-b)^3 + 16708616703698846875648*(b-1/2)^26*(1-b)^2 + 834636046096526213120*(b-1/2)^27*(1-b) + 18714509706474291200*(b-1/2)^28
noncomputable def certSC (b : ℝ) : ℝ := 1615565186456580397855219370227138560000*(1/4-b)^31 + 46429396352308529443173587161744146432000*b*(1/4-b)^30 + 645075066135043685780638873093613499187200*b^2*(1/4-b)^29 + 5770827689160658698343300205057695662735360*b^3*(1/4-b)^28 + 37352393305045795827917053696115745451147264*b^4*(1/4-b)^27 + 186350975937653791468139777058952096801357824*b^5*(1/4-b)^26 + 745446416508194279395660652738611139244457984*b^6*(1/4-b)^25 + 2455671221577188075228197682951674332499148800*b^7*(1/4-b)^24 + 6789822297676643147108004218038604248763072512*b^8*(1/4-b)^23 + 15979813694742621359382861249466389380263313408*b^9*(1/4-b)^22 + 32351120209792278958047526218728038900401438720*b^10*(1/4-b)^21 + 56791547684250400186673471380246109503537283072*b^11*(1/4-b)^20 + 86971893910405142561571883120924466810999275520*b^12*(1/4-b)^19 + 116713256999288275928984509157771658873110790144*b^13*(1/4-b)^18 + 137684807024899330007586081317491081187193520128*b^14*(1/4-b)^17 + 143074151126160301300443244055485625029175017472*b^15*(1/4-b)^16 + 131093320001479611397570848347886562483420266496*b^16*(1/4-b)^15 + 105913153996916086777437321994479887735827988480*b^17*(1/4-b)^14 + 75378197505765500933887107001185229702791430144*b^18*(1/4-b)^13 + 47162280853498860750424843830464090491490140160*b^19*(1/4-b)^12 + 25860086592125227058792005949075994402822815744*b^20*(1/4-b)^11 + 12371362184574254188702724415025327276826820608*b^21*(1/4-b)^10 + 5132687306975828052054607153678649904185999360*b^22*(1/4-b)^9 + 1832106871716427456516483121296825552312729600*b^23*(1/4-b)^8 + 556759638824185951894576429866608379297792000*b^24*(1/4-b)^7 + 142041852444209360864778550133319301857280000*b^25*(1/4-b)^6 + 29849880036537350418761316686345797632000000*b^26*(1/4-b)^5 + 5031070684025312553039560690282528768000000*b^27*(1/4-b)^4 + 653796489587621898421359889467310080000000*b^28*(1/4-b)^3 + 61492198331025902988615571569049600000000*b^29*(1/4-b)^2 + 3725308422452590970972853878784000000000*b^30*(1/4-b) + 109148708587100159742398663680000000000*b^31
noncomputable def certSD (b : ℝ) : ℝ := 17101048711146670150704333619200000000*(1-b)^36 + 577526277455698516439121953095680000000*(b-3/4)*(1-b)^35 + 9466241498166327554938466716483584000000*(b-3/4)^2*(1-b)^34 + 100309514623733052449618361287599718400000*(b-3/4)^3*(1-b)^33 + 772272188804278637958070451021807616000000*(b-3/4)^4*(1-b)^32 + 4602878763483071792592407866358718529536000*(b-3/4)^5*(1-b)^31 + 22098821480631999753065030719812831438438400*(b-3/4)^6*(1-b)^30 + 87805738126932424008159452991040130457272320*(b-3/4)^7*(1-b)^29 + 294387551679552630665585035808518641027121152*(b-3/4)^8*(1-b)^28 + 844971023886619712810513634157118195821969408*(b-3/4)^9*(1-b)^27 + 2099393113349761605881828584354905285202018304*(b-3/4)^10*(1-b)^26 + 4554162297472091569916040388770592561242832896*(b-3/4)^11*(1-b)^25 + 8683847981706442060636562829203208429134413824*(b-3/4)^12*(1-b)^24 + 14631884492545240230796296401831156274381717504*(b-3/4)^13*(1-b)^23 + 21875502577340073538764234028132627919663005696*(b-3/4)^14*(1-b)^22 + 29110183914146690573613786003036683578567032832*(b-3/4)^15*(1-b)^21 + 34558336938105532381244118034947454965360099328*(b-3/4)^16*(1-b)^20 + 36656048816944423010751898353114100458252664832*(b-3/4)^17*(1-b)^19 + 34768399685814395281719351980748739004636069888*(b-3/4)^18*(1-b)^18 + 29494563933320014602292904269489639028919631872*(b-3/4)^19*(1-b)^17 + 22366751032345192760813495983301630587052228608*(b-3/4)^20*(1-b)^16 + 15144634102603984199781746012329139187558121472*(b-3/4)^21*(1-b)^15 + 9138783800336785038745501965753961559158161408*(b-3/4)^22*(1-b)^14 + 4901477822761411121964399811395925530296451072*(b-3/4)^23*(1-b)^13 + 2328198672337205270792613425329088000570687488*(b-3/4)^24*(1-b)^12 + 974890872738642782662954929122347445158674432*(b-3/4)^25*(1-b)^11 + 357743752362548724120364138048251065456918528*(b-3/4)^26*(1-b)^10 + 114187525884600566295555986224054872490115072*(b-3/4)^27*(1-b)^9 + 31402465474711800113557110298786666492461056*(b-3/4)^28*(1-b)^8 + 7350234194918468452194199340866507242471424*(b-3/4)^29*(1-b)^7 + 1441122034806072320634219927252388559192064*(b-3/4)^30*(1-b)^6 + 231674893752889971741807570881265979621376*(b-3/4)^31*(1-b)^5 + 29644092814205363877701977274841609273344*(b-3/4)^32*(1-b)^4 + 2890580846612086451596607967605374844928*(b-3/4)^33*(1-b)^3 + 200456696528740274142164534076702195712*(b-3/4)^34*(1-b)^2 + 8719898694105303563177216904328642560*(b-3/4)^35*(1-b) + 175950664266257504169780707537715200*(b-3/4)^36

set_option maxHeartbeats 8000000 in
lemma certA {b : ℝ} (h0 : 0 < b) (h1 : b ≤ 1/2) : (1:ℝ)/100 ≤ LbfSelse b := by
  have hQ4 : (0:ℝ) < 4*b^2 - 16*b + 17 := by nlinarith [sq_nonneg (2-b)]
  have h2mb : (0:ℝ) < 2-b := by linarith
  have h1pb : (0:ℝ) < 1+b := by linarith
  have h32b : (0:ℝ) < 3-2*b := by linarith
  have hQ : (0:ℝ) < QA b := by unfold QA; positivity
  have hkey : (LbfSelse b - 1/100) * QA b = certSA b := by
    unfold LbfSelse WPTfS S3f S1f QA certSA
    field_simp
    ring
  have hS : (0:ℝ) ≤ certSA b := by unfold certSA; positivity
  have hprod : (0:ℝ) ≤ (LbfSelse b - 1/100) * QA b := by rw [hkey]; exact hS
  have hnn : (0:ℝ) ≤ LbfSelse b - 1/100 := nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hQ
  linarith

set_option maxHeartbeats 8000000 in
lemma certB {b : ℝ} (h0 : 0 < b) (h1 : 1/2 ≤ b) (h2 : b ≤ 1) : (1:ℝ)/100 ≤ LbfSif b := by
  have hQ4 : (0:ℝ) < 4*b^2 - 16*b + 17 := by nlinarith [sq_nonneg (2-b)]
  have hb2 : (0:ℝ) < b^2 := by positivity
  have h2mb : (0:ℝ) < 2-b := by linarith
  have h1pb : (0:ℝ) < 1+b := by linarith
  have h32b : (0:ℝ) < 3-2*b := by linarith
  have hQ : (0:ℝ) < QB b := by unfold QB; positivity
  have hkey : (LbfSif b - 1/100) * QB b = certSB b := by
    unfold LbfSif WPTfS S3f S1f QB certSB
    field_simp
    ring
  have hS : (0:ℝ) ≤ certSB b := by unfold certSB; positivity
  have hprod : (0:ℝ) ≤ (LbfSif b - 1/100) * QB b := by rw [hkey]; exact hS
  have hnn : (0:ℝ) ≤ LbfSif b - 1/100 := nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hQ
  linarith

set_option maxHeartbeats 8000000 in
lemma certC {b : ℝ} (h0 : 0 < b) (h1 : b ≤ 1/4) : (C1f b - 4*b)/2 - 1 ≤ 4 * LbfSelse b := by
  have hQ4 : (0:ℝ) < 4*b^2 - 16*b + 17 := by nlinarith [sq_nonneg (2-b)]
  have hQ5 : (0:ℝ) < 2*b^2 - 6*b + 5 := by nlinarith [sq_nonneg (2*b-3)]
  have hQ6 : (0:ℝ) < 4*b^2 + 8*b + 5 := by nlinarith [sq_nonneg (2*b+2)]
  have h2mb : (0:ℝ) < 2-b := by linarith
  have h1pb : (0:ℝ) < 1+b := by linarith
  have h32b : (0:ℝ) < 3-2*b := by linarith
  have hQ : (0:ℝ) < QC b := by unfold QC; positivity
  have hkey : (4 * LbfSelse b - ((C1f b - 4*b)/2 - 1)) * QC b = certSC b := by
    unfold C1f WTStf LbfSelse WPTfS S3f S1f QC certSC
    field_simp
    ring
  have hS : (0:ℝ) ≤ certSC b := by unfold certSC; positivity
  have hprod : (0:ℝ) ≤ (4 * LbfSelse b - ((C1f b - 4*b)/2 - 1)) * QC b := by rw [hkey]; exact hS
  have hnn : (0:ℝ) ≤ 4 * LbfSelse b - ((C1f b - 4*b)/2 - 1) := nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hQ
  linarith

set_option maxHeartbeats 8000000 in
lemma certD {b : ℝ} (h0 : 0 < b) (h1 : 3/4 ≤ b) (h2 : b ≤ 1) : C1f b + 1/(4*b^2) - 4 ≤ 16 * LbfSif b := by
  have hQ4 : (0:ℝ) < 4*b^2 - 16*b + 17 := by nlinarith [sq_nonneg (2-b)]
  have hQ5 : (0:ℝ) < 2*b^2 - 6*b + 5 := by nlinarith [sq_nonneg (2*b-3)]
  have hQ6 : (0:ℝ) < 4*b^2 + 8*b + 5 := by nlinarith [sq_nonneg (2*b+2)]
  have hb2 : (0:ℝ) < b^2 := by positivity
  have h2mb : (0:ℝ) < 2-b := by linarith
  have h1pb : (0:ℝ) < 1+b := by linarith
  have h32b : (0:ℝ) < 3-2*b := by linarith
  have hQ : (0:ℝ) < QD b := by unfold QD; positivity
  have hkey : (16 * LbfSif b - (C1f b + 1/(4*b^2) - 4)) * QD b = certSD b := by
    unfold C1f WTStf LbfSif WPTfS S3f S1f QD certSD
    field_simp
    ring
  have hS : (0:ℝ) ≤ certSD b := by unfold certSD; positivity
  have hprod : (0:ℝ) ≤ (16 * LbfSif b - (C1f b + 1/(4*b^2) - 4)) * QD b := by rw [hkey]; exact hS
  have hnn : (0:ℝ) ≤ 16 * LbfSif b - (C1f b + 1/(4*b^2) - 4) := nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hQ
  linarith

set_option maxHeartbeats 8000000 in
theorem boxWindow_Lb_facts {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
  (let at8 : ℝ → ℝ := fun y => y - y^3/3 + y^5/5 - y^7/7 + y^9/9 - y^11/11 + y^13/13 - y^15/15;
   let A : ℝ := 3/2 - β;
   let B : ℝ := 1 + β;
   let C : ℝ := 2 - β;
   let D : ℝ := C^2 - β^2;
   let WPTlb : ℝ := (13/5)*(at8 ((1/2)/A) + at8 ((1/2)/B))
      + D/(2*C) * at8 ((1/2)/C)
      + D^2/8 * ((at8 ((1/2)/C) + C*(1/2)/(C^2+(1/2)^2))/(2*C^3))
      + D^3/16 * (3*at8 ((1/2)/C)/(8*C^5) + (1/2)*(5*C^2+3*(1/2)^2)/(8*C^4*(C^2+(1/2)^2)^2));
   let WTSt : ℝ := (13/5)*(A/((A^2+1/4)^2) + B/((B^2+1/4)^2))
      + D * (1/(2*((C^2+1/4)^2))) + D^2 * (1/(2*C^5)) + D^3 * (3/(8*C^7));
   let C1 : ℝ := WTSt + 1/(4*C^2);
   let Lb : ℝ := if 1/2 ≤ β then
       2*WPTlb - (3*(6931471808/10^10) - (1-β)^2 - (1-β)^4/2) - (6931471808/10^10) - 2
         - 1/(48*C^2) - 1/(48*β^2)
     else
       2*WPTlb - (2*(6931471808/10^10) - β/2) - (6931471808/10^10) - 1 - 1/(48*C^2)
         - 2*β*((6931471808/10^10)+13/12) - (1-2*β);
   (1/100 ≤ Lb) ∧
   (β ≤ 1/4 → (C1 - 4*β)/2 - Real.log 3 ≤ 4*Lb) ∧
   (3/4 ≤ β → C1 + 1/(4*β^2) - 4 ≤ 16*Lb)) := by
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
    exact Real.exp_one_lt_three.le
  change (1/100 ≤ Lbf β) ∧ (β ≤ 1/4 → (C1f β - 4*β)/2 - Real.log 3 ≤ 4*Lbf β)
    ∧ (3/4 ≤ β → C1f β + 1/(4*β^2) - 4 ≤ 16*Lbf β)
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : 1/2 ≤ β
    · have hc := certB hβ0 h hβ1.le
      have hs : LbfSif β ≤ Lbf β := by
        rw [show Lbf β = Lbfif β from by rw [Lbf, if_pos h]]
        exact LbfSif_le_Lbfif hβ0 hβ1
      linarith
    · have hlt : β < 1/2 := not_le.mp h
      have hle : β ≤ 1/2 := le_of_lt hlt
      have hc := certA hβ0 hle
      have hs : LbfSelse β ≤ Lbf β := by
        rw [show Lbf β = Lbfelse β from by rw [Lbf, if_neg h]]
        exact LbfSelse_le_Lbfelse hβ0 hβ1
      linarith
  · intro hle
    have hb2 : β < 1/2 := by linarith
    have hc := certC hβ0 hle
    have hs : LbfSelse β ≤ Lbf β := by
      rw [show Lbf β = Lbfelse β from by rw [Lbf, if_neg (not_le.mpr hb2)]]
      exact LbfSelse_le_Lbfelse hβ0 hβ1
    linarith
  · intro hge
    have hge' : 1/2 ≤ β := by linarith
    have hc := certD hβ0 hge hβ1.le
    have hs : LbfSif β ≤ Lbf β := by
      rw [show Lbf β = Lbfif β from by rw [Lbf, if_pos hge']]
      exact LbfSif_le_Lbfif hβ0 hβ1
    linarith

end Commons.Analysis.Integral