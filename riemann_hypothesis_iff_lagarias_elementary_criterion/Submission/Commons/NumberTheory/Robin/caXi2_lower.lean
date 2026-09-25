import Mathlib
import Submission.Commons.Analysis.Real.log_one_add_lower
import Submission.Commons.Analysis.Real.log_taylor3_upper
import Submission.Commons.Analysis.Log.log_sq_le_sqrt_of_ge_1530
import Submission.Commons.Analysis.Log.caXi2_lower_bracket_mono
import Submission.Commons.NumberTheory.Robin.caXi2_upper
import Submission.Commons.Analysis.Log.log_1530_bounds
import Submission.Commons.NumberTheory.Robin.caXi2_lower_A_ge
import Submission.Commons.NumberTheory.Robin.caXi2_lower_Dup_ge

namespace Commons.NumberTheory.Robin

set_option maxHeartbeats 16000000

/-! ### Auxiliary logarithm-series estimate -/

private lemma neg_log_one_sub_ge (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (u + u^2/2 + u^3/3 + u^4/4 + u^5/5 + u^6/6 : ℝ) ≤ -Real.log (1-u) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := u) (by rwa [abs_of_nonneg hu0])
  have hle := hs.summable.sum_le_tsum (Finset.range 6) (fun i hi => by positivity)
  rw [hs.tsum_eq] at hle
  have hlhs : ∑ i ∈ Finset.range 6, u^(i+1)/((i:ℝ)+1) = u + u^2/2 + u^3/3 + u^4/4 + u^5/5 + u^6/6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    ring
  rw [hlhs] at hle
  exact hle

/-! ### The numerical core estimates (verified by exact polynomial identities) -/

private lemma core_poly (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 13637/100000) :
    0 ≤ (((3852077475351989277861453534272236131472689931285104533345263312974254346687545447984493:ℝ)/298023223876953125000000000000000000000000000000000000000000000000000000000000000000000)*w^14 + ((-1246250326771456136009584493223372485400753067112351288238109822602562699917810379796607339:ℝ)/14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000)*w^13 + ((561504202773682876462067360424510685738486856718966290423982856013945906147367589069832140797:ℝ)/2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000)*w^12 + ((-147831418760617713973833912717081431457648541369062514394797481536584323353958483063691:ℝ)/596046447753906250000000000000000000000000000000000000000000000000000000000000000000)*w^11 + ((281925788053884201408170783619130529109997386519889599758836316489264736976999719:ℝ)/953674316406250000000000000000000000000000000000000000000000000000000000000000)*w^10 + ((-52211845338782417532469336874476252065465085072138211588932521230682588369:ℝ)/381469726562500000000000000000000000000000000000000000000000000000000000)*w^9 + ((107997471199221887719861046756345873927930102331130668738809288350557:ℝ)/1220703125000000000000000000000000000000000000000000000000000000000)*w^8 + ((80656671258006267754230584252710646590305329171320494910353:ℝ)/4882812500000000000000000000000000000000000000000000000000)*w^7 + ((-96546235534820837447715663787234896009614663472360981:ℝ)/7629394531250000000000000000000000000000000000000000)*w^6 + ((1876498307775255102903382757289265108371009717:ℝ)/1525878906250000000000000000000000000000000000)*w^5) := by
  rw [show (((3852077475351989277861453534272236131472689931285104533345263312974254346687545447984493:ℝ)/298023223876953125000000000000000000000000000000000000000000000000000000000000000000000)*w^14 + ((-1246250326771456136009584493223372485400753067112351288238109822602562699917810379796607339:ℝ)/14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000)*w^13 + ((561504202773682876462067360424510685738486856718966290423982856013945906147367589069832140797:ℝ)/2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000)*w^12 + ((-147831418760617713973833912717081431457648541369062514394797481536584323353958483063691:ℝ)/596046447753906250000000000000000000000000000000000000000000000000000000000000000000)*w^11 + ((281925788053884201408170783619130529109997386519889599758836316489264736976999719:ℝ)/953674316406250000000000000000000000000000000000000000000000000000000000000000)*w^10 + ((-52211845338782417532469336874476252065465085072138211588932521230682588369:ℝ)/381469726562500000000000000000000000000000000000000000000000000000000000)*w^9 + ((107997471199221887719861046756345873927930102331130668738809288350557:ℝ)/1220703125000000000000000000000000000000000000000000000000000000000)*w^8 + ((80656671258006267754230584252710646590305329171320494910353:ℝ)/4882812500000000000000000000000000000000000000000000000000)*w^7 + ((-96546235534820837447715663787234896009614663472360981:ℝ)/7629394531250000000000000000000000000000000000000000)*w^6 + ((1876498307775255102903382757289265108371009717:ℝ)/1525878906250000000000000000000000000000000000)*w^5) = (((0:ℝ)/1) * (w/(13637/100000:ℝ))^0 * (1 - w/(13637/100000:ℝ))^14 + ((0:ℝ)/1) * (w/(13637/100000:ℝ))^1 * (1 - w/(13637/100000:ℝ))^13 + ((0:ℝ)/1) * (w/(13637/100000:ℝ))^2 * (1 - w/(13637/100000:ℝ))^12 + ((0:ℝ)/1) * (w/(13637/100000:ℝ))^3 * (1 - w/(13637/100000:ℝ))^11 + ((0:ℝ)/1) * (w/(13637/100000:ℝ))^4 * (1 - w/(13637/100000:ℝ))^10 + ((884998184143396972371775060181367995419211731433225192587637546169:ℝ)/15258789062500000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^5 * (1 - w/(13637/100000:ℝ))^9 + ((3361553615275685405539429004930792055112233600346584776703184113978712944485571:ℝ)/7629394531250000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^6 * (1 - w/(13637/100000:ℝ))^8 + ((708671658903828662775362752553648306711901522613388597486819621994259577075934156279308349:ℝ)/488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^7 * (1 - w/(13637/100000:ℝ))^7 + ((33020987106691432758390342174168309683998464996310333543766158654229089966205732140950355572742892836797:ℝ)/12207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^8 * (1 - w/(13637/100000:ℝ))^6 + ((1188544915540247325500937595589910380427875869187673914602421222790234249449420285744949349919966628075327153702987:ℝ)/381469726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^9 * (1 - w/(13637/100000:ℝ))^5 + ((216108750831809618924786003013430743837238788982989860620001872568809141912992222711651437543111073415377896870733154517752431:ℝ)/95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^10 * (1 - w/(13637/100000:ℝ))^4 + ((6038943193026138992992886971778467451578310835384808308684701202872232468779900610025620531487351808141232882937390429878584095087649217:ℝ)/5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^11 * (1 - w/(13637/100000:ℝ))^3 + ((755462526816366359666045001824297815924992826077441051409207437461486572943505715714260306664409105858080494186502320733503557664207768904452614157:ℝ)/2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^12 * (1 - w/(13637/100000:ℝ))^2 + ((40313953117764718367923360308160298848097399009409708556193332210624900789825778592542852387503757145180728879278539540408625305561579899435200097217:ℝ)/1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^13 * (1 - w/(13637/100000:ℝ))^1 + ((114134371258302770886112795830436039444076495300518139876972646850070814122697823985573029128834399090076489114655228957225996833831173969825437515077:ℝ)/2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^14 * (1 - w/(13637/100000:ℝ))^0) from by ring]
  have h1 : (0:ℝ) ≤ 1 - w/(13637/100000:ℝ) := by
    rw [sub_nonneg, div_le_one (by norm_num : (0:ℝ) < 13637/100000)]
    exact hw1
  positivity

private lemma core_t5 (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 13637/100000) :
    0 ≤ (((-28116433053669401774201142087969316973251132193248957085415922521326756297656257:ℝ)/9094947017729282379150390625000000000000000000000000000000000000000000000000000)*w^11 + ((13171410675668700728439091147847194905525513179594855750699454404029445724746629911:ℝ)/909494701772928237915039062500000000000000000000000000000000000000000000000000000)*w^10 + ((-2313804529271921946396537100262843124768633272130246354392520801317519313783:ℝ)/291038304567337036132812500000000000000000000000000000000000000000000000000)*w^9 + ((-27203919233052722473866520177660122153478780058221455579585560201727003:ℝ)/1164153218269348144531250000000000000000000000000000000000000000000000)*w^8 + ((12328654605321720037597708735996514560425064602638673287384979447:ℝ)/931322574615478515625000000000000000000000000000000000000000000)*w^7 + ((-28458381377743071111239191296732387141836688317029740955191:ℝ)/745058059692382812500000000000000000000000000000000000000)*w^6 + ((9516052315833922099178849088011159667:ℝ)/15258789062500000000000000000000000000000)) := by
  rw [show (((-28116433053669401774201142087969316973251132193248957085415922521326756297656257:ℝ)/9094947017729282379150390625000000000000000000000000000000000000000000000000000)*w^11 + ((13171410675668700728439091147847194905525513179594855750699454404029445724746629911:ℝ)/909494701772928237915039062500000000000000000000000000000000000000000000000000000)*w^10 + ((-2313804529271921946396537100262843124768633272130246354392520801317519313783:ℝ)/291038304567337036132812500000000000000000000000000000000000000000000000000)*w^9 + ((-27203919233052722473866520177660122153478780058221455579585560201727003:ℝ)/1164153218269348144531250000000000000000000000000000000000000000000000)*w^8 + ((12328654605321720037597708735996514560425064602638673287384979447:ℝ)/931322574615478515625000000000000000000000000000000000000000000)*w^7 + ((-28458381377743071111239191296732387141836688317029740955191:ℝ)/745058059692382812500000000000000000000000000000000000000)*w^6 + ((9516052315833922099178849088011159667:ℝ)/15258789062500000000000000000000000000000)) = (((9516052315833922099178849088011159667:ℝ)/15258789062500000000000000000000000000000) * (w/(13637/100000:ℝ))^0 * (1 - w/(13637/100000:ℝ))^11 + ((104676575474173143090967339968122756337:ℝ)/15258789062500000000000000000000000000000) * (w/(13637/100000:ℝ))^1 * (1 - w/(13637/100000:ℝ))^10 + ((104676575474173143090967339968122756337:ℝ)/3051757812500000000000000000000000000000) * (w/(13637/100000:ℝ))^2 * (1 - w/(13637/100000:ℝ))^9 + ((314029726422519429272902019904368269011:ℝ)/3051757812500000000000000000000000000000) * (w/(13637/100000:ℝ))^3 * (1 - w/(13637/100000:ℝ))^8 + ((314029726422519429272902019904368269011:ℝ)/1525878906250000000000000000000000000000) * (w/(13637/100000:ℝ))^4 * (1 - w/(13637/100000:ℝ))^7 + ((2198208084957636004910314139330577883077:ℝ)/7629394531250000000000000000000000000000) * (w/(13637/100000:ℝ))^5 * (1 - w/(13637/100000:ℝ))^6 + ((214485727892711786497374343341268546511524577919512685827519455299849560157434359041681:ℝ)/745058059692382812500000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^6 * (1 - w/(13637/100000:ℝ))^5 + ((19053540720287162703266101632790934572086354522598653049803151620272674600224037567338894601275051:ℝ)/93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^7 * (1 - w/(13637/100000:ℝ))^4 + ((1169837952443717046797913507502097887945906405860627671154289198471177975979103873775262686067660082341300037:ℝ)/11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^8 * (1 - w/(13637/100000:ℝ))^3 + ((9285570038448011871869345454653598099607451635746052860337467126311818464749238435501025174221495078026065541209810509:ℝ)/291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^9 * (1 - w/(13637/100000:ℝ))^2 + ((515648706444039507026707692025240649263747600293794633370872315329151389013665467588497869808615094910808156329718824220780873439:ℝ)/90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^10 * (1 - w/(13637/100000:ℝ))^1 + ((35170326286736344904546192256880872419864777131669579494580630368518167692175243662153603000883550062449521888833591441096094512059:ℝ)/90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) * (w/(13637/100000:ℝ))^11 * (1 - w/(13637/100000:ℝ))^0) from by ring]
  have h1 : (0:ℝ) ≤ 1 - w/(13637/100000:ℝ) := by
    rw [sub_nonneg, div_le_one (by norm_num : (0:ℝ) < 13637/100000)]
    exact hw1
  positivity


/-! ### The core polynomial inequalities in "factored" (usable) form -/

/-- The truncated series lower bound `A_core` for `A = L/(2(1-β/L)²) - Dup`. -/
private noncomputable def Acore (w : ℝ) : ℝ :=
  3 * (34657359 / 10 ^ 8) ^ 2 * w / 2 + 2 * (34657359 / 10 ^ 8) ^ 3 * w ^ 2
    + 5 * (34657359 / 10 ^ 8) ^ 4 * w ^ 3 / 2 + 3 * (34657359 / 10 ^ 8) ^ 5 * w ^ 4
    + (34657359 / 10 ^ 8) * w + (34657359 / 10 ^ 8) ^ 2 * w ^ 2 / 2
    + (34657359 / 10 ^ 8) ^ 3 * w ^ 3 / 3 + (34657359 / 10 ^ 8) ^ 4 * w ^ 4 / 4

private lemma core_poly_f (w C r b : ℝ) (hC : C = 117252 / 10 ^ 5) (hr : r = 141422 / 10 ^ 5)
    (hb : b = 3465736 / 10 ^ 7) (hw0 : 0 < w) (hw1 : w ≤ 13637 / 100000) :
    0 ≤ 8 * (1 - b * w) ^ 2 * (r * (1 - b * w) + C ^ 2 * w ^ 2) ^ 2
          * (C ^ 4 * w ^ 4 * Acore w + C ^ 8 * w ^ 8 * (19823 / 10 ^ 4))
        - (200004 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 * (r * (1 - b * w) + C ^ 2 * w ^ 2)
        - C ^ 8 * w ^ 7 * r ^ 2 := by
  have key : 8 * (1 - b * w) ^ 2 * (r * (1 - b * w) + C ^ 2 * w ^ 2) ^ 2
          * (C ^ 4 * w ^ 4 * Acore w + C ^ 8 * w ^ 8 * (19823 / 10 ^ 4))
        - (200004 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 * (r * (1 - b * w) + C ^ 2 * w ^ 2)
        - C ^ 8 * w ^ 7 * r ^ 2
      = ((((3852077475351989277861453534272236131472689931285104533345263312974254346687545447984493:ℝ)/298023223876953125000000000000000000000000000000000000000000000000000000000000000000000)*w^14 + ((-1246250326771456136009584493223372485400753067112351288238109822602562699917810379796607339:ℝ)/14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000)*w^13 + ((561504202773682876462067360424510685738486856718966290423982856013945906147367589069832140797:ℝ)/2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000)*w^12 + ((-147831418760617713973833912717081431457648541369062514394797481536584323353958483063691:ℝ)/596046447753906250000000000000000000000000000000000000000000000000000000000000000000)*w^11 + ((281925788053884201408170783619130529109997386519889599758836316489264736976999719:ℝ)/953674316406250000000000000000000000000000000000000000000000000000000000000000)*w^10 + ((-52211845338782417532469336874476252065465085072138211588932521230682588369:ℝ)/381469726562500000000000000000000000000000000000000000000000000000000000)*w^9 + ((107997471199221887719861046756345873927930102331130668738809288350557:ℝ)/1220703125000000000000000000000000000000000000000000000000000000000)*w^8 + ((80656671258006267754230584252710646590305329171320494910353:ℝ)/4882812500000000000000000000000000000000000000000000000000)*w^7 + ((-96546235534820837447715663787234896009614663472360981:ℝ)/7629394531250000000000000000000000000000000000000000)*w^6 + ((1876498307775255102903382757289265108371009717:ℝ)/1525878906250000000000000000000000000000000000)*w^5)) := by
    rw [hC, hr, hb]
    unfold Acore
    ring
  rw [key]
  exact core_poly w hw0 hw1

private lemma core_t5_f (w C r b : ℝ) (hC : C = 117252 / 10 ^ 5) (hr : r = 141422 / 10 ^ 5)
    (hb : b = 3465736 / 10 ^ 7) (hw0 : 0 < w) (hw1 : w ≤ 13637 / 100000) :
    24 * (1 - b * w) ^ 2 * (r * (1 - b * w) + C ^ 2 * w ^ 2)
        * (C ^ 12 * w ^ 6 / 6 + C ^ 12 * w ^ 7 * b / 3) ≤ (12 / 10 ^ 5) * C ^ 6 * r ^ 2 := by
  have key : 24 * (1 - b * w) ^ 2 * (r * (1 - b * w) + C ^ 2 * w ^ 2)
        * (C ^ 12 * w ^ 6 / 6 + C ^ 12 * w ^ 7 * b / 3) - (12 / 10 ^ 5) * C ^ 6 * r ^ 2
        + ((((-28116433053669401774201142087969316973251132193248957085415922521326756297656257:ℝ)/9094947017729282379150390625000000000000000000000000000000000000000000000000000)*w^11 + ((13171410675668700728439091147847194905525513179594855750699454404029445724746629911:ℝ)/909494701772928237915039062500000000000000000000000000000000000000000000000000000)*w^10 + ((-2313804529271921946396537100262843124768633272130246354392520801317519313783:ℝ)/291038304567337036132812500000000000000000000000000000000000000000000000000)*w^9 + ((-27203919233052722473866520177660122153478780058221455579585560201727003:ℝ)/1164153218269348144531250000000000000000000000000000000000000000000000)*w^8 + ((12328654605321720037597708735996514560425064602638673287384979447:ℝ)/931322574615478515625000000000000000000000000000000000000000000)*w^7 + ((-28458381377743071111239191296732387141836688317029740955191:ℝ)/745058059692382812500000000000000000000000000000000000000)*w^6 + ((9516052315833922099178849088011159667:ℝ)/15258789062500000000000000000000000000000))) = 0 := by
    rw [hC, hr, hb]
    ring
  have h := core_t5 w hw0 hw1
  linarith [h, key]


/-! ### The main theorem -/

theorem caXi2_lower (ξ ξ2 : ℝ) (hξ : 1530 ≤ ξ) (hξ2 : 1 < ξ2)
    (hF : Real.log (1 + 1 / (ξ2 + ξ2 ^ 2)) / Real.log ξ2
        = Real.log (1 + 1 / ξ) / Real.log ξ) :
    Real.sqrt (2 * ξ) * (1 - Real.log 2 / (2 * Real.log ξ)) ≤ ξ2 := by
  have hξ1 : 1 < ξ := by linarith
  have hξpos : 0 < ξ := by linarith
  set L : ℝ := Real.log ξ with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hξ1
  have hL7330 : (7.3330 : ℝ) ≤ L := by
    rw [hLdef]
    exact le_trans Commons.Analysis.Log.log_1530_bounds.1 (Real.log_le_log (by norm_num) hξ)
  have hL733 : (7.333 : ℝ) ≤ L := by
    have h : (7.3330 : ℝ) = 7.333 := by norm_num
    linarith [hL7330, h]
  set β : ℝ := Real.log 2 / 2 with hβdef
  have hβpos : 0 < β := by rw [hβdef]; exact half_pos (Real.log_pos (by norm_num))
  have hβle : β ≤ 3465736 / 10 ^ 7 := by
    rw [hβdef]; have h := Real.log_two_lt_d9; norm_num at h ⊢; linarith
  have hβge : 34657359 / 10 ^ 8 ≤ β := by
    rw [hβdef]; have h := Real.log_two_gt_d9; norm_num at h ⊢; linarith
  have hβLtL : β < L := by linarith
  have hlog2 : Real.log 2 = 2 * β := by rw [hβdef]; ring
  set p : ℝ := 1 - β / L with hpdef
  have hppos : 0 < p := by rw [hpdef, sub_pos, div_lt_one hLpos]; exact hβLtL
  have hple1 : p ≤ 1 := by
    rw [hpdef]
    have h : 0 ≤ β / L := by positivity
    linarith
  have hpge : 1 - (3465736 / 10 ^ 7) / 7.333 ≤ p := by
    rw [hpdef, sub_le_sub_iff_left]
    rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 7.333)]
    nlinarith [hβle, hL733]
  set s : ℝ := 1 / Real.sqrt ξ with hsdef
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hs_mul : s * Real.sqrt ξ = 1 := by
    rw [hsdef, one_div, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hξpos))]
  have hs2 : s ^ 2 = 1 / ξ := by
    rw [hsdef, div_pow, one_pow, Real.sq_sqrt hξpos.le]
  set B : ℝ := Real.sqrt (2 * ξ) * p with hBdef
  have hBval : B = Real.sqrt 2 * p / s := by
    rw [hBdef, hsdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ξ]
    have hne : Real.sqrt ξ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hξpos)
    field_simp <;> ring_nf
  have hBpos : 0 < B := by rw [hBval]; positivity
  have hBgt1 : 1 < B := by
    have hsq2 : (1.4142135 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hξr : (39.1152 : ℝ) ≤ Real.sqrt ξ := by
      rw [Real.le_sqrt (by norm_num) hξpos.le]; nlinarith [hξ]
    have hmul : 1.4142135 * 39.1152 * (1 - (3465736 / 10 ^ 7) / 7.333)
        ≤ Real.sqrt 2 * Real.sqrt ξ * p := by
      have h3 : (0 : ℝ) ≤ 1 - (3465736 / 10 ^ 7) / 7.333 := by norm_num
      have h4 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have h5 : (0 : ℝ) ≤ Real.sqrt ξ := Real.sqrt_nonneg ξ
      calc 1.4142135 * 39.1152 * (1 - (3465736 / 10 ^ 7) / 7.333)
          ≤ Real.sqrt 2 * 39.1152 * (1 - (3465736 / 10 ^ 7) / 7.333) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq2 (by norm_num)) h3
        _ ≤ Real.sqrt 2 * Real.sqrt ξ * (1 - (3465736 / 10 ^ 7) / 7.333) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξr h4) h3
        _ ≤ Real.sqrt 2 * Real.sqrt ξ * p := mul_le_mul_of_nonneg_left hpge (mul_nonneg h4 h5)
    rw [hBdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ξ]
    linarith [hmul, (by norm_num : (1 : ℝ) < 1.4142135 * 39.1152 * (1 - (3465736 / 10 ^ 7) / 7.333))]
  have hlogB_eq : Real.log B = (L + 2 * β) / 2 + Real.log (1 - β / L) := by
    have h1 : 0 < Real.sqrt (2 * ξ) := Real.sqrt_pos.mpr (by linarith)
    rw [hBdef, Real.log_mul (ne_of_gt h1) (ne_of_gt hppos), hpdef,
        Real.log_sqrt (by linarith : (0 : ℝ) ≤ 2 * ξ),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hξpos), ← hLdef, hlog2]
    ring
  set Dup : ℝ := (L + 2 * β) / 2
      - (β / L + (β / L) ^ 2 / 2 + (β / L) ^ 3 / 3 + (β / L) ^ 4 / 4
          + (β / L) ^ 5 / 5 + (β / L) ^ 6 / 6) with hDupdef
  have hlogB_le : Real.log B ≤ Dup := by
    rw [hlogB_eq, hDupdef]
    have h := neg_log_one_sub_ge (β / L) (by positivity) (by rw [div_lt_one hLpos]; exact hβLtL)
    linarith
  have hDup_ge : 19823 / 5000 ≤ Dup := by
    rw [hDupdef]; exact caXi2_lower_Dup_ge L β hL733 hβge hβle
  have hDup0 : 0 ≤ Dup := by linarith [hDup_ge]
  have hDup_le_b : Dup ≤ (L + 2 * (3465736 / 10 ^ 7)) / 2 := by
    rw [hDupdef]
    have hφ : 0 ≤ β / L + (β / L) ^ 2 / 2 + (β / L) ^ 3 / 3 + (β / L) ^ 4 / 4
        + (β / L) ^ 5 / 5 + (β / L) ^ 6 / 6 := by positivity
    linarith [hβle, hφ]
  set w : ℝ := 1 / L with hwdef
  have hwpos : 0 < w := by rw [hwdef]; positivity
  have hLw : L * w = 1 := by rw [hwdef]; field_simp
  have hL_eq : L = 1 / w := by rw [eq_div_iff (ne_of_gt hwpos)]; exact hLw
  have hwle : w ≤ 13637 / 100000 := by
    rw [hwdef, div_le_iff₀ hLpos]; nlinarith [hL733]
  set C : ℝ := 117252 / 10 ^ 5 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; norm_num
  set r : ℝ := 141422 / 10 ^ 5 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; norm_num
  have hr2 : (2 : ℝ) ≤ r ^ 2 := by rw [hrdef]; norm_num
  set pc : ℝ := 1 - (3465736 / 10 ^ 7) * w with hpcdef
  have hpcpos : 0 < pc := by
    rw [hpcdef]
    have h : (3465736 / 10 ^ 7) * w ≤ (3465736 / 10 ^ 7) * (13637 / 100000) :=
      mul_le_mul_of_nonneg_left hwle (by norm_num)
    linarith only [h]
  have hpc_le_p : pc ≤ p := by
    rw [hpcdef, hpdef, hwdef]
    have h1 : β / L ≤ (3465736 / 10 ^ 7) / L := div_le_div_of_nonneg_right hβle hLpos.le
    have h2 : (3465736 / 10 ^ 7) * (1 / L) = (3465736 / 10 ^ 7) / L := by ring
    linarith
  set D : ℝ := r * pc + C ^ 2 * w ^ 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set e : ℝ := C ^ 2 * w ^ 2 / (r * pc) with hedef
  have hDe : D = r * pc * (1 + e) := by
    rw [hDdef, hedef]; field_simp <;> ring_nf
  set smax : ℝ := C ^ 2 * w ^ 2 with hsmaxdef
  have hsmaxpos : 0 < smax := by rw [hsmaxdef]; positivity
  have hsmax2pos : 0 < smax ^ 2 := by positivity
  set etamax : ℝ := Real.sqrt 2 * smax / (2 * p) with hetamaxdef
  have hetamaxpos : 0 < etamax := by rw [hetamaxdef]; positivity
  have h1etamax : (0 : ℝ) < 1 + etamax := by linarith
  set eta : ℝ := Real.sqrt 2 * s / (2 * p) with hetadef
  have hetapos : 0 < eta := by rw [hetadef]; positivity
  have h1eta : (0 : ℝ) < 1 + eta := by linarith
  have hss : s ≤ smax := by
    have hLsq : L ^ 2 ≤ 1.37478 * Real.sqrt ξ := by
      rw [hLdef]; exact Commons.Analysis.Log.log_sq_le_sqrt_of_ge_1530 ξ hξ
    have h1 : s * L ^ 2 ≤ 1.37478 := by
      have hm : s * L ^ 2 ≤ s * (1.37478 * Real.sqrt ξ) :=
        mul_le_mul_of_nonneg_left hLsq (le_of_lt hspos)
      have h2 : s * (1.37478 * Real.sqrt ξ) = 1.37478 * (s * Real.sqrt ξ) := by ring
      rw [h2, hs_mul, mul_one] at hm
      exact hm
    have h2 : s * L ^ 2 ≤ C ^ 2 := by
      have hC2 : (1.37478 : ℝ) ≤ C ^ 2 := by rw [hCdef]; norm_num
      exact le_trans h1 hC2
    have hw2 : w ^ 2 = 1 / L ^ 2 := by rw [hL_eq]; field_simp <;> ring
    have heq : C ^ 2 * w ^ 2 = C ^ 2 / L ^ 2 := by rw [hw2]; ring
    rw [hsmaxdef, heq, le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 2)]
    exact h2
  have hsmaxL2 : smax * L ^ 2 ≤ (117252 / 10 ^ 5) ^ 2 := by
    have h2 : C ^ 2 * w ^ 2 * L ^ 2 = C ^ 2 := by
      rw [show C ^ 2 * w ^ 2 * L ^ 2 = C ^ 2 * (w * L) ^ 2 by ring]
      rw [show w * L = 1 by rw [mul_comm]; exact hLw]
      ring
    rw [hsmaxdef, h2, hCdef]
  have heub : etamax ≤ (141422 / 10 ^ 5) * ((117252 / 10 ^ 5) ^ 2)
      / (2 * (1 - (3465736 / 10 ^ 7) / 7.333) * (7.333) ^ 2) := by
    have hsq2r : Real.sqrt 2 ≤ r := by
      rw [hrdef]; rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hL2ge : (7.333 : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith [hL733]
    have hkey : Real.sqrt 2 * (1 - (3465736 / 10 ^ 7) / 7.333) * (7.333) ^ 2
        ≤ r * p * L ^ 2 := by
      have h3 : (0 : ℝ) ≤ 1 - (3465736 / 10 ^ 7) / 7.333 := by norm_num
      have sp1 : Real.sqrt 2 * (1 - (3465736 / 10 ^ 7) / 7.333) * (7.333) ^ 2
          ≤ r * (1 - (3465736 / 10 ^ 7) / 7.333) * (7.333) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq2r h3) (by norm_num)
      have sp2 : r * (1 - (3465736 / 10 ^ 7) / 7.333) * (7.333) ^ 2
          ≤ r * p * (7.333) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpge (le_of_lt hrpos)) (by norm_num)
      have sp3 : r * p * (7.333) ^ 2 ≤ r * p * L ^ 2 :=
        mul_le_mul_of_nonneg_left hL2ge (mul_nonneg (le_of_lt hrpos) (le_of_lt hppos))
      linarith [sp1, sp2, sp3]
    have hL2inv : L ^ 2 * (1 / L ^ 2) = 1 := by field_simp
    rw [hetamaxdef, hsmaxdef]
    have hw2 : w ^ 2 = 1 / L ^ 2 := by rw [hL_eq]; field_simp <;> ring
    rw [hw2, hCdef]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * p)
        (by positivity : (0 : ℝ) < 2 * (1 - (3465736 / 10 ^ 7) / 7.333) * (7.333) ^ 2)]
    have hk := mul_le_mul_of_nonneg_right hkey
      (by positivity : (0 : ℝ) ≤ 2 * (117252 / 10 ^ 5) ^ 2 * (1 / L ^ 2))
    nlinarith [hk, hL2inv]
  have hGB : B ^ 2 + B = 2 * p ^ 2 * (1 + eta) / s ^ 2 := by
    rw [hetadef, hBval]
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hpne : p ≠ 0 := ne_of_gt hppos
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  set wq : ℝ := 1 / (B ^ 2 + B) with hwqdef
  have hwq : wq = s ^ 2 / (2 * p ^ 2 * (1 + eta)) := by
    rw [hwqdef, hGB, one_div_div]
  have hwqnn : 0 ≤ wq := by rw [hwqdef]; positivity
  have hwqle : wq ≤ 1 / 2 := by
    rw [hwqdef, div_le_iff₀ (by positivity : (0 : ℝ) < B ^ 2 + B)]
    nlinarith [hBgt1]
  set brmax : ℝ := L / (2 * p ^ 2) - Dup
      - smax * L * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
      - smax ^ 2 * L / (8 * p ^ 4 * (1 + etamax) ^ 2) + smax ^ 2 * Dup / 2
      - smax ^ 4 * Dup / 3 with hbrmaxdef
  set br : ℝ := L / (2 * p ^ 2) - Dup
      - s * L * Real.sqrt 2 / (4 * p ^ 3 * (1 + eta))
      - s ^ 2 * L / (8 * p ^ 4 * (1 + eta) ^ 2) + s ^ 2 * Dup / 2
      - s ^ 4 * Dup / 3 with hbrdef
  have hS4 : pc ^ 2 * (1 + e) ≤ p ^ 2 * (1 + etamax) := by
    rw [hedef, hetamaxdef, hsmaxdef]
    have h1 : pc ^ 2 * (1 + C ^ 2 * w ^ 2 / (r * pc)) = pc ^ 2 + C ^ 2 * w ^ 2 * pc / r := by
      field_simp <;> ring_nf
    have h2 : p ^ 2 * (1 + Real.sqrt 2 * (C ^ 2 * w ^ 2) / (2 * p))
        = p ^ 2 + Real.sqrt 2 * C ^ 2 * w ^ 2 * p / 2 := by
      field_simp <;> ring_nf
    rw [h1, h2]
    have hsq2r : (2 : ℝ) ≤ Real.sqrt 2 * r := by
      have hsq : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hsq, hr2, mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt hrpos)]
    have h1r : 1 / r ≤ Real.sqrt 2 / 2 := by
      rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 2)]
      linarith [hsq2r]
    have hpr : pc / r ≤ Real.sqrt 2 * p / 2 := by
      have h3 : pc / r ≤ p / r := by
        rw [div_le_div_iff₀ hrpos hrpos]; nlinarith [hpc_le_p, le_of_lt hrpos]
      have h4 : p / r ≤ Real.sqrt 2 * p / 2 := by
        calc p / r = p * (1 / r) := by ring
          _ ≤ p * (Real.sqrt 2 / 2) := mul_le_mul_of_nonneg_left h1r (le_of_lt hppos)
          _ = Real.sqrt 2 * p / 2 := by ring
      linarith
    have hpc2 : pc ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (le_of_lt hpcpos) hpc_le_p 2
    have h5 : C ^ 2 * w ^ 2 * pc / r ≤ Real.sqrt 2 * C ^ 2 * w ^ 2 * p / 2 := by
      calc C ^ 2 * w ^ 2 * pc / r = C ^ 2 * w ^ 2 * (pc / r) := by ring
        _ ≤ C ^ 2 * w ^ 2 * (Real.sqrt 2 * p / 2) := mul_le_mul_of_nonneg_left hpr (by positivity)
        _ = Real.sqrt 2 * C ^ 2 * w ^ 2 * p / 2 := by ring
    linarith [hpc2, h5]
  have hS : Real.sqrt 2 * pc ^ 3 * (1 + e) ≤ r * p ^ 3 * (1 + etamax) := by
    rw [hedef, hetamaxdef, hsmaxdef]
    have h1 : Real.sqrt 2 * pc ^ 3 * (1 + C ^ 2 * w ^ 2 / (r * pc))
        = Real.sqrt 2 * pc ^ 3 + Real.sqrt 2 * C ^ 2 * w ^ 2 * pc ^ 2 / r := by
      field_simp <;> ring_nf
    have h2 : r * p ^ 3 * (1 + Real.sqrt 2 * (C ^ 2 * w ^ 2) / (2 * p))
        = r * p ^ 3 + Real.sqrt 2 * C ^ 2 * w ^ 2 * r * p ^ 2 / 2 := by
      field_simp <;> ring_nf
    rw [h1, h2]
    have hpc3 : pc ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (le_of_lt hpcpos) hpc_le_p 3
    have hpc2 : pc ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (le_of_lt hpcpos) hpc_le_p 2
    have hA : Real.sqrt 2 * pc ^ 3 ≤ Real.sqrt 2 * p ^ 3 :=
      mul_le_mul_of_nonneg_left hpc3 (Real.sqrt_nonneg 2)
    have hB : Real.sqrt 2 * C ^ 2 * w ^ 2 * pc ^ 2 / r
        ≤ Real.sqrt 2 * C ^ 2 * w ^ 2 * p ^ 2 / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpc2 (by positivity)) (le_of_lt hrpos)
    have hCb : Real.sqrt 2 * C ^ 2 * w ^ 2 * p ^ 2 / r
        - Real.sqrt 2 * C ^ 2 * w ^ 2 * r * p ^ 2 / 2 ≤ 0 := by
      have hfac : Real.sqrt 2 * C ^ 2 * w ^ 2 * p ^ 2 / r
            - Real.sqrt 2 * C ^ 2 * w ^ 2 * r * p ^ 2 / 2
          = (Real.sqrt 2 * C ^ 2 * w ^ 2 * p ^ 2 / r) * (1 - r ^ 2 / 2) := by
        field_simp <;> ring_nf
      rw [hfac]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hr2])
    have hD : Real.sqrt 2 * p ^ 3 - r * p ^ 3 ≤ 0 := by
      have h2r : Real.sqrt 2 ≤ r := by
        rw [hrdef]; rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have h3 : p ^ 3 * (Real.sqrt 2 - r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt hppos) 3) (by linarith)
      linarith [h3]
    calc Real.sqrt 2 * pc ^ 3 + Real.sqrt 2 * C ^ 2 * w ^ 2 * pc ^ 2 / r
        ≤ Real.sqrt 2 * p ^ 3 + Real.sqrt 2 * C ^ 2 * w ^ 2 * p ^ 2 / r := add_le_add hA hB
      _ ≤ r * p ^ 3 + Real.sqrt 2 * C ^ 2 * w ^ 2 * r * p ^ 2 / 2 :=
            add_le_add (sub_nonpos.mp hD) (sub_nonpos.mp hCb)
  have hT1 : 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax)))
      ≤ 2 * C ^ 6 * w ^ 5 * r ^ 2 * D := by
    have hkey : Real.sqrt 2 * pc ^ 2 * D ≤ r ^ 2 * p ^ 3 * (1 + etamax) := by
      have he : Real.sqrt 2 * pc ^ 2 * D = r * (Real.sqrt 2 * pc ^ 3 * (1 + e)) := by
        rw [hDe]; ring
      rw [he]
      calc r * (Real.sqrt 2 * pc ^ 3 * (1 + e))
          ≤ r * (r * p ^ 3 * (1 + etamax)) := mul_le_mul_of_nonneg_left hS (le_of_lt hrpos)
        _ = r ^ 2 * p ^ 3 * (1 + etamax) := by ring
    have hgoal : Real.sqrt 2 * pc ^ 2 * D ^ 2 ≤ r ^ 2 * p ^ 3 * (1 + etamax) * D := by
      calc Real.sqrt 2 * pc ^ 2 * D ^ 2 = (Real.sqrt 2 * pc ^ 2 * D) * D := by ring
        _ ≤ (r ^ 2 * p ^ 3 * (1 + etamax)) * D := mul_le_mul_of_nonneg_right hkey (le_of_lt hDpos)
        _ = r ^ 2 * p ^ 3 * (1 + etamax) * D := by ring
    have hpos : (0 : ℝ) < 4 * p ^ 3 * (1 + etamax) := by positivity
    rw [show 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax)))
        = 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2) / (4 * p ^ 3 * (1 + etamax)) by
          rw [← mul_div_assoc]]
    rw [div_le_iff₀ hpos]
    have h8 : 8 * C ^ 6 * w ^ 5 * (Real.sqrt 2 * pc ^ 2 * D ^ 2)
        ≤ 8 * C ^ 6 * w ^ 5 * (r ^ 2 * p ^ 3 * (1 + etamax) * D) :=
      mul_le_mul_of_nonneg_left hgoal (by positivity)
    linarith [h8]
  have hT2 : 8 * pc ^ 2 * D ^ 2 * (C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2))
      ≤ C ^ 8 * w ^ 7 * r ^ 2 := by
    have hkey : pc ^ 2 * D ^ 2 ≤ r ^ 2 * p ^ 4 * (1 + etamax) ^ 2 := by
      have he : pc ^ 2 * D ^ 2 = (r * (pc ^ 2 * (1 + e))) ^ 2 := by rw [hDe]; ring
      rw [he]
      have h3 : (pc ^ 2 * (1 + e)) ^ 2 ≤ (p ^ 2 * (1 + etamax)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hS4 2
      calc (r * (pc ^ 2 * (1 + e))) ^ 2 = r ^ 2 * (pc ^ 2 * (1 + e)) ^ 2 := by ring
        _ ≤ r ^ 2 * (p ^ 2 * (1 + etamax)) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = r ^ 2 * p ^ 4 * (1 + etamax) ^ 2 := by ring
    have hpos : (0 : ℝ) < 8 * p ^ 4 * (1 + etamax) ^ 2 := by positivity
    rw [show 8 * pc ^ 2 * D ^ 2 * (C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2))
        = 8 * pc ^ 2 * D ^ 2 * (C ^ 8 * w ^ 7) / (8 * p ^ 4 * (1 + etamax) ^ 2) by
          rw [← mul_div_assoc]]
    rw [div_le_iff₀ hpos]
    have h8 : C ^ 8 * w ^ 7 * (pc ^ 2 * D ^ 2) ≤ C ^ 8 * w ^ 7 * (r ^ 2 * p ^ 4 * (1 + etamax) ^ 2) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith [h8]
  have hcore5 : 4 * pc ^ 2 * D * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w)
      ≤ (12 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 := by
    have h5 := core_t5_f w C r (3465736 / 10 ^ 7) hCdef hrdef rfl hwpos hwle
    rw [← hpcdef, ← hDdef] at h5
    have h3 : 24 * pc ^ 2 * D * (C ^ 12 * w ^ 6 / 6 + C ^ 12 * w ^ 7 * (3465736 / 10 ^ 7) / 3)
        = 4 * pc ^ 2 * D * C ^ 12 * w ^ 6 * (1 + 2 * (3465736 / 10 ^ 7) * w) := by ring
    rw [h3] at h5
    have h4 := mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ w ^ 5)
    have e1 : 4 * pc ^ 2 * D * C ^ 12 * w ^ 6 * (1 + 2 * (3465736 / 10 ^ 7) * w) * w ^ 5
        = 4 * pc ^ 2 * D * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w) := by ring
    have e2 : (12 / 10 ^ 5) * C ^ 6 * r ^ 2 * w ^ 5 = (12 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 := by ring
    rw [e1, e2] at h4
    exact h4
  have hT5 : 8 * pc ^ 2 * D ^ 2 * (C ^ 12 * w ^ 12 * Dup / 3)
      ≤ (4 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 * D := by
    have hb : (L + 2 * (3465736 / 10 ^ 7)) / 2 = (1 + 2 * (3465736 / 10 ^ 7) * w) / (2 * w) := by
      rw [hL_eq]; field_simp
    have hDup' : Dup ≤ (1 + 2 * (3465736 / 10 ^ 7) * w) / (2 * w) := by
      have h := hDup_le_b
      rw [hb] at h
      exact h
    have h1 : 8 * pc ^ 2 * D ^ 2 * (C ^ 12 * w ^ 12 * Dup / 3)
        ≤ (4 / 3) * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w) := by
      have h := hDup'
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * w)] at h
      have h4 : 0 < 4 * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11 := by positivity
      have h3 := (mul_le_mul_iff_of_pos_left h4).mp
        (mul_le_mul_of_nonneg_left h (le_of_lt h4))
      have h3' : 2 * w * Dup ≤ 1 + 2 * (3465736 / 10 ^ 7) * w := by
        simpa only [mul_comm] using h3
      calc 8 * pc ^ 2 * D ^ 2 * (C ^ 12 * w ^ 12 * Dup / 3)
          = (4 * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11 / 3) * (2 * w * Dup) := by ring
        _ ≤ (4 * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11 / 3)
              * (1 + 2 * (3465736 / 10 ^ 7) * w) :=
              mul_le_mul_of_nonneg_left h3' (by positivity)
        _ = (4 / 3) * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11
              * (1 + 2 * (3465736 / 10 ^ 7) * w) := by ring
    have h2 : (4 / 3) * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w)
        = (D / 3) * (4 * pc ^ 2 * D * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w)) := by ring
    calc 8 * pc ^ 2 * D ^ 2 * (C ^ 12 * w ^ 12 * Dup / 3)
        ≤ (4 / 3) * pc ^ 2 * D ^ 2 * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w) := h1
      _ = (D / 3) * (4 * pc ^ 2 * D * C ^ 12 * w ^ 11 * (1 + 2 * (3465736 / 10 ^ 7) * w)) := h2
      _ ≤ (D / 3) * ((12 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2) :=
            mul_le_mul_of_nonneg_left hcore5 (by positivity)
      _ = (4 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 * D := by ring
  have hcore : 0 ≤ 8 * pc ^ 2 * D ^ 2 * (C ^ 4 * w ^ 4 * Acore w + C ^ 8 * w ^ 8 * (19823 / 10 ^ 4))
        - (200004 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 * D - C ^ 8 * w ^ 7 * r ^ 2 := by
    have h := core_poly_f w C r (3465736 / 10 ^ 7) hCdef hrdef rfl hwpos hwle
    rw [← hpcdef, ← hDdef] at h
    exact h
  have hAsum : 8 * pc ^ 2 * D ^ 2 * (C ^ 4 * w ^ 4 * Acore w + C ^ 8 * w ^ 8 * (19823 / 10 ^ 4))
      ≤ 8 * pc ^ 2 * D ^ 2
          * (C ^ 4 * w ^ 4 * (L / (2 * p ^ 2) - Dup) + C ^ 8 * w ^ 8 * (Dup / 2)) := by
    have hconv : Acore w = 3 * (34657359 / 10 ^ 8) ^ 2 / (2 * L)
        + 2 * (34657359 / 10 ^ 8) ^ 3 / L ^ 2 + 5 * (34657359 / 10 ^ 8) ^ 4 / (2 * L ^ 3)
        + 3 * (34657359 / 10 ^ 8) ^ 5 / L ^ 4 + (34657359 / 10 ^ 8) / L
        + (34657359 / 10 ^ 8) ^ 2 / (2 * L ^ 2) + (34657359 / 10 ^ 8) ^ 3 / (3 * L ^ 3)
        + (34657359 / 10 ^ 8) ^ 4 / (4 * L ^ 4) := by
      unfold Acore
      rw [hwdef]
      ring
    have hA1 : Acore w ≤ L / (2 * p ^ 2) - Dup := by
      rw [hconv, hDupdef, hpdef]
      have h := caXi2_lower_A_ge L β (34657359 / 10 ^ 8) hLpos hβLtL (by norm_num) hβge
      linarith [h]
    have hA2 : (19823 / 10 ^ 4 : ℝ) ≤ Dup / 2 := by linarith [hDup_ge]
    have h1 : C ^ 4 * w ^ 4 * Acore w ≤ C ^ 4 * w ^ 4 * (L / (2 * p ^ 2) - Dup) :=
      mul_le_mul_of_nonneg_left hA1 (by positivity)
    have h2 : C ^ 8 * w ^ 8 * (19823 / 10 ^ 4) ≤ C ^ 8 * w ^ 8 * (Dup / 2) :=
      mul_le_mul_of_nonneg_left hA2 (by positivity)
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
  have hsum3 : 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
        + C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2) + C ^ 12 * w ^ 12 * Dup / 3)
      ≤ (200004 / 10 ^ 5) * C ^ 6 * w ^ 5 * r ^ 2 * D + C ^ 8 * w ^ 7 * r ^ 2 := by
    have he : 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
          + C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2) + C ^ 12 * w ^ 12 * Dup / 3)
        = 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax)))
          + 8 * pc ^ 2 * D ^ 2 * (C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2))
          + 8 * pc ^ 2 * D ^ 2 * (C ^ 12 * w ^ 12 * Dup / 3) := by ring
    rw [he]
    linarith [hT1, hT2, hT5]
  have hbrmax_nonneg : 0 ≤ brmax := by
    have hId : smax ^ 2 * brmax
        = C ^ 4 * w ^ 4 * (L / (2 * p ^ 2) - Dup) + C ^ 8 * w ^ 8 * Dup / 2
          - C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
          - C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2) - C ^ 12 * w ^ 12 * Dup / 3 := by
      rw [hbrmaxdef, hsmaxdef, hL_eq]
      field_simp <;> ring
    have hsc : 0 ≤ C ^ 4 * w ^ 4 * (L / (2 * p ^ 2) - Dup) + C ^ 8 * w ^ 8 * Dup / 2
        - C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
        - C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2) - C ^ 12 * w ^ 12 * Dup / 3 := by
      have h1 : 8 * pc ^ 2 * D ^ 2 * (C ^ 6 * w ^ 5 * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
            + C ^ 8 * w ^ 7 / (8 * p ^ 4 * (1 + etamax) ^ 2) + C ^ 12 * w ^ 12 * Dup / 3)
          ≤ 8 * pc ^ 2 * D ^ 2
              * (C ^ 4 * w ^ 4 * (L / (2 * p ^ 2) - Dup) + C ^ 8 * w ^ 8 * Dup / 2) := by
        linarith [hcore, hAsum, hsum3]
      have h2 := (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 8 * pc ^ 2 * D ^ 2)).mp h1
      linarith [h2]
    have hsc2 : 0 ≤ smax ^ 2 * brmax := by rw [hId]; exact hsc
    exact (mul_nonneg_iff_of_pos_left hsmax2pos).mp hsc2
  have hmono : brmax ≤ br := by
    have hchild := Commons.Analysis.Log.caXi2_lower_bracket_mono L p s smax eta etamax Dup
      hL733 hppos hple1 hspos hss hetadef hetamaxdef hDup_le_b hDup0 hsmaxL2 heub
    have hterm : s ^ 2 / (1 + eta) ^ 2 ≤ smax ^ 2 / (1 + etamax) ^ 2 := by
      have hkey : s * (1 + etamax) ≤ smax * (1 + eta) := by
        rw [hetadef, hetamaxdef]
        have h1 : s * (1 + Real.sqrt 2 * smax / (2 * p))
            = s + s * (Real.sqrt 2 * smax / (2 * p)) := by ring
        have h2 : smax * (1 + Real.sqrt 2 * s / (2 * p))
            = smax + smax * (Real.sqrt 2 * s / (2 * p)) := by ring
        rw [h1, h2]
        have heq : s * (Real.sqrt 2 * smax / (2 * p))
            = smax * (Real.sqrt 2 * s / (2 * p)) := by ring
        linarith [hss, heq]
      have h3 : 0 ≤ s * (1 + etamax) := by positivity
      have h5 := pow_le_pow_left₀ h3 hkey 2
      rw [mul_pow, mul_pow] at h5
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + eta) ^ 2)
        (by positivity : (0 : ℝ) < (1 + etamax) ^ 2)]
      exact h5
    have hdiff : br - brmax
        = (smax * L * Real.sqrt 2 / (4 * p ^ 3 * (1 + etamax))
            - s * L * Real.sqrt 2 / (4 * p ^ 3 * (1 + eta)))
          + L / (8 * p ^ 4) * (smax ^ 2 / (1 + etamax) ^ 2 - s ^ 2 / (1 + eta) ^ 2)
          - ((smax ^ 2 - s ^ 2) * Dup / 2 - (smax ^ 4 - s ^ 4) * Dup / 3) := by
      rw [hbrmaxdef, hbrdef]
      field_simp
      ring
    have hnn : 0 ≤ L / (8 * p ^ 4) * (smax ^ 2 / (1 + etamax) ^ 2 - s ^ 2 / (1 + eta) ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hterm)
    linarith [hchild, hnn, hdiff]
  have hbr_nonneg : 0 ≤ br := le_trans hbrmax_nonneg hmono
  have hid : L * (wq - wq ^ 2 / 2) - (s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3) * Dup = s ^ 2 * br := by
    rw [hbrdef, hwq, hetadef]
    have hsne : s ≠ 0 := ne_of_gt hspos
    field_simp
    ring
  have hDelta : 0 ≤ L * (wq - wq ^ 2 / 2) - (s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3) * Dup := by
    rw [hid]
    exact mul_nonneg (sq_nonneg s) hbr_nonneg
  have hQnn : 0 ≤ s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3 := by
    have hs2le1 : s ^ 2 ≤ 1 := by
      rw [hs2, div_le_one hξpos]; linarith
    have hfac : s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3 = s ^ 2 * (1 - s ^ 2 / 2 + s ^ 4 / 3) := by ring
    rw [hfac]
    refine mul_nonneg (sq_nonneg s) ?_
    have h1 : 0 ≤ 1 - s ^ 2 / 2 := by linarith only [hs2le1]
    have h2 : 0 ≤ s ^ 4 / 3 := by positivity
    linarith only [h1, h2]
  have hQlog : Real.log (1 + 1 / ξ) ≤ s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3 := by
    have hneg : (-1 : ℝ) < 1 / ξ := by
      have h : (0 : ℝ) < 1 / ξ := by positivity
      linarith
    have h := Commons.Analysis.Real.log_one_add_le_cubic (x := 1 / ξ) hneg
    have hrw : (1 / ξ) - (1 / ξ) ^ 2 / 2 + (1 / ξ) ^ 3 / 3 = s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3 := by
      rw [hs2.symm]; ring
    rw [hrw] at h
    exact h
  have hlogwq : wq - wq ^ 2 / 2 ≤ Real.log (1 + wq) :=
    Commons.Analysis.Real.log_one_add_lower (u₀ := 1 / 2) (by norm_num) hwqnn hwqle
  have hmain : Real.log (1 + 1 / ξ) / L ≤ Real.log (1 + 1 / (B + B ^ 2)) / Real.log B := by
    rw [show B + B ^ 2 = B ^ 2 + B by ring]
    have hlogBpos : 0 < Real.log B := Real.log_pos hBgt1
    have h1 : L * (wq - wq ^ 2 / 2) ≤ L * Real.log (1 + wq) :=
      mul_le_mul_of_nonneg_left hlogwq (le_of_lt hLpos)
    rw [hwqdef] at h1
    have h2 : (s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3) * Dup ≤ L * (1 / (B ^ 2 + B) - (1 / (B ^ 2 + B)) ^ 2 / 2) := by
      have h := hDelta
      rw [hwqdef] at h
      linarith [h]
    have h3 : Real.log (1 + 1 / ξ) * Real.log B ≤ (s ^ 2 - s ^ 4 / 2 + s ^ 6 / 3) * Dup :=
      mul_le_mul hQlog hlogB_le (le_of_lt hlogBpos) hQnn
    rw [div_le_div_iff₀ hLpos hlogBpos]
    linarith [h1, h2, h3]
  have hgoal_eq : Real.sqrt (2 * ξ) * (1 - Real.log 2 / (2 * Real.log ξ)) = B := by
    rw [hBdef, hpdef, hβdef, ← hLdef]
    ring
  rw [hgoal_eq]
  by_contra hcon
  rw [not_le] at hcon
  have hc := caXi2_upper_f2_strict hξ2 hcon
  rw [hF] at hc
  exact absurd hc (not_lt.mpr hmain)

end Commons.NumberTheory.Robin
