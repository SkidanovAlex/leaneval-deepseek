import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralTwo_core_corrected

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section
open scoped BigOperators Nat
open Filter Topology
open Polynomial

namespace Commons.Analysis.Summation
namespace CdtTwentyFourCore

/-! ## The clearing factor and the decomposition coefficients -/

def Lc : ℤ := 1543671433629959940367556695200

def cA : ℕ → ℤ := fun j => if j = 25 then (6466329416153451564626421985491438121504800 : ℤ) else if j = 26 then (-185329311630459407630664888020165022915480000 : ℤ) else if j = 28 then (24246018365442605782658062940556972183323040000 : ℤ) else if j = 29 then (-153050599659025494532144339049059670788709280000 : ℤ) else if j = 31 then (1130547851849520963188078583979403885867361120000 : ℤ) else if j = 32 then (6810567342741361400809588518346596793701888192000 : ℤ) else if j = 34 then (-413878112328526994260931890866167546432623083720000 : ℤ) else if j = 35 then (1520427499430573465768566110097478730769571835264000 : ℤ) else if j = 37 then (-2814793678727564041173296876400068245922109680160000 : ℤ) else if j = 38 then (-23334143738894557163085864070302890955132608745600000 : ℤ) else if j = 40 then (478089966414464216251506818050673303179187801230368000 : ℤ) else if j = 41 then (-1036974563393382757979259267960610196330161549295280000 : ℤ) else if j = 43 then (-2730070522967491798072345533368993935132508429669760000 : ℤ) else if j = 44 then (17205811440861603399714599501405181904621273477393920000 : ℤ) else if j = 46 then (-90554297159261164467304827878118129756257798404716480000 : ℤ) else if j = 47 then (66552184429295449474425336700727587197498822773427916800 : ℤ) else if j = 49 then (1005392909375380057613609292617777927497831654406868780000 : ℤ) else if j = 50 then (-2361855189038094278826474169673873295031152608626645603200 : ℤ) else if j = 52 then (906418422905074285050502376061233735846120963033238048000 : ℤ) else if j = 53 then (9716333323381507368647209138315841241468948326827585920000 : ℤ) else if j = 55 then (-56900403903553744836823533633076356767700952873817174112000 : ℤ) else if j = 56 then (54506831225011200669789741694137253967801381192383113600000 : ℤ) else if j = 58 then (247499883206007173440901603498808082461396303293758280820000 : ℤ) else if j = 59 then (-554630947554495014070092226426583158657644371420707390720000 : ℤ) else if j = 61 then (306913142427337164245412258249833675844690554904432117600000 : ℤ) else if j = 62 then (1126204339282006801901495647317254097085250074054487273856000 : ℤ) else if j = 64 then (-5473122215789969433973302082398474939988808692425298662720000 : ℤ) else if j = 65 then (4518962530853183330172995871346376943378673185515867597136000 : ℤ) else if j = 67 then (14686293809389189924443064738692325727579935971320903636352000 : ℤ) else if j = 68 then (-27725018450969030503396503809965799951902654188529215876480000 : ℤ) else if j = 70 then (7627325181019789974176216258011327622114856698148394818432000 : ℤ) else if j = 71 then (41424811696253920204187416053056647343917367609859743644800000 : ℤ) else if j = 73 then (-125967053305237571829892500862187730888902870060967626338080000 : ℤ) else if j = 74 then (75001078646902696443039735954142190464022316832999535842080000 : ℤ) else if j = 76 then (259183811290316236139741922668551484489432657535150986701440000 : ℤ) else if j = 77 then (-381443469659714092002755432808083010699533716655665544834496000 : ℤ) else if j = 79 then (-16422895176947485285260175659437605067243534444635155338880000 : ℤ) else if j = 80 then (488578086020804595841254048950291346331168205513741249494656000 : ℤ) else if j = 82 then (-827112467168037321069141394218924190312559252230698291684432000 : ℤ) else if j = 83 then (271737972447310406678617430133078702051704085073677764110080000 : ℤ) else if j = 85 then (1439989503470508200789156357908728744813904379793609517869312000 : ℤ) else if j = 86 then (-1610875997495205061289722381081559494347933492932212361903040000 : ℤ) else if j = 88 then (-476170754125688159350237540791213681813592353500236727239680000 : ℤ) else if j = 89 then (1814512530535474155838233410656142065499072773821718831464780000 : ℤ) else if j = 91 then (-1681709700840668348160074092318973669658269442208425332530560000 : ℤ) else if j = 92 then (70857557408900530974891998422125458884642826026499957495136000 : ℤ) else if j = 94 then (2590768898787687606148454624618682575258207723490698767686720000 : ℤ) else if j = 95 then (-2211227829531066337684827179270834930946356778266464353004896000 : ℤ) else if j = 97 then (-1012412570909854098231162081952429401180330330889737712971129600 : ℤ) else if j = 98 then (2142272074339294478869251566932436934549511034241166956865080000 : ℤ) else if j = 100 then (-1122431710142177451749508617761918275243873432981680820346752000 : ℤ) else if j = 101 then (-261411375940853451079530732609071513862087649921178653934880000 : ℤ) else if j = 103 then (1527614853189944494682387569874766536481495581826851137741440000 : ℤ) else if j = 104 then (-1028730056182967038783720327118942803197381981106542956172960000 : ℤ) else if j = 106 then (-514659984150101002611933873901987120559048018766006598565040000 : ℤ) else if j = 107 then (797421053061613932644143497448565583827300230301708846950848000 : ℤ) else if j = 109 then (-270519741670373046786767401245470892295565816808067981553280000 : ℤ) else if j = 110 then (-95038994635073888895946588746352041623949644466780761506080000 : ℤ) else if j = 112 then (287989998840015839884788958822705488470803587176332127091456000 : ℤ) else if j = 113 then (-167226329098686631198599392045648228626024474279414979396220000 : ℤ) else if j = 115 then (-63037305518480254633463084124293346881401090014844857101760000 : ℤ) else if j = 116 then (86603299745648271486219936639149182261455556559574914111520000 : ℤ) else if j = 118 then (-25952752865753343924984240595093957244996698897873401946560000 : ℤ) else if j = 119 then (-3230451972139883954364347797681041310665962899644695614560000 : ℤ) else if j = 121 then (15229480973735599282769073248189946386746188363276764370360000 : ℤ) else if j = 122 then (-8797308262926395189987408078639830903901941362089136384247200 : ℤ) else if j = 124 then (-1093900470136725537694754712437327976618368461354948865280000 : ℤ) else if j = 125 then (2062490525230912001077622411597393475410491653013337008550400 : ℤ) else if j = 127 then (-771498381488613669840173316029847827463188037733499056896000 : ℤ) else if j = 128 then (174164748794456728484224592351133789952231359898564483200000 : ℤ) else if j = 130 then (138270456028239508487388309970366978304183313264136408248000 : ℤ) else if j = 131 then (-93845328791352089364979012064815970426836884481920940800000 : ℤ) else if j = 133 then (10357291718245521338066637187962088222230230752017633600000 : ℤ) else if j = 134 then (1925287041179446437433272218020857305010240214033632000000 : ℤ) else if j = 136 then (-2620116233386862395328409373645250455904192642471340480000 : ℤ) else if j = 137 then (1172498809696786717547043045488032192794156554854146240000 : ℤ) else if j = 139 then (-57005795507149009466418795312014557154064524178377280000 : ℤ) else if j = 140 then (-17196286713300790627528584558980013906518811666151680000 : ℤ) else if j = 142 then (8980814125667787980975298573665417972935647604721376000 : ℤ) else if j = 143 then (-3115690030206422789817805665086408101451191400236800000 : ℤ) else if j = 145 then (170127482103098438273544876929094097139389268926152000 : ℤ) else if j = 146 then (-24963226934083284342444319257471781628614991608800000 : ℤ) else 0

def cD : ℕ → ℤ := fun j => if j = 25 then (-49995833502635621567153592802043048690325037 : ℤ) else if j = 26 then (769871043555942709342991217399290306357984875 : ℤ) else if j = 27 then (9593547448220117362718403687056806626181500720 : ℤ) else if j = 28 then (-192664298259683023168853347672206882952858372437 : ℤ) else if j = 29 then (707105994384740694583310632551306959958592485375 : ℤ) else if j = 30 then (2324221360628404587221662493260416343781433578280 : ℤ) else if j = 31 then (-16418720984869956598773946662803844013315392614637 : ℤ) else if j = 32 then (21519604046266625941287957459518547388255059860775 : ℤ) else if j = 33 then (-274018446939106784655654171817879307556134225008020 : ℤ) else if j = 34 then (2239036053001891591935359829226535894077642021069813 : ℤ) else if j = 35 then (-3724348948722343355343843324701270694101704338104425 : ℤ) else if j = 36 then (-13557055800187381007762023977510028214225088160862820 : ℤ) else if j = 37 then (42579785499518337658729691515431285887049415278232413 : ℤ) else if j = 38 then (-39619481381196603164541233766002059550858445433594425 : ℤ) else if j = 39 then (505265287337590646486297361560094068532772186228599180 : ℤ) else if j = 40 then (-2320422645352662498241319099432425859157253218528809067 : ℤ) else if j = 41 then (2171568936301560498557879842544521591325777829454404825 : ℤ) else if j = 42 then (4202145369665847738877390917992676513842130586902160710 : ℤ) else if j = 43 then (-269075649052177992673837757072091470992476840410563467 : ℤ) else if j = 44 then (3376479727713115019928495733171236168417077470571772825 : ℤ) else if j = 45 then (-177040362536546945606219935969594139253750685111572183450 : ℤ) else if j = 46 then (469866378581618473250012583858823041369586012678038375333 : ℤ) else if j = 47 then (-325789353656232234462121401876355839152784485066599307559 : ℤ) else if j = 48 then (581035331262945372148337676836877060716702680767710691750 : ℤ) else if j = 49 then (-2884605339266759058572640735825353045213130782004651768342 : ℤ) else if j = 50 then (771026388054166514695839515037860777744610507261101786907 : ℤ) else if j = 51 then (12603192550010853068824074258815600057162147043673526824350 : ℤ) else if j = 52 then (-16774526047947506006196683944459284405131686595841805403422 : ℤ) else if j = 53 then (16519801585664039236603562664821699879779406399011522772107 : ℤ) else if j = 54 then (-102172930765804060767777838924071036372745846574607494720250 : ℤ) else if j = 55 then (211320207845135354273081573664341896698496628129691831871098 : ℤ) else if j = 56 then (-80699635680687719647265703901364801910274064376286651861893 : ℤ) else if j = 57 then (10233115973983907434753901928890963102397568791585531926025 : ℤ) else if j = 58 then (-401368138653172771130696499285875421291172742126011781326227 : ℤ) else if j = 59 then (-248000011424689580343373835986172334251617050594269224125093 : ℤ) else if j = 60 then (2628043254194219819276593924377862287962177656832784121681785 : ℤ) else if j = 61 then (-2930122234980203873368797264100902090346932417557667522957227 : ℤ) else if j = 62 then (2434752940348361496824799974409525461791302010066128449019467 : ℤ) else if j = 63 then (-9990010478709830506390042810490095470654655691145859598841015 : ℤ) else if j = 64 then (15872344811265698717195878481593682557514690945020494660935973 : ℤ) else if j = 65 then (-2601599623088286554377299511160321453915268014337703086097923 : ℤ) else if j = 66 then (-2249940398120434753518784738070454926539998932945676863237790 : ℤ) else if j = 67 then (-14782641824670131739237533692582909528072294645660002935734347 : ℤ) else if j = 68 then (-22644934613094320154889640144909912926733709233891255493156723 : ℤ) else if j = 69 then (105271435040952548338689140008693058775940319616310084206719610 : ℤ) else if j = 70 then (-91118461591817368945165404144430343922946053122566939036489467 : ℤ) else if j = 71 then (77481612518648556536511476295697962755749671647707600482941277 : ℤ) else if j = 72 then (-255727915363277411763479593739441802474253420459363073154509790 : ℤ) else if j = 73 then (302890965208146608593518063624807215200227660759886725684967833 : ℤ) else if j = 74 then (-13081002290415506745174558653271001410940004895847550750481423 : ℤ) else if j = 75 then (-4476876371416573618824850913265928421394444022926513966359910 : ℤ) else if j = 76 then (-195309419845802950719356863146495475232504558959270339825368567 : ℤ) else if j = 77 then (-383731517751227770472525816943867897934423165800742328937327783 : ℤ) else if j = 78 then (1110366208316233343369041635014791524537050150544792555115789590 : ℤ) else if j = 79 then (-737496491472614492372918567682887691722922121891000931636545767 : ℤ) else if j = 80 then (746592152185162959094470707148379319540977061772498835851459177 : ℤ) else if j = 81 then (-1991866237441251894566065584638638190507192653565429585823466785 : ℤ) else if j = 82 then (1732808115760064904206443546871224292837837517885573727188385803 : ℤ) else if j = 83 then (-4456761175061749093962200897283115045799449551478179447616023 : ℤ) else if j = 84 then (321461738627043163326588102852840074375138326796976051336589215 : ℤ) else if j = 85 then (-861159902674878727792523538163042422894119966826311080980679317 : ℤ) else if j = 86 then (-1822335683912427782605156928355796899769540548723515644328148423 : ℤ) else if j = 87 then (3560120905122656244376303265340909645210401699304343943360667615 : ℤ) else if j = 88 then (-1856441835723724465931403961453782018115158873690486570985418517 : ℤ) else if j = 89 then (2373087997321641964342712719571561646929047689132570708962190252 : ℤ) else if j = 90 then (-4962854551116329514582254464443776203490096951987950570167184110 : ℤ) else if j = 91 then (3172672252321112113905793149258184196826765689393455706486485083 : ℤ) else if j = 92 then (-14296887273562787629804169936154441005009176847706606930256188 : ℤ) else if j = 93 then (1070100132049852572084142643616668673524261117179945444818036390 : ℤ) else if j = 94 then (-1113804396668537576160998872165630287859222443148111948673703117 : ℤ) else if j = 95 then (-2749238767426024709820959142905857851299938366416764729483547348 : ℤ) else if j = 96 then (3765040316735676201285962274984083938079410033844950584900429390 : ℤ) else if j = 97 then (-1636363996666011369173492206375766909881364304402414904254870465 : ℤ) else if j = 98 then (2463072984120849527265600368555630737414191560393603514786581202 : ℤ) else if j = 99 then (-3979179647117715685020856196817673529763467828581888075779500610 : ℤ) else if j = 100 then (1865405863408860195654437790933257850965330370635744551364552175 : ℤ) else if j = 101 then (31693406468766341138166197418450732332597261466130027530423402 : ℤ) else if j = 102 then (689311924732857516460137053394432419366764305975952467717436110 : ℤ) else if j = 103 then (-334761590864894008727221345082069456315200692718428131616273825 : ℤ) else if j = 104 then (-1371858427765947161842413847530168666277163025653310030351339198 : ℤ) else if j = 105 then (1379912403171490911348653183422924076576537304609109824761468820 : ℤ) else if j = 106 then (-529814965922941679835834492260341335679123291654635086122169075 : ℤ) else if j = 107 then (775582185705436535267629665805781028005461676532549102793564082 : ℤ) else if j = 108 then (-977603206957570021697558948015037164785765137623348081488867980 : ℤ) else if j = 109 then (319588463953953326634903098333694617673113402017552901730992925 : ℤ) else if j = 110 then (65347715783425534695571431269961407984750598462386754748050282 : ℤ) else if j = 111 then (70474706275624833857257083644795929608500663617113977381363220 : ℤ) else if j = 112 then (6683413867163752904940605954798719231615986004243685290993725 : ℤ) else if j = 113 then (-215655927788358775132404413574022561734907366578212277871387293 : ℤ) else if j = 114 then (169651425976037756571337011920447786068492584713285824737730470 : ℤ) else if j = 115 then (-54202746340361406162873118996273127115262292771407926087689275 : ℤ) else if j = 116 then (59609745913758748166215995350562486972176206957939272809028907 : ℤ) else if j = 117 then (-61239286832105728097069033679058226336152175741163249341174250 : ℤ) else if j = 118 then (10122825596649799583538181520890737551679776001761387497459725 : ℤ) else if j = 119 then (12926299539486048881944869706998709710764681495762033084420307 : ℤ) else if j = 120 then (-3768566463603230143880342522567138923944373508728285900893210 : ℤ) else if j = 121 then (3388124110273482358996358607722450099242562416378610896475100 : ℤ) else if j = 122 then (-8285487118262583972302483843128881408091006965574386040105686 : ℤ) else if j = 123 then (5291196152994502545604375508082998386902514666895023740621990 : ℤ) else if j = 124 then (-964405443689461001434684155294009999205229671733057216232900 : ℤ) else if j = 125 then (379689967555409479818372439553188092603832950187185044306490 : ℤ) else if j = 126 then (-475504995802452832574688407434894564057132823813491997644410 : ℤ) else if j = 127 then (-105640007072093085988416247387579141162764076200764793752100 : ℤ) else if j = 128 then (323701346442619897447717938797043652830694584692583081417690 : ℤ) else if j = 129 then (-136465803852165796566543213326078988262559432777901794074260 : ℤ) else if j = 130 then (31450412658552048138988496756862124665380059700945871052875 : ℤ) else if j = 131 then (-29404753732737259574168683210536800566666783269732992905110 : ℤ) else if j = 132 then (15521380975278538566763186331500154468733924745873695804540 : ℤ) else if j = 133 then (2353643048938158765095208823646841344887815178964740037875 : ℤ) else if j = 134 then (-4362183761424173078917338567098868412673555363402042243110 : ℤ) else if j = 135 then (1253577310700849937808483173340765959618067016215903716300 : ℤ) else if j = 136 then (-294388808919192968801650263516610839489053285596408165125 : ℤ) else if j = 137 then (231878627545945569530555263101395510901033676894480198230 : ℤ) else if j = 138 then (-70123690784330899863328317193829408782925882424232911000 : ℤ) else if j = 139 then (-21588966482207709573846912410047586086972108907085178125 : ℤ) else if j = 140 then (17030706707903394735285684977040381795465136638476713350 : ℤ) else if j = 141 then (-3016762898730940314486435613830647334368436131751896400 : ℤ) else if j = 142 then (-93934463509009728166940215460225335043389020262308625 : ℤ) else if j = 143 then (58888171522434042617621461913761333943097207741054550 : ℤ) else 0

def aIdx : Finset ℕ := {25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 73, 74, 76, 77, 79, 80, 82, 83, 85, 86, 88, 89, 91, 92, 94, 95, 97, 98, 100, 101, 103, 104, 106, 107, 109, 110, 112, 113, 115, 116, 118, 119, 121, 122, 124, 125, 127, 128, 130, 131, 133, 134, 136, 137, 139, 140, 142, 143, 145, 146}
def dIdx : Finset ℕ := {25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143}

/-! ## index bounds -/

lemma aIdx_bounds (j : ℕ) (hj : j ∈ aIdx) : 25 ≤ j ∧ j ≤ 146 := by
  simp only [aIdx, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

lemma dIdx_bounds (k : ℕ) (hk : k ∈ dIdx) : 25 ≤ k ∧ k ≤ 143 := by
  simp only [dIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  omega



def Sf (i : ℕ) : Finset ℕ := (Finset.range 25).image (fun j => 3 * j + i)

/-! ## polynomials -/

noncomputable def Dpol : ℤ[X] := ∏ τ ∈ Finset.range 122, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2
noncomputable def Qpol (i : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 122, (if τ ∈ Sf i then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Rpol (j : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 122, (if (25 + τ : ℕ) = j then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Tpol (k : ℕ) : ℤ[X] :=
  (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
    (∏ τ ∈ Finset.range 122, (if (25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3 then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)))
noncomputable def Ppol (i : ℕ) : ℤ[X] := ∏ j ∈ Finset.range 25, (C (3:ℤ) * X + C ((25 + 3 * j + i : ℕ) : ℤ))

noncomputable def P1 : ℤ[X] :=
  C ((2449355331463399245243817101990587209159419235557239421496624563961175150924305897881600000000 : ℤ)) *
    ((∏ r ∈ Finset.range 48, (Polynomial.X + C (((r : ℤ) + 1)))) *
    (∑ i ∈ Finset.range 50, C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) * Qpol i))

noncomputable def P2 : ℤ[X] :=
  C ((12413915592536072670862289047373375038521486354677760000000000 : ℤ)) *
    ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k))

/-! ## generic product lemmas -/

lemma prod_ite_one_eq {ι M : Type*} [CommMonoid M] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (f : ι → M) :
    (∏ i ∈ s, (if p i then (1 : M) else f i)) = ∏ i ∈ s.filter (fun i => ¬ p i), f i := by
  rw [Finset.prod_ite]
  simp

lemma Sf_subset (i : ℕ) (hi : i < 50) : Sf i ⊆ Finset.range 122 := by
  intro τ hτ
  simp only [Sf, Finset.mem_image, Finset.mem_range] at hτ ⊢
  obtain ⟨j, hj, rfl⟩ := hτ
  omega

lemma Sf_card (i : ℕ) : (Sf i).card = 25 := by
  rw [Sf, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have h : 3 * x + i = 3 * y + i := hxy
    omega

lemma prod_Sf_eq (i : ℕ) (F : ℕ → ℤ[X]) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 25, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma Ppol_sq_eq (i : ℕ) :
    (Ppol i) ^ 2 = ∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Ppol, prod_Sf_eq i (fun τ => (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  have h : (25 + (3 * j + i) : ℕ) = 25 + 3 * j + i := by omega
  rw [h]

lemma Qpol_eq (i : ℕ) (hi : i < 50) :
    Qpol i = ∏ τ ∈ (Finset.range 122) \ Sf i, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Qpol, prod_ite_one_eq, Finset.sdiff_eq_filter]

lemma prod_range_split (i : ℕ) (hi : i < 50) (F : ℕ → ℤ[X]) :
    (∏ τ ∈ Finset.range 122, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 122) \ Sf i, F τ) := by
  rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset (Sf_subset i hi)]

lemma Dpol_split (i : ℕ) (hi : i < 50) :
    Dpol = (∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2) *
      (∏ τ ∈ (Finset.range 122) \ Sf i, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2) := by
  unfold Dpol
  exact prod_range_split i hi _

lemma Dpol_eq_Ppol_sq_mul_Qpol (i : ℕ) (hi : i < 50) : Dpol = Ppol i ^ 2 * Qpol i := by
  rw [Dpol_split i hi, ← Ppol_sq_eq i, ← Qpol_eq i hi]

lemma Rpol_eq (j : ℕ) :
    Rpol j = ∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = j)),
      (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Rpol, prod_ite_one_eq]

lemma prod_filter_step (j : ℕ) :
    (∏ τ ∈ Finset.range 122, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 122).filter (fun τ => (25 + τ : ℕ) = j),
            (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = j)),
            (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 122) (fun τ => (25 + τ : ℕ) = j) _).symm

lemma filter_eq_singleton (j : ℕ) (h1 : 25 ≤ j) (h2 : j ≤ 146) :
    (Finset.range 122).filter (fun τ => (25 + τ : ℕ) = j) = {j - 25} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hj⟩; omega
  · rintro rfl; constructor <;> omega

lemma Dpol_eq_sq_mul_Rpol (j : ℕ) (h1 : 25 ≤ j) (h2 : j ≤ 146) :
    Dpol = (C (3:ℤ) * X + C (j : ℤ)) ^ 2 * Rpol j := by
  rw [Dpol, prod_filter_step j, Rpol_eq j, filter_eq_singleton j h1 h2, Finset.prod_singleton]
  have e : ((25 + (j - 25) : ℕ) : ℤ) = (j : ℤ) := by omega
  rw [e]

lemma prod_filter_step2 (k : ℕ) :
    (∏ τ ∈ Finset.range 122, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 122).filter (fun τ => ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 122)
    (fun τ => ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)) _).symm

lemma filter_eq_pair (k : ℕ) (h1 : 25 ≤ k) (h2 : k ≤ 143) :
    (Finset.range 122).filter (fun τ => ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)) = {k - 25, k - 22} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hk | hk⟩
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> constructor <;> omega

lemma Dpol_eq_lin_mul_Tpol (k : ℕ) (h1 : 25 ≤ k) (h2 : k ≤ 143) :
    Dpol = (C (3:ℤ) * X + C (k : ℤ)) * (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) * Tpol k := by
  have hne : k - 25 ∉ ({k - 22} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [Tpol, prod_ite_one_eq, Dpol, prod_filter_step2 k, filter_eq_pair k h1 h2,
    Finset.prod_insert hne, Finset.prod_singleton]
  have e1 : ((25 + (k - 25) : ℕ) : ℤ) = (k : ℤ) := by omega
  have e2 : ((25 + (k - 22) : ℕ) : ℤ) = ((k + 3 : ℕ) : ℤ) := by omega
  rw [e1, e2]
  ring

/-! ## degree bounds -/

lemma natDegree_lin_le (c : ℤ) : (C (3:ℤ) * X + C c).natDegree ≤ 1 := by
  calc (C (3:ℤ) * X + C c).natDegree ≤ max (C (3:ℤ) * X).natDegree (C c).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ max 1 0 := by
        apply max_le
        · calc (C (3:ℤ) * X).natDegree ≤ X.natDegree := Polynomial.natDegree_C_mul_le _ _
            _ = 1 := Polynomial.natDegree_X
        · rw [Polynomial.natDegree_C]; norm_num
    _ = 1 := by norm_num

lemma natDegree_sq_lin_le (c : ℤ) : ((C (3:ℤ) * X + C c) ^ 2).natDegree ≤ 2 := by
  calc ((C (3:ℤ) * X + C c) ^ 2).natDegree ≤ 2 * (C (3:ℤ) * X + C c).natDegree :=
        Polynomial.natDegree_pow_le
    _ ≤ 2 * 1 := by gcongr; exact natDegree_lin_le c
    _ = 2 := by norm_num

lemma natDegree_prod_sq_le_card (s : Finset ℕ) :
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 2 * s.card := by
  have h1 : (∏ τ ∈ s, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤
      ∑ τ ∈ s, ((C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2).natDegree :=
    Polynomial.natDegree_prod_le s (fun τ => (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)
  have h2 : (∑ τ ∈ s, ((C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2).natDegree) ≤ ∑ _τ ∈ s, 2 :=
    Finset.sum_le_sum (fun τ _ => natDegree_sq_lin_le _)
  have h3 : (∑ _τ ∈ s, (2 : ℕ)) = 2 * s.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  linarith

lemma natDegree_prod_sq_le_244 (s : Finset ℕ) (h : s.card ≤ 122) :
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 244 :=
  le_trans (natDegree_prod_sq_le_card s) (by omega)

lemma natDegree_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (n : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ n) : (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · exact h a (Finset.mem_insert_self a s)
      · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma filter_card_le (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range 122).filter p).card ≤ 122 := by
  have h := Finset.card_le_card (Finset.filter_subset p (Finset.range 122))
  rwa [Finset.card_range] at h

lemma card_sdiff_le (s : Finset ℕ) : ((Finset.range 122) \ s).card ≤ 122 := by
  have h := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range 122) (t := s))
  rwa [Finset.card_range] at h

lemma natDegree_Qpol_le (i : ℕ) (hi : i < 50) : (Qpol i).natDegree ≤ 244 := by
  rw [Qpol_eq i hi]
  exact natDegree_prod_sq_le_244 _ (card_sdiff_le _)

lemma natDegree_Rpol_le (j : ℕ) : (Rpol j).natDegree ≤ 244 := by
  rw [Rpol_eq j]
  exact natDegree_prod_sq_le_244 _ (filter_card_le _)

lemma Tpol_eq' (k : ℕ) :
    Tpol k = (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)) := by
  rw [Tpol, prod_ite_one_eq]

lemma natDegree_Tpol_le (k : ℕ) : (Tpol k).natDegree ≤ 246 := by
  have h1 : (Tpol k).natDegree ≤ (C (3:ℤ) * X + C (k : ℤ)).natDegree +
      ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
        (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
          (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)).natDegree := by
    rw [Tpol_eq' k]
    exact Polynomial.natDegree_mul_le
  have h2 : ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2)).natDegree ≤ 1 + 244 := by
    have hm := Polynomial.natDegree_mul_le (p := (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)))
      (q := (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2))
    have ha : (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
    have hb : (∏ τ ∈ (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((25 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 244 :=
      natDegree_prod_sq_le_244 _ (filter_card_le _)
    linarith
  have h3 : (C (3:ℤ) * X + C (k : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
  linarith

lemma natDegree_P1_le : P1.natDegree ≤ 292 := by
  have h1 : P1.natDegree ≤ (C ((79766443076872509863361 : ℤ) * (175232954511896091869033107292160000 : ℤ) ^ 2)).natDegree +
      ((∏ r ∈ Finset.range 48, (Polynomial.X + C (((r : ℤ) + 1)))) *
        (∑ i ∈ Finset.range 50,
          C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) * Qpol i)).natDegree := by
    rw [P1]
    exact Polynomial.natDegree_mul_le
  have h2 : ((∏ r ∈ Finset.range 48, (Polynomial.X + C (((r : ℤ) + 1)))) *
      (∑ i ∈ Finset.range 50,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) * Qpol i)).natDegree ≤ 48 + 244 := by
    refine le_trans (Polynomial.natDegree_mul_le) (add_le_add ?_ ?_)
    · have hp : (∏ r ∈ Finset.range 48, (Polynomial.X + C (((r : ℤ) + 1)))).natDegree ≤
          ∑ r ∈ Finset.range 48, (Polynomial.X + C (((r : ℤ) + 1))).natDegree :=
        Polynomial.natDegree_prod_le _ _
      have hq : (∑ r ∈ Finset.range 48, (Polynomial.X + C (((r : ℤ) + 1))).natDegree) = 48 := by
        rw [Finset.sum_congr rfl (fun r _ => Polynomial.natDegree_X_add_C _)]
        simp
      omega
    · exact natDegree_sum_le' _ _ 244 (fun i hi => by
        rw [Finset.mem_range] at hi
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Qpol_le i hi))
  have h3 : (C ((79766443076872509863361 : ℤ) * (175232954511896091869033107292160000 : ℤ) ^ 2)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma natDegree_P2_le : P2.natDegree ≤ 246 := by
  have h1 : P2.natDegree ≤ (C ((12413915592536072670862289047373375038521486354677760000000000 : ℤ))).natDegree +
      ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree := by
    rw [P2]
    exact Polynomial.natDegree_mul_le
  have hR : (∑ j ∈ aIdx, C (cA j) * Rpol j).natDegree ≤ 244 :=
    natDegree_sum_le' _ _ 244 (fun j _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Rpol_le j))
  have hT : (∑ k ∈ dIdx, C (cD k) * Tpol k).natDegree ≤ 246 :=
    natDegree_sum_le' _ _ 246 (fun k _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Tpol_le k))
  have h2 : ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree ≤
      246 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (le_trans hR (by norm_num)) hT)
  have h3 : (C ((12413915592536072670862289047373375038521486354677760000000000 : ℤ))).natDegree = 0 := Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma degree_bound : max P1.natDegree P2.natDegree < 293 := by
  rw [max_lt_iff]
  constructor
  · exact lt_of_le_of_lt natDegree_P1_le (by norm_num)
  · exact lt_of_le_of_lt natDegree_P2_le (by norm_num)

/-! ## evaluation of the polynomials (integer form) -/

def EvP1 (c : ℤ) : ℤ := (79766443076872509863361 * 175232954511896091869033107292160000 ^ 2) *
  ((∏ r ∈ Finset.range 48, (c + ((r : ℤ) + 1))) *
   (∑ i ∈ Finset.range 50, (Lc * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) *
     (∏ τ ∈ Finset.range 122, (if τ ∈ Sf i then 1 else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2))))

def EvP2 (c : ℤ) : ℤ := 12413915592536072670862289047373375038521486354677760000000000 *
  ((∑ j ∈ aIdx, cA j * (∏ τ ∈ Finset.range 122, (if (25 + τ : ℕ) = j then 1 else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2)))
   + (∑ k ∈ dIdx, cD k * ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) * (∏ τ ∈ Finset.range 122, (if (25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3 then 1 else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2)))))

lemma eval_ite (p : Prop) [Decidable p] (x : ℤ) (a b : ℤ[X]) :
    Polynomial.eval x (if p then a else b) = if p then Polynomial.eval x a else Polynomial.eval x b := by
  split <;> rfl

lemma eval_P1_EvP1 (c : ℤ) : P1.eval c = EvP1 c := by
  rw [P1, EvP1]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_one, Qpol,
    eval_ite]
  ring

lemma eval_P2_EvP2 (c : ℤ) : P2.eval c = EvP2 c := by
  rw [P2, EvP2]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_one, Rpol, Tpol,
    eval_ite]
  ring

/-! ## Cheap evaluation

The kernel evaluation of `EvP1`/`EvP2` recomputes all the 72-factor products, which is
prohibitively slow.  We introduce the single common product `Pall c` and rewrite
`EvP1`/`EvP2` in terms of it (dividing out the factors that are absent), so that each
`decide` only has to compute `Pall c` once and perform divisions by small factors. -/

def Pall (c : ℤ) : ℤ := ∏ τ ∈ Finset.range 122, (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2

lemma prod_Sf_eqZ (i : ℕ) (F : ℕ → ℤ) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 25, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma prod_range_splitZ (i : ℕ) (hi : i < 50) (F : ℕ → ℤ) :
    (∏ τ ∈ Finset.range 122, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 122) \ Sf i, F τ) := by
  rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset (Sf_subset i hi)]

lemma sqf_ne_zero {c : ℤ} (hc : 0 ≤ c) {t : ℕ} (ht : 0 < t) : (3 * c + (t : ℤ)) ^ 2 ≠ 0 := by
  refine pow_ne_zero 2 ?_
  have h1 : (0 : ℤ) ≤ 3 * c := by linarith
  have h2 : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  linarith

lemma prod_erase_eq_div (s : Finset ℕ) (a : ℕ) (ha : a ∈ s) (g : ℕ → ℤ) (hg : g a ≠ 0) :
    (∏ x ∈ s.erase a, g x) = (∏ x ∈ s, g x) / g a := by
  have h := Finset.prod_erase_mul s g ha
  rw [← h]
  exact (Int.mul_ediv_cancel _ hg).symm

lemma prod_erase_pair_eq_div (s : Finset ℕ) (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s.erase a)
    (g : ℕ → ℤ) (ha' : g a ≠ 0) (hb' : g b ≠ 0) :
    (∏ x ∈ (s.erase a).erase b, g x) = (∏ x ∈ s, g x) / (g a * g b) := by
  have hP : (∏ x ∈ s, g x) = (g a * g b) * (∏ x ∈ (s.erase a).erase b, g x) := by
    rw [← Finset.prod_erase_mul s g ha, ← Finset.prod_erase_mul (s.erase a) g hb]
    ring
  rw [hP]
  exact (Int.mul_ediv_cancel_left _ (mul_ne_zero ha' hb')).symm

lemma filter_not_eq_erase (j : ℕ) (h1 : 25 ≤ j) (h2 : j ≤ 146) :
    (Finset.range 122).filter (fun τ => ¬ ((25 + τ : ℕ) = j)) =
      (Finset.range 122).erase (j - 25) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨hlt, hne⟩
    exact ⟨fun h => hne (by omega), hlt⟩
  · rintro ⟨hne, hlt⟩
    exact ⟨hlt, fun h => hne (by omega)⟩

lemma filter_not_pair_eq_erase (k : ℕ) (h1 : 25 ≤ k) (h2 : k ≤ 143) :
    (Finset.range 122).filter
        (fun τ => ¬ ((25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3)) =
      ((Finset.range 122).erase (k - 25)).erase (k - 22) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨hlt, hne⟩
    refine ⟨?_, ?_, hlt⟩
    · intro h; exact hne (Or.inr (by omega))
    · intro h; exact hne (Or.inl (by omega))
  · rintro ⟨hne1, hne2, hlt⟩
    refine ⟨hlt, ?_⟩
    rintro (h | h)
    · exact hne2 (by omega)
    · exact hne1 (by omega)

lemma prod_ite_eq_div {c : ℤ} (hc : 0 ≤ c) (j : ℕ) (h1 : 25 ≤ j) (h2 : j ≤ 146) :
    (∏ τ ∈ Finset.range 122,
        (if (25 + τ : ℕ) = j then (1 : ℤ)
          else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (3 * c + ((25 + (j - 25) : ℕ) : ℤ)) ^ 2 := by
  have hmem : j - 25 ∈ Finset.range 122 := by
    simp only [Finset.mem_range]; omega
  have hne : (3 * c + ((25 + (j - 25) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hj : (25 + (j - 25) : ℕ) = j := by omega
    rw [hj]; exact sqf_ne_zero hc (by omega : 0 < j)
  rw [prod_ite_one_eq, filter_not_eq_erase j h1 h2, Pall]
  exact prod_erase_eq_div _ _ hmem _ hne

lemma prod_ite_pair_eq_div {c : ℤ} (hc : 0 ≤ c) (k : ℕ) (h1 : 25 ≤ k)
    (h2 : k ≤ 143) :
    (∏ τ ∈ Finset.range 122,
        (if (25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3 then (1 : ℤ)
          else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / ((3 * c + ((25 + (k - 25) : ℕ) : ℤ)) ^ 2 *
          (3 * c + ((25 + (k - 22) : ℕ) : ℤ)) ^ 2) := by
  have hmem1 : k - 25 ∈ Finset.range 122 := by
    simp only [Finset.mem_range]; omega
  have hmem2 : k - 22 ∈ (Finset.range 122).erase (k - 25) := by
    simp only [Finset.mem_erase, Finset.mem_range]
    constructor
    · omega
    · omega
  have hne1 : (3 * c + ((25 + (k - 25) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (25 + (k - 25) : ℕ) = k := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k)
  have hne2 : (3 * c + ((25 + (k - 22) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (25 + (k - 22) : ℕ) = k + 3 := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k + 3)
  rw [prod_ite_one_eq, filter_not_pair_eq_erase k h1 h2, Pall]
  exact prod_erase_pair_eq_div _ _ _ hmem1 hmem2 _ hne1 hne2

lemma prod_ite_Sf_eq_div {c : ℤ} (hc : 0 ≤ c) (i : ℕ) (hi : i < 50) :
    (∏ τ ∈ Finset.range 122,
        (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (∏ j ∈ Finset.range 25,
          (3 * c + ((25 + (3 * j + i) : ℕ) : ℤ)) ^ 2) := by
  have hSf : (∏ τ ∈ Sf i, (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ j ∈ Finset.range 25, (3 * c + ((25 + (3 * j + i) : ℕ) : ℤ)) ^ 2) :=
    prod_Sf_eqZ i _
  have hne : (∏ j ∈ Finset.range 25,
      (3 * c + ((25 + (3 * j + i) : ℕ) : ℤ)) ^ 2) ≠ 0 := by
    rw [← hSf]
    exact Finset.prod_ne_zero_iff.mpr (fun τ _ => sqf_ne_zero hc (by omega : 0 < 25 + τ))
  have hsplit : Pall c =
      (∏ j ∈ Finset.range 25, (3 * c + ((25 + (3 * j + i) : ℕ) : ℤ)) ^ 2) *
        (∏ τ ∈ (Finset.range 122) \ Sf i,
          (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2) := by
    rw [Pall, prod_range_splitZ i hi, hSf]
  rw [prod_ite_one_eq, ← Finset.sdiff_eq_filter, hsplit,
    Int.mul_ediv_cancel_left _ hne]

def EvP1cheap (c : ℤ) : ℤ :=
  (79766443076872509863361 * 175232954511896091869033107292160000 ^ 2) *
    ((∏ r ∈ Finset.range 48, (c + ((r : ℤ) + 1))) *
     (∑ i ∈ Finset.range 50, (Lc * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) *
       (Pall c / (∏ j ∈ Finset.range 25,
         (3 * c + ((25 + (3 * j + i) : ℕ) : ℤ)) ^ 2))))

def EvP2cheap (c : ℤ) : ℤ :=
  (12413915592536072670862289047373375038521486354677760000000000) *
    ((∑ j ∈ aIdx, cA j * (Pall c / (3 * c + ((25 + (j - 25) : ℕ) : ℤ)) ^ 2))
     + (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((25 + (k - 25) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((25 + (k - 22) : ℕ) : ℤ)) ^ 2)))))

lemma EvP1_sum_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ i ∈ Finset.range 50, (Lc * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) *
        (∏ τ ∈ Finset.range 122,
          (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ i ∈ Finset.range 50, (Lc * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) *
        (Pall c / (∏ j ∈ Finset.range 25,
          (3 * c + ((25 + (3 * j + i) : ℕ) : ℤ)) ^ 2))) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [prod_ite_Sf_eq_div hc i hi]

lemma EvP2_sum1_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ j ∈ aIdx, cA j *
        (∏ τ ∈ Finset.range 122,
          (if (25 + τ : ℕ) = j then (1 : ℤ)
            else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ j ∈ aIdx, cA j *
        (Pall c / (3 * c + ((25 + (j - 25) : ℕ) : ℤ)) ^ 2)) := by
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨h1, h2⟩ := aIdx_bounds j hj
  rw [prod_ite_eq_div hc j h1 h2]

lemma EvP2_sum2_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ k ∈ dIdx, cD k *
        ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
          (∏ τ ∈ Finset.range 122,
            (if (25 + τ : ℕ) = k ∨ (25 + τ : ℕ) = k + 3 then (1 : ℤ)
              else (3 * c + ((25 + τ : ℕ) : ℤ)) ^ 2))))
      = (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((25 + (k - 25) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((25 + (k - 22) : ℕ) : ℤ)) ^ 2)))) := by
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨h1, h2⟩ := dIdx_bounds k hk
  rw [prod_ite_pair_eq_div hc k h1 h2]

lemma EvP1_eq_cheap {c : ℤ} (hc : 0 ≤ c) : EvP1 c = EvP1cheap c := by
  rw [EvP1, EvP1cheap, EvP1_sum_eq hc]

lemma EvP2_eq_cheap {c : ℤ} (hc : 0 ≤ c) : EvP2 c = EvP2cheap c := by
  rw [EvP2, EvP2cheap, EvP2_sum1_eq hc, EvP2_sum2_eq hc]


set_option maxHeartbeats 0 in
lemma evc_0 : EvP1 (0:ℤ) = EvP2 (0:ℤ) := by
  rw [EvP1_eq_cheap (c := (0:ℤ)) (by norm_num), EvP2_eq_cheap (c := (0:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_1 : EvP1 (1:ℤ) = EvP2 (1:ℤ) := by
  rw [EvP1_eq_cheap (c := (1:ℤ)) (by norm_num), EvP2_eq_cheap (c := (1:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_2 : EvP1 (2:ℤ) = EvP2 (2:ℤ) := by
  rw [EvP1_eq_cheap (c := (2:ℤ)) (by norm_num), EvP2_eq_cheap (c := (2:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_3 : EvP1 (3:ℤ) = EvP2 (3:ℤ) := by
  rw [EvP1_eq_cheap (c := (3:ℤ)) (by norm_num), EvP2_eq_cheap (c := (3:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_4 : EvP1 (4:ℤ) = EvP2 (4:ℤ) := by
  rw [EvP1_eq_cheap (c := (4:ℤ)) (by norm_num), EvP2_eq_cheap (c := (4:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_5 : EvP1 (5:ℤ) = EvP2 (5:ℤ) := by
  rw [EvP1_eq_cheap (c := (5:ℤ)) (by norm_num), EvP2_eq_cheap (c := (5:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_6 : EvP1 (6:ℤ) = EvP2 (6:ℤ) := by
  rw [EvP1_eq_cheap (c := (6:ℤ)) (by norm_num), EvP2_eq_cheap (c := (6:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_7 : EvP1 (7:ℤ) = EvP2 (7:ℤ) := by
  rw [EvP1_eq_cheap (c := (7:ℤ)) (by norm_num), EvP2_eq_cheap (c := (7:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_8 : EvP1 (8:ℤ) = EvP2 (8:ℤ) := by
  rw [EvP1_eq_cheap (c := (8:ℤ)) (by norm_num), EvP2_eq_cheap (c := (8:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_9 : EvP1 (9:ℤ) = EvP2 (9:ℤ) := by
  rw [EvP1_eq_cheap (c := (9:ℤ)) (by norm_num), EvP2_eq_cheap (c := (9:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_10 : EvP1 (10:ℤ) = EvP2 (10:ℤ) := by
  rw [EvP1_eq_cheap (c := (10:ℤ)) (by norm_num), EvP2_eq_cheap (c := (10:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_11 : EvP1 (11:ℤ) = EvP2 (11:ℤ) := by
  rw [EvP1_eq_cheap (c := (11:ℤ)) (by norm_num), EvP2_eq_cheap (c := (11:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_12 : EvP1 (12:ℤ) = EvP2 (12:ℤ) := by
  rw [EvP1_eq_cheap (c := (12:ℤ)) (by norm_num), EvP2_eq_cheap (c := (12:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_13 : EvP1 (13:ℤ) = EvP2 (13:ℤ) := by
  rw [EvP1_eq_cheap (c := (13:ℤ)) (by norm_num), EvP2_eq_cheap (c := (13:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_14 : EvP1 (14:ℤ) = EvP2 (14:ℤ) := by
  rw [EvP1_eq_cheap (c := (14:ℤ)) (by norm_num), EvP2_eq_cheap (c := (14:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_15 : EvP1 (15:ℤ) = EvP2 (15:ℤ) := by
  rw [EvP1_eq_cheap (c := (15:ℤ)) (by norm_num), EvP2_eq_cheap (c := (15:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_16 : EvP1 (16:ℤ) = EvP2 (16:ℤ) := by
  rw [EvP1_eq_cheap (c := (16:ℤ)) (by norm_num), EvP2_eq_cheap (c := (16:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_17 : EvP1 (17:ℤ) = EvP2 (17:ℤ) := by
  rw [EvP1_eq_cheap (c := (17:ℤ)) (by norm_num), EvP2_eq_cheap (c := (17:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_18 : EvP1 (18:ℤ) = EvP2 (18:ℤ) := by
  rw [EvP1_eq_cheap (c := (18:ℤ)) (by norm_num), EvP2_eq_cheap (c := (18:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_19 : EvP1 (19:ℤ) = EvP2 (19:ℤ) := by
  rw [EvP1_eq_cheap (c := (19:ℤ)) (by norm_num), EvP2_eq_cheap (c := (19:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_20 : EvP1 (20:ℤ) = EvP2 (20:ℤ) := by
  rw [EvP1_eq_cheap (c := (20:ℤ)) (by norm_num), EvP2_eq_cheap (c := (20:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_21 : EvP1 (21:ℤ) = EvP2 (21:ℤ) := by
  rw [EvP1_eq_cheap (c := (21:ℤ)) (by norm_num), EvP2_eq_cheap (c := (21:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_22 : EvP1 (22:ℤ) = EvP2 (22:ℤ) := by
  rw [EvP1_eq_cheap (c := (22:ℤ)) (by norm_num), EvP2_eq_cheap (c := (22:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_23 : EvP1 (23:ℤ) = EvP2 (23:ℤ) := by
  rw [EvP1_eq_cheap (c := (23:ℤ)) (by norm_num), EvP2_eq_cheap (c := (23:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_24 : EvP1 (24:ℤ) = EvP2 (24:ℤ) := by
  rw [EvP1_eq_cheap (c := (24:ℤ)) (by norm_num), EvP2_eq_cheap (c := (24:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_25 : EvP1 (25:ℤ) = EvP2 (25:ℤ) := by
  rw [EvP1_eq_cheap (c := (25:ℤ)) (by norm_num), EvP2_eq_cheap (c := (25:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_26 : EvP1 (26:ℤ) = EvP2 (26:ℤ) := by
  rw [EvP1_eq_cheap (c := (26:ℤ)) (by norm_num), EvP2_eq_cheap (c := (26:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_27 : EvP1 (27:ℤ) = EvP2 (27:ℤ) := by
  rw [EvP1_eq_cheap (c := (27:ℤ)) (by norm_num), EvP2_eq_cheap (c := (27:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_28 : EvP1 (28:ℤ) = EvP2 (28:ℤ) := by
  rw [EvP1_eq_cheap (c := (28:ℤ)) (by norm_num), EvP2_eq_cheap (c := (28:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_29 : EvP1 (29:ℤ) = EvP2 (29:ℤ) := by
  rw [EvP1_eq_cheap (c := (29:ℤ)) (by norm_num), EvP2_eq_cheap (c := (29:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_30 : EvP1 (30:ℤ) = EvP2 (30:ℤ) := by
  rw [EvP1_eq_cheap (c := (30:ℤ)) (by norm_num), EvP2_eq_cheap (c := (30:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_31 : EvP1 (31:ℤ) = EvP2 (31:ℤ) := by
  rw [EvP1_eq_cheap (c := (31:ℤ)) (by norm_num), EvP2_eq_cheap (c := (31:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_32 : EvP1 (32:ℤ) = EvP2 (32:ℤ) := by
  rw [EvP1_eq_cheap (c := (32:ℤ)) (by norm_num), EvP2_eq_cheap (c := (32:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_33 : EvP1 (33:ℤ) = EvP2 (33:ℤ) := by
  rw [EvP1_eq_cheap (c := (33:ℤ)) (by norm_num), EvP2_eq_cheap (c := (33:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_34 : EvP1 (34:ℤ) = EvP2 (34:ℤ) := by
  rw [EvP1_eq_cheap (c := (34:ℤ)) (by norm_num), EvP2_eq_cheap (c := (34:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_35 : EvP1 (35:ℤ) = EvP2 (35:ℤ) := by
  rw [EvP1_eq_cheap (c := (35:ℤ)) (by norm_num), EvP2_eq_cheap (c := (35:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_36 : EvP1 (36:ℤ) = EvP2 (36:ℤ) := by
  rw [EvP1_eq_cheap (c := (36:ℤ)) (by norm_num), EvP2_eq_cheap (c := (36:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_37 : EvP1 (37:ℤ) = EvP2 (37:ℤ) := by
  rw [EvP1_eq_cheap (c := (37:ℤ)) (by norm_num), EvP2_eq_cheap (c := (37:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_38 : EvP1 (38:ℤ) = EvP2 (38:ℤ) := by
  rw [EvP1_eq_cheap (c := (38:ℤ)) (by norm_num), EvP2_eq_cheap (c := (38:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_39 : EvP1 (39:ℤ) = EvP2 (39:ℤ) := by
  rw [EvP1_eq_cheap (c := (39:ℤ)) (by norm_num), EvP2_eq_cheap (c := (39:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_40 : EvP1 (40:ℤ) = EvP2 (40:ℤ) := by
  rw [EvP1_eq_cheap (c := (40:ℤ)) (by norm_num), EvP2_eq_cheap (c := (40:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_41 : EvP1 (41:ℤ) = EvP2 (41:ℤ) := by
  rw [EvP1_eq_cheap (c := (41:ℤ)) (by norm_num), EvP2_eq_cheap (c := (41:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_42 : EvP1 (42:ℤ) = EvP2 (42:ℤ) := by
  rw [EvP1_eq_cheap (c := (42:ℤ)) (by norm_num), EvP2_eq_cheap (c := (42:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_43 : EvP1 (43:ℤ) = EvP2 (43:ℤ) := by
  rw [EvP1_eq_cheap (c := (43:ℤ)) (by norm_num), EvP2_eq_cheap (c := (43:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_44 : EvP1 (44:ℤ) = EvP2 (44:ℤ) := by
  rw [EvP1_eq_cheap (c := (44:ℤ)) (by norm_num), EvP2_eq_cheap (c := (44:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_45 : EvP1 (45:ℤ) = EvP2 (45:ℤ) := by
  rw [EvP1_eq_cheap (c := (45:ℤ)) (by norm_num), EvP2_eq_cheap (c := (45:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_46 : EvP1 (46:ℤ) = EvP2 (46:ℤ) := by
  rw [EvP1_eq_cheap (c := (46:ℤ)) (by norm_num), EvP2_eq_cheap (c := (46:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_47 : EvP1 (47:ℤ) = EvP2 (47:ℤ) := by
  rw [EvP1_eq_cheap (c := (47:ℤ)) (by norm_num), EvP2_eq_cheap (c := (47:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_48 : EvP1 (48:ℤ) = EvP2 (48:ℤ) := by
  rw [EvP1_eq_cheap (c := (48:ℤ)) (by norm_num), EvP2_eq_cheap (c := (48:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_49 : EvP1 (49:ℤ) = EvP2 (49:ℤ) := by
  rw [EvP1_eq_cheap (c := (49:ℤ)) (by norm_num), EvP2_eq_cheap (c := (49:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_50 : EvP1 (50:ℤ) = EvP2 (50:ℤ) := by
  rw [EvP1_eq_cheap (c := (50:ℤ)) (by norm_num), EvP2_eq_cheap (c := (50:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_51 : EvP1 (51:ℤ) = EvP2 (51:ℤ) := by
  rw [EvP1_eq_cheap (c := (51:ℤ)) (by norm_num), EvP2_eq_cheap (c := (51:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_52 : EvP1 (52:ℤ) = EvP2 (52:ℤ) := by
  rw [EvP1_eq_cheap (c := (52:ℤ)) (by norm_num), EvP2_eq_cheap (c := (52:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_53 : EvP1 (53:ℤ) = EvP2 (53:ℤ) := by
  rw [EvP1_eq_cheap (c := (53:ℤ)) (by norm_num), EvP2_eq_cheap (c := (53:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_54 : EvP1 (54:ℤ) = EvP2 (54:ℤ) := by
  rw [EvP1_eq_cheap (c := (54:ℤ)) (by norm_num), EvP2_eq_cheap (c := (54:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_55 : EvP1 (55:ℤ) = EvP2 (55:ℤ) := by
  rw [EvP1_eq_cheap (c := (55:ℤ)) (by norm_num), EvP2_eq_cheap (c := (55:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_56 : EvP1 (56:ℤ) = EvP2 (56:ℤ) := by
  rw [EvP1_eq_cheap (c := (56:ℤ)) (by norm_num), EvP2_eq_cheap (c := (56:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_57 : EvP1 (57:ℤ) = EvP2 (57:ℤ) := by
  rw [EvP1_eq_cheap (c := (57:ℤ)) (by norm_num), EvP2_eq_cheap (c := (57:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_58 : EvP1 (58:ℤ) = EvP2 (58:ℤ) := by
  rw [EvP1_eq_cheap (c := (58:ℤ)) (by norm_num), EvP2_eq_cheap (c := (58:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_59 : EvP1 (59:ℤ) = EvP2 (59:ℤ) := by
  rw [EvP1_eq_cheap (c := (59:ℤ)) (by norm_num), EvP2_eq_cheap (c := (59:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_60 : EvP1 (60:ℤ) = EvP2 (60:ℤ) := by
  rw [EvP1_eq_cheap (c := (60:ℤ)) (by norm_num), EvP2_eq_cheap (c := (60:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_61 : EvP1 (61:ℤ) = EvP2 (61:ℤ) := by
  rw [EvP1_eq_cheap (c := (61:ℤ)) (by norm_num), EvP2_eq_cheap (c := (61:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_62 : EvP1 (62:ℤ) = EvP2 (62:ℤ) := by
  rw [EvP1_eq_cheap (c := (62:ℤ)) (by norm_num), EvP2_eq_cheap (c := (62:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_63 : EvP1 (63:ℤ) = EvP2 (63:ℤ) := by
  rw [EvP1_eq_cheap (c := (63:ℤ)) (by norm_num), EvP2_eq_cheap (c := (63:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_64 : EvP1 (64:ℤ) = EvP2 (64:ℤ) := by
  rw [EvP1_eq_cheap (c := (64:ℤ)) (by norm_num), EvP2_eq_cheap (c := (64:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_65 : EvP1 (65:ℤ) = EvP2 (65:ℤ) := by
  rw [EvP1_eq_cheap (c := (65:ℤ)) (by norm_num), EvP2_eq_cheap (c := (65:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_66 : EvP1 (66:ℤ) = EvP2 (66:ℤ) := by
  rw [EvP1_eq_cheap (c := (66:ℤ)) (by norm_num), EvP2_eq_cheap (c := (66:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_67 : EvP1 (67:ℤ) = EvP2 (67:ℤ) := by
  rw [EvP1_eq_cheap (c := (67:ℤ)) (by norm_num), EvP2_eq_cheap (c := (67:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_68 : EvP1 (68:ℤ) = EvP2 (68:ℤ) := by
  rw [EvP1_eq_cheap (c := (68:ℤ)) (by norm_num), EvP2_eq_cheap (c := (68:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_69 : EvP1 (69:ℤ) = EvP2 (69:ℤ) := by
  rw [EvP1_eq_cheap (c := (69:ℤ)) (by norm_num), EvP2_eq_cheap (c := (69:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_70 : EvP1 (70:ℤ) = EvP2 (70:ℤ) := by
  rw [EvP1_eq_cheap (c := (70:ℤ)) (by norm_num), EvP2_eq_cheap (c := (70:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_71 : EvP1 (71:ℤ) = EvP2 (71:ℤ) := by
  rw [EvP1_eq_cheap (c := (71:ℤ)) (by norm_num), EvP2_eq_cheap (c := (71:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_72 : EvP1 (72:ℤ) = EvP2 (72:ℤ) := by
  rw [EvP1_eq_cheap (c := (72:ℤ)) (by norm_num), EvP2_eq_cheap (c := (72:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_73 : EvP1 (73:ℤ) = EvP2 (73:ℤ) := by
  rw [EvP1_eq_cheap (c := (73:ℤ)) (by norm_num), EvP2_eq_cheap (c := (73:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_74 : EvP1 (74:ℤ) = EvP2 (74:ℤ) := by
  rw [EvP1_eq_cheap (c := (74:ℤ)) (by norm_num), EvP2_eq_cheap (c := (74:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_75 : EvP1 (75:ℤ) = EvP2 (75:ℤ) := by
  rw [EvP1_eq_cheap (c := (75:ℤ)) (by norm_num), EvP2_eq_cheap (c := (75:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_76 : EvP1 (76:ℤ) = EvP2 (76:ℤ) := by
  rw [EvP1_eq_cheap (c := (76:ℤ)) (by norm_num), EvP2_eq_cheap (c := (76:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_77 : EvP1 (77:ℤ) = EvP2 (77:ℤ) := by
  rw [EvP1_eq_cheap (c := (77:ℤ)) (by norm_num), EvP2_eq_cheap (c := (77:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_78 : EvP1 (78:ℤ) = EvP2 (78:ℤ) := by
  rw [EvP1_eq_cheap (c := (78:ℤ)) (by norm_num), EvP2_eq_cheap (c := (78:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_79 : EvP1 (79:ℤ) = EvP2 (79:ℤ) := by
  rw [EvP1_eq_cheap (c := (79:ℤ)) (by norm_num), EvP2_eq_cheap (c := (79:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_80 : EvP1 (80:ℤ) = EvP2 (80:ℤ) := by
  rw [EvP1_eq_cheap (c := (80:ℤ)) (by norm_num), EvP2_eq_cheap (c := (80:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_81 : EvP1 (81:ℤ) = EvP2 (81:ℤ) := by
  rw [EvP1_eq_cheap (c := (81:ℤ)) (by norm_num), EvP2_eq_cheap (c := (81:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_82 : EvP1 (82:ℤ) = EvP2 (82:ℤ) := by
  rw [EvP1_eq_cheap (c := (82:ℤ)) (by norm_num), EvP2_eq_cheap (c := (82:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_83 : EvP1 (83:ℤ) = EvP2 (83:ℤ) := by
  rw [EvP1_eq_cheap (c := (83:ℤ)) (by norm_num), EvP2_eq_cheap (c := (83:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_84 : EvP1 (84:ℤ) = EvP2 (84:ℤ) := by
  rw [EvP1_eq_cheap (c := (84:ℤ)) (by norm_num), EvP2_eq_cheap (c := (84:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_85 : EvP1 (85:ℤ) = EvP2 (85:ℤ) := by
  rw [EvP1_eq_cheap (c := (85:ℤ)) (by norm_num), EvP2_eq_cheap (c := (85:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_86 : EvP1 (86:ℤ) = EvP2 (86:ℤ) := by
  rw [EvP1_eq_cheap (c := (86:ℤ)) (by norm_num), EvP2_eq_cheap (c := (86:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_87 : EvP1 (87:ℤ) = EvP2 (87:ℤ) := by
  rw [EvP1_eq_cheap (c := (87:ℤ)) (by norm_num), EvP2_eq_cheap (c := (87:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_88 : EvP1 (88:ℤ) = EvP2 (88:ℤ) := by
  rw [EvP1_eq_cheap (c := (88:ℤ)) (by norm_num), EvP2_eq_cheap (c := (88:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_89 : EvP1 (89:ℤ) = EvP2 (89:ℤ) := by
  rw [EvP1_eq_cheap (c := (89:ℤ)) (by norm_num), EvP2_eq_cheap (c := (89:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_90 : EvP1 (90:ℤ) = EvP2 (90:ℤ) := by
  rw [EvP1_eq_cheap (c := (90:ℤ)) (by norm_num), EvP2_eq_cheap (c := (90:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_91 : EvP1 (91:ℤ) = EvP2 (91:ℤ) := by
  rw [EvP1_eq_cheap (c := (91:ℤ)) (by norm_num), EvP2_eq_cheap (c := (91:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_92 : EvP1 (92:ℤ) = EvP2 (92:ℤ) := by
  rw [EvP1_eq_cheap (c := (92:ℤ)) (by norm_num), EvP2_eq_cheap (c := (92:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_93 : EvP1 (93:ℤ) = EvP2 (93:ℤ) := by
  rw [EvP1_eq_cheap (c := (93:ℤ)) (by norm_num), EvP2_eq_cheap (c := (93:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_94 : EvP1 (94:ℤ) = EvP2 (94:ℤ) := by
  rw [EvP1_eq_cheap (c := (94:ℤ)) (by norm_num), EvP2_eq_cheap (c := (94:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_95 : EvP1 (95:ℤ) = EvP2 (95:ℤ) := by
  rw [EvP1_eq_cheap (c := (95:ℤ)) (by norm_num), EvP2_eq_cheap (c := (95:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_96 : EvP1 (96:ℤ) = EvP2 (96:ℤ) := by
  rw [EvP1_eq_cheap (c := (96:ℤ)) (by norm_num), EvP2_eq_cheap (c := (96:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_97 : EvP1 (97:ℤ) = EvP2 (97:ℤ) := by
  rw [EvP1_eq_cheap (c := (97:ℤ)) (by norm_num), EvP2_eq_cheap (c := (97:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_98 : EvP1 (98:ℤ) = EvP2 (98:ℤ) := by
  rw [EvP1_eq_cheap (c := (98:ℤ)) (by norm_num), EvP2_eq_cheap (c := (98:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_99 : EvP1 (99:ℤ) = EvP2 (99:ℤ) := by
  rw [EvP1_eq_cheap (c := (99:ℤ)) (by norm_num), EvP2_eq_cheap (c := (99:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_100 : EvP1 (100:ℤ) = EvP2 (100:ℤ) := by
  rw [EvP1_eq_cheap (c := (100:ℤ)) (by norm_num), EvP2_eq_cheap (c := (100:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_101 : EvP1 (101:ℤ) = EvP2 (101:ℤ) := by
  rw [EvP1_eq_cheap (c := (101:ℤ)) (by norm_num), EvP2_eq_cheap (c := (101:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_102 : EvP1 (102:ℤ) = EvP2 (102:ℤ) := by
  rw [EvP1_eq_cheap (c := (102:ℤ)) (by norm_num), EvP2_eq_cheap (c := (102:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_103 : EvP1 (103:ℤ) = EvP2 (103:ℤ) := by
  rw [EvP1_eq_cheap (c := (103:ℤ)) (by norm_num), EvP2_eq_cheap (c := (103:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_104 : EvP1 (104:ℤ) = EvP2 (104:ℤ) := by
  rw [EvP1_eq_cheap (c := (104:ℤ)) (by norm_num), EvP2_eq_cheap (c := (104:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_105 : EvP1 (105:ℤ) = EvP2 (105:ℤ) := by
  rw [EvP1_eq_cheap (c := (105:ℤ)) (by norm_num), EvP2_eq_cheap (c := (105:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_106 : EvP1 (106:ℤ) = EvP2 (106:ℤ) := by
  rw [EvP1_eq_cheap (c := (106:ℤ)) (by norm_num), EvP2_eq_cheap (c := (106:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_107 : EvP1 (107:ℤ) = EvP2 (107:ℤ) := by
  rw [EvP1_eq_cheap (c := (107:ℤ)) (by norm_num), EvP2_eq_cheap (c := (107:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_108 : EvP1 (108:ℤ) = EvP2 (108:ℤ) := by
  rw [EvP1_eq_cheap (c := (108:ℤ)) (by norm_num), EvP2_eq_cheap (c := (108:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_109 : EvP1 (109:ℤ) = EvP2 (109:ℤ) := by
  rw [EvP1_eq_cheap (c := (109:ℤ)) (by norm_num), EvP2_eq_cheap (c := (109:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_110 : EvP1 (110:ℤ) = EvP2 (110:ℤ) := by
  rw [EvP1_eq_cheap (c := (110:ℤ)) (by norm_num), EvP2_eq_cheap (c := (110:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_111 : EvP1 (111:ℤ) = EvP2 (111:ℤ) := by
  rw [EvP1_eq_cheap (c := (111:ℤ)) (by norm_num), EvP2_eq_cheap (c := (111:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_112 : EvP1 (112:ℤ) = EvP2 (112:ℤ) := by
  rw [EvP1_eq_cheap (c := (112:ℤ)) (by norm_num), EvP2_eq_cheap (c := (112:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_113 : EvP1 (113:ℤ) = EvP2 (113:ℤ) := by
  rw [EvP1_eq_cheap (c := (113:ℤ)) (by norm_num), EvP2_eq_cheap (c := (113:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_114 : EvP1 (114:ℤ) = EvP2 (114:ℤ) := by
  rw [EvP1_eq_cheap (c := (114:ℤ)) (by norm_num), EvP2_eq_cheap (c := (114:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_115 : EvP1 (115:ℤ) = EvP2 (115:ℤ) := by
  rw [EvP1_eq_cheap (c := (115:ℤ)) (by norm_num), EvP2_eq_cheap (c := (115:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_116 : EvP1 (116:ℤ) = EvP2 (116:ℤ) := by
  rw [EvP1_eq_cheap (c := (116:ℤ)) (by norm_num), EvP2_eq_cheap (c := (116:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_117 : EvP1 (117:ℤ) = EvP2 (117:ℤ) := by
  rw [EvP1_eq_cheap (c := (117:ℤ)) (by norm_num), EvP2_eq_cheap (c := (117:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_118 : EvP1 (118:ℤ) = EvP2 (118:ℤ) := by
  rw [EvP1_eq_cheap (c := (118:ℤ)) (by norm_num), EvP2_eq_cheap (c := (118:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_119 : EvP1 (119:ℤ) = EvP2 (119:ℤ) := by
  rw [EvP1_eq_cheap (c := (119:ℤ)) (by norm_num), EvP2_eq_cheap (c := (119:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_120 : EvP1 (120:ℤ) = EvP2 (120:ℤ) := by
  rw [EvP1_eq_cheap (c := (120:ℤ)) (by norm_num), EvP2_eq_cheap (c := (120:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_121 : EvP1 (121:ℤ) = EvP2 (121:ℤ) := by
  rw [EvP1_eq_cheap (c := (121:ℤ)) (by norm_num), EvP2_eq_cheap (c := (121:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_122 : EvP1 (122:ℤ) = EvP2 (122:ℤ) := by
  rw [EvP1_eq_cheap (c := (122:ℤ)) (by norm_num), EvP2_eq_cheap (c := (122:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_123 : EvP1 (123:ℤ) = EvP2 (123:ℤ) := by
  rw [EvP1_eq_cheap (c := (123:ℤ)) (by norm_num), EvP2_eq_cheap (c := (123:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_124 : EvP1 (124:ℤ) = EvP2 (124:ℤ) := by
  rw [EvP1_eq_cheap (c := (124:ℤ)) (by norm_num), EvP2_eq_cheap (c := (124:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_125 : EvP1 (125:ℤ) = EvP2 (125:ℤ) := by
  rw [EvP1_eq_cheap (c := (125:ℤ)) (by norm_num), EvP2_eq_cheap (c := (125:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_126 : EvP1 (126:ℤ) = EvP2 (126:ℤ) := by
  rw [EvP1_eq_cheap (c := (126:ℤ)) (by norm_num), EvP2_eq_cheap (c := (126:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_127 : EvP1 (127:ℤ) = EvP2 (127:ℤ) := by
  rw [EvP1_eq_cheap (c := (127:ℤ)) (by norm_num), EvP2_eq_cheap (c := (127:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_128 : EvP1 (128:ℤ) = EvP2 (128:ℤ) := by
  rw [EvP1_eq_cheap (c := (128:ℤ)) (by norm_num), EvP2_eq_cheap (c := (128:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_129 : EvP1 (129:ℤ) = EvP2 (129:ℤ) := by
  rw [EvP1_eq_cheap (c := (129:ℤ)) (by norm_num), EvP2_eq_cheap (c := (129:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_130 : EvP1 (130:ℤ) = EvP2 (130:ℤ) := by
  rw [EvP1_eq_cheap (c := (130:ℤ)) (by norm_num), EvP2_eq_cheap (c := (130:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_131 : EvP1 (131:ℤ) = EvP2 (131:ℤ) := by
  rw [EvP1_eq_cheap (c := (131:ℤ)) (by norm_num), EvP2_eq_cheap (c := (131:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_132 : EvP1 (132:ℤ) = EvP2 (132:ℤ) := by
  rw [EvP1_eq_cheap (c := (132:ℤ)) (by norm_num), EvP2_eq_cheap (c := (132:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_133 : EvP1 (133:ℤ) = EvP2 (133:ℤ) := by
  rw [EvP1_eq_cheap (c := (133:ℤ)) (by norm_num), EvP2_eq_cheap (c := (133:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_134 : EvP1 (134:ℤ) = EvP2 (134:ℤ) := by
  rw [EvP1_eq_cheap (c := (134:ℤ)) (by norm_num), EvP2_eq_cheap (c := (134:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_135 : EvP1 (135:ℤ) = EvP2 (135:ℤ) := by
  rw [EvP1_eq_cheap (c := (135:ℤ)) (by norm_num), EvP2_eq_cheap (c := (135:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_136 : EvP1 (136:ℤ) = EvP2 (136:ℤ) := by
  rw [EvP1_eq_cheap (c := (136:ℤ)) (by norm_num), EvP2_eq_cheap (c := (136:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_137 : EvP1 (137:ℤ) = EvP2 (137:ℤ) := by
  rw [EvP1_eq_cheap (c := (137:ℤ)) (by norm_num), EvP2_eq_cheap (c := (137:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_138 : EvP1 (138:ℤ) = EvP2 (138:ℤ) := by
  rw [EvP1_eq_cheap (c := (138:ℤ)) (by norm_num), EvP2_eq_cheap (c := (138:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_139 : EvP1 (139:ℤ) = EvP2 (139:ℤ) := by
  rw [EvP1_eq_cheap (c := (139:ℤ)) (by norm_num), EvP2_eq_cheap (c := (139:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_140 : EvP1 (140:ℤ) = EvP2 (140:ℤ) := by
  rw [EvP1_eq_cheap (c := (140:ℤ)) (by norm_num), EvP2_eq_cheap (c := (140:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_141 : EvP1 (141:ℤ) = EvP2 (141:ℤ) := by
  rw [EvP1_eq_cheap (c := (141:ℤ)) (by norm_num), EvP2_eq_cheap (c := (141:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_142 : EvP1 (142:ℤ) = EvP2 (142:ℤ) := by
  rw [EvP1_eq_cheap (c := (142:ℤ)) (by norm_num), EvP2_eq_cheap (c := (142:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_143 : EvP1 (143:ℤ) = EvP2 (143:ℤ) := by
  rw [EvP1_eq_cheap (c := (143:ℤ)) (by norm_num), EvP2_eq_cheap (c := (143:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_144 : EvP1 (144:ℤ) = EvP2 (144:ℤ) := by
  rw [EvP1_eq_cheap (c := (144:ℤ)) (by norm_num), EvP2_eq_cheap (c := (144:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_145 : EvP1 (145:ℤ) = EvP2 (145:ℤ) := by
  rw [EvP1_eq_cheap (c := (145:ℤ)) (by norm_num), EvP2_eq_cheap (c := (145:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_146 : EvP1 (146:ℤ) = EvP2 (146:ℤ) := by
  rw [EvP1_eq_cheap (c := (146:ℤ)) (by norm_num), EvP2_eq_cheap (c := (146:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_147 : EvP1 (147:ℤ) = EvP2 (147:ℤ) := by
  rw [EvP1_eq_cheap (c := (147:ℤ)) (by norm_num), EvP2_eq_cheap (c := (147:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_148 : EvP1 (148:ℤ) = EvP2 (148:ℤ) := by
  rw [EvP1_eq_cheap (c := (148:ℤ)) (by norm_num), EvP2_eq_cheap (c := (148:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_149 : EvP1 (149:ℤ) = EvP2 (149:ℤ) := by
  rw [EvP1_eq_cheap (c := (149:ℤ)) (by norm_num), EvP2_eq_cheap (c := (149:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_150 : EvP1 (150:ℤ) = EvP2 (150:ℤ) := by
  rw [EvP1_eq_cheap (c := (150:ℤ)) (by norm_num), EvP2_eq_cheap (c := (150:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_151 : EvP1 (151:ℤ) = EvP2 (151:ℤ) := by
  rw [EvP1_eq_cheap (c := (151:ℤ)) (by norm_num), EvP2_eq_cheap (c := (151:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_152 : EvP1 (152:ℤ) = EvP2 (152:ℤ) := by
  rw [EvP1_eq_cheap (c := (152:ℤ)) (by norm_num), EvP2_eq_cheap (c := (152:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_153 : EvP1 (153:ℤ) = EvP2 (153:ℤ) := by
  rw [EvP1_eq_cheap (c := (153:ℤ)) (by norm_num), EvP2_eq_cheap (c := (153:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_154 : EvP1 (154:ℤ) = EvP2 (154:ℤ) := by
  rw [EvP1_eq_cheap (c := (154:ℤ)) (by norm_num), EvP2_eq_cheap (c := (154:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_155 : EvP1 (155:ℤ) = EvP2 (155:ℤ) := by
  rw [EvP1_eq_cheap (c := (155:ℤ)) (by norm_num), EvP2_eq_cheap (c := (155:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_156 : EvP1 (156:ℤ) = EvP2 (156:ℤ) := by
  rw [EvP1_eq_cheap (c := (156:ℤ)) (by norm_num), EvP2_eq_cheap (c := (156:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_157 : EvP1 (157:ℤ) = EvP2 (157:ℤ) := by
  rw [EvP1_eq_cheap (c := (157:ℤ)) (by norm_num), EvP2_eq_cheap (c := (157:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_158 : EvP1 (158:ℤ) = EvP2 (158:ℤ) := by
  rw [EvP1_eq_cheap (c := (158:ℤ)) (by norm_num), EvP2_eq_cheap (c := (158:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_159 : EvP1 (159:ℤ) = EvP2 (159:ℤ) := by
  rw [EvP1_eq_cheap (c := (159:ℤ)) (by norm_num), EvP2_eq_cheap (c := (159:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_160 : EvP1 (160:ℤ) = EvP2 (160:ℤ) := by
  rw [EvP1_eq_cheap (c := (160:ℤ)) (by norm_num), EvP2_eq_cheap (c := (160:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_161 : EvP1 (161:ℤ) = EvP2 (161:ℤ) := by
  rw [EvP1_eq_cheap (c := (161:ℤ)) (by norm_num), EvP2_eq_cheap (c := (161:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_162 : EvP1 (162:ℤ) = EvP2 (162:ℤ) := by
  rw [EvP1_eq_cheap (c := (162:ℤ)) (by norm_num), EvP2_eq_cheap (c := (162:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_163 : EvP1 (163:ℤ) = EvP2 (163:ℤ) := by
  rw [EvP1_eq_cheap (c := (163:ℤ)) (by norm_num), EvP2_eq_cheap (c := (163:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_164 : EvP1 (164:ℤ) = EvP2 (164:ℤ) := by
  rw [EvP1_eq_cheap (c := (164:ℤ)) (by norm_num), EvP2_eq_cheap (c := (164:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_165 : EvP1 (165:ℤ) = EvP2 (165:ℤ) := by
  rw [EvP1_eq_cheap (c := (165:ℤ)) (by norm_num), EvP2_eq_cheap (c := (165:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_166 : EvP1 (166:ℤ) = EvP2 (166:ℤ) := by
  rw [EvP1_eq_cheap (c := (166:ℤ)) (by norm_num), EvP2_eq_cheap (c := (166:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_167 : EvP1 (167:ℤ) = EvP2 (167:ℤ) := by
  rw [EvP1_eq_cheap (c := (167:ℤ)) (by norm_num), EvP2_eq_cheap (c := (167:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_168 : EvP1 (168:ℤ) = EvP2 (168:ℤ) := by
  rw [EvP1_eq_cheap (c := (168:ℤ)) (by norm_num), EvP2_eq_cheap (c := (168:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_169 : EvP1 (169:ℤ) = EvP2 (169:ℤ) := by
  rw [EvP1_eq_cheap (c := (169:ℤ)) (by norm_num), EvP2_eq_cheap (c := (169:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_170 : EvP1 (170:ℤ) = EvP2 (170:ℤ) := by
  rw [EvP1_eq_cheap (c := (170:ℤ)) (by norm_num), EvP2_eq_cheap (c := (170:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_171 : EvP1 (171:ℤ) = EvP2 (171:ℤ) := by
  rw [EvP1_eq_cheap (c := (171:ℤ)) (by norm_num), EvP2_eq_cheap (c := (171:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_172 : EvP1 (172:ℤ) = EvP2 (172:ℤ) := by
  rw [EvP1_eq_cheap (c := (172:ℤ)) (by norm_num), EvP2_eq_cheap (c := (172:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_173 : EvP1 (173:ℤ) = EvP2 (173:ℤ) := by
  rw [EvP1_eq_cheap (c := (173:ℤ)) (by norm_num), EvP2_eq_cheap (c := (173:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_174 : EvP1 (174:ℤ) = EvP2 (174:ℤ) := by
  rw [EvP1_eq_cheap (c := (174:ℤ)) (by norm_num), EvP2_eq_cheap (c := (174:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_175 : EvP1 (175:ℤ) = EvP2 (175:ℤ) := by
  rw [EvP1_eq_cheap (c := (175:ℤ)) (by norm_num), EvP2_eq_cheap (c := (175:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_176 : EvP1 (176:ℤ) = EvP2 (176:ℤ) := by
  rw [EvP1_eq_cheap (c := (176:ℤ)) (by norm_num), EvP2_eq_cheap (c := (176:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_177 : EvP1 (177:ℤ) = EvP2 (177:ℤ) := by
  rw [EvP1_eq_cheap (c := (177:ℤ)) (by norm_num), EvP2_eq_cheap (c := (177:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_178 : EvP1 (178:ℤ) = EvP2 (178:ℤ) := by
  rw [EvP1_eq_cheap (c := (178:ℤ)) (by norm_num), EvP2_eq_cheap (c := (178:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_179 : EvP1 (179:ℤ) = EvP2 (179:ℤ) := by
  rw [EvP1_eq_cheap (c := (179:ℤ)) (by norm_num), EvP2_eq_cheap (c := (179:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_180 : EvP1 (180:ℤ) = EvP2 (180:ℤ) := by
  rw [EvP1_eq_cheap (c := (180:ℤ)) (by norm_num), EvP2_eq_cheap (c := (180:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_181 : EvP1 (181:ℤ) = EvP2 (181:ℤ) := by
  rw [EvP1_eq_cheap (c := (181:ℤ)) (by norm_num), EvP2_eq_cheap (c := (181:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_182 : EvP1 (182:ℤ) = EvP2 (182:ℤ) := by
  rw [EvP1_eq_cheap (c := (182:ℤ)) (by norm_num), EvP2_eq_cheap (c := (182:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_183 : EvP1 (183:ℤ) = EvP2 (183:ℤ) := by
  rw [EvP1_eq_cheap (c := (183:ℤ)) (by norm_num), EvP2_eq_cheap (c := (183:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_184 : EvP1 (184:ℤ) = EvP2 (184:ℤ) := by
  rw [EvP1_eq_cheap (c := (184:ℤ)) (by norm_num), EvP2_eq_cheap (c := (184:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_185 : EvP1 (185:ℤ) = EvP2 (185:ℤ) := by
  rw [EvP1_eq_cheap (c := (185:ℤ)) (by norm_num), EvP2_eq_cheap (c := (185:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_186 : EvP1 (186:ℤ) = EvP2 (186:ℤ) := by
  rw [EvP1_eq_cheap (c := (186:ℤ)) (by norm_num), EvP2_eq_cheap (c := (186:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_187 : EvP1 (187:ℤ) = EvP2 (187:ℤ) := by
  rw [EvP1_eq_cheap (c := (187:ℤ)) (by norm_num), EvP2_eq_cheap (c := (187:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_188 : EvP1 (188:ℤ) = EvP2 (188:ℤ) := by
  rw [EvP1_eq_cheap (c := (188:ℤ)) (by norm_num), EvP2_eq_cheap (c := (188:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_189 : EvP1 (189:ℤ) = EvP2 (189:ℤ) := by
  rw [EvP1_eq_cheap (c := (189:ℤ)) (by norm_num), EvP2_eq_cheap (c := (189:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_190 : EvP1 (190:ℤ) = EvP2 (190:ℤ) := by
  rw [EvP1_eq_cheap (c := (190:ℤ)) (by norm_num), EvP2_eq_cheap (c := (190:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_191 : EvP1 (191:ℤ) = EvP2 (191:ℤ) := by
  rw [EvP1_eq_cheap (c := (191:ℤ)) (by norm_num), EvP2_eq_cheap (c := (191:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_192 : EvP1 (192:ℤ) = EvP2 (192:ℤ) := by
  rw [EvP1_eq_cheap (c := (192:ℤ)) (by norm_num), EvP2_eq_cheap (c := (192:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_193 : EvP1 (193:ℤ) = EvP2 (193:ℤ) := by
  rw [EvP1_eq_cheap (c := (193:ℤ)) (by norm_num), EvP2_eq_cheap (c := (193:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_194 : EvP1 (194:ℤ) = EvP2 (194:ℤ) := by
  rw [EvP1_eq_cheap (c := (194:ℤ)) (by norm_num), EvP2_eq_cheap (c := (194:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_195 : EvP1 (195:ℤ) = EvP2 (195:ℤ) := by
  rw [EvP1_eq_cheap (c := (195:ℤ)) (by norm_num), EvP2_eq_cheap (c := (195:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_196 : EvP1 (196:ℤ) = EvP2 (196:ℤ) := by
  rw [EvP1_eq_cheap (c := (196:ℤ)) (by norm_num), EvP2_eq_cheap (c := (196:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_197 : EvP1 (197:ℤ) = EvP2 (197:ℤ) := by
  rw [EvP1_eq_cheap (c := (197:ℤ)) (by norm_num), EvP2_eq_cheap (c := (197:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_198 : EvP1 (198:ℤ) = EvP2 (198:ℤ) := by
  rw [EvP1_eq_cheap (c := (198:ℤ)) (by norm_num), EvP2_eq_cheap (c := (198:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_199 : EvP1 (199:ℤ) = EvP2 (199:ℤ) := by
  rw [EvP1_eq_cheap (c := (199:ℤ)) (by norm_num), EvP2_eq_cheap (c := (199:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_200 : EvP1 (200:ℤ) = EvP2 (200:ℤ) := by
  rw [EvP1_eq_cheap (c := (200:ℤ)) (by norm_num), EvP2_eq_cheap (c := (200:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_201 : EvP1 (201:ℤ) = EvP2 (201:ℤ) := by
  rw [EvP1_eq_cheap (c := (201:ℤ)) (by norm_num), EvP2_eq_cheap (c := (201:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_202 : EvP1 (202:ℤ) = EvP2 (202:ℤ) := by
  rw [EvP1_eq_cheap (c := (202:ℤ)) (by norm_num), EvP2_eq_cheap (c := (202:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_203 : EvP1 (203:ℤ) = EvP2 (203:ℤ) := by
  rw [EvP1_eq_cheap (c := (203:ℤ)) (by norm_num), EvP2_eq_cheap (c := (203:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_204 : EvP1 (204:ℤ) = EvP2 (204:ℤ) := by
  rw [EvP1_eq_cheap (c := (204:ℤ)) (by norm_num), EvP2_eq_cheap (c := (204:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_205 : EvP1 (205:ℤ) = EvP2 (205:ℤ) := by
  rw [EvP1_eq_cheap (c := (205:ℤ)) (by norm_num), EvP2_eq_cheap (c := (205:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_206 : EvP1 (206:ℤ) = EvP2 (206:ℤ) := by
  rw [EvP1_eq_cheap (c := (206:ℤ)) (by norm_num), EvP2_eq_cheap (c := (206:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_207 : EvP1 (207:ℤ) = EvP2 (207:ℤ) := by
  rw [EvP1_eq_cheap (c := (207:ℤ)) (by norm_num), EvP2_eq_cheap (c := (207:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_208 : EvP1 (208:ℤ) = EvP2 (208:ℤ) := by
  rw [EvP1_eq_cheap (c := (208:ℤ)) (by norm_num), EvP2_eq_cheap (c := (208:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_209 : EvP1 (209:ℤ) = EvP2 (209:ℤ) := by
  rw [EvP1_eq_cheap (c := (209:ℤ)) (by norm_num), EvP2_eq_cheap (c := (209:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_210 : EvP1 (210:ℤ) = EvP2 (210:ℤ) := by
  rw [EvP1_eq_cheap (c := (210:ℤ)) (by norm_num), EvP2_eq_cheap (c := (210:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_211 : EvP1 (211:ℤ) = EvP2 (211:ℤ) := by
  rw [EvP1_eq_cheap (c := (211:ℤ)) (by norm_num), EvP2_eq_cheap (c := (211:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_212 : EvP1 (212:ℤ) = EvP2 (212:ℤ) := by
  rw [EvP1_eq_cheap (c := (212:ℤ)) (by norm_num), EvP2_eq_cheap (c := (212:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_213 : EvP1 (213:ℤ) = EvP2 (213:ℤ) := by
  rw [EvP1_eq_cheap (c := (213:ℤ)) (by norm_num), EvP2_eq_cheap (c := (213:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_214 : EvP1 (214:ℤ) = EvP2 (214:ℤ) := by
  rw [EvP1_eq_cheap (c := (214:ℤ)) (by norm_num), EvP2_eq_cheap (c := (214:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_215 : EvP1 (215:ℤ) = EvP2 (215:ℤ) := by
  rw [EvP1_eq_cheap (c := (215:ℤ)) (by norm_num), EvP2_eq_cheap (c := (215:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_216 : EvP1 (216:ℤ) = EvP2 (216:ℤ) := by
  rw [EvP1_eq_cheap (c := (216:ℤ)) (by norm_num), EvP2_eq_cheap (c := (216:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_217 : EvP1 (217:ℤ) = EvP2 (217:ℤ) := by
  rw [EvP1_eq_cheap (c := (217:ℤ)) (by norm_num), EvP2_eq_cheap (c := (217:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_218 : EvP1 (218:ℤ) = EvP2 (218:ℤ) := by
  rw [EvP1_eq_cheap (c := (218:ℤ)) (by norm_num), EvP2_eq_cheap (c := (218:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_219 : EvP1 (219:ℤ) = EvP2 (219:ℤ) := by
  rw [EvP1_eq_cheap (c := (219:ℤ)) (by norm_num), EvP2_eq_cheap (c := (219:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_220 : EvP1 (220:ℤ) = EvP2 (220:ℤ) := by
  rw [EvP1_eq_cheap (c := (220:ℤ)) (by norm_num), EvP2_eq_cheap (c := (220:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_221 : EvP1 (221:ℤ) = EvP2 (221:ℤ) := by
  rw [EvP1_eq_cheap (c := (221:ℤ)) (by norm_num), EvP2_eq_cheap (c := (221:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_222 : EvP1 (222:ℤ) = EvP2 (222:ℤ) := by
  rw [EvP1_eq_cheap (c := (222:ℤ)) (by norm_num), EvP2_eq_cheap (c := (222:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_223 : EvP1 (223:ℤ) = EvP2 (223:ℤ) := by
  rw [EvP1_eq_cheap (c := (223:ℤ)) (by norm_num), EvP2_eq_cheap (c := (223:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_224 : EvP1 (224:ℤ) = EvP2 (224:ℤ) := by
  rw [EvP1_eq_cheap (c := (224:ℤ)) (by norm_num), EvP2_eq_cheap (c := (224:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_225 : EvP1 (225:ℤ) = EvP2 (225:ℤ) := by
  rw [EvP1_eq_cheap (c := (225:ℤ)) (by norm_num), EvP2_eq_cheap (c := (225:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_226 : EvP1 (226:ℤ) = EvP2 (226:ℤ) := by
  rw [EvP1_eq_cheap (c := (226:ℤ)) (by norm_num), EvP2_eq_cheap (c := (226:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_227 : EvP1 (227:ℤ) = EvP2 (227:ℤ) := by
  rw [EvP1_eq_cheap (c := (227:ℤ)) (by norm_num), EvP2_eq_cheap (c := (227:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_228 : EvP1 (228:ℤ) = EvP2 (228:ℤ) := by
  rw [EvP1_eq_cheap (c := (228:ℤ)) (by norm_num), EvP2_eq_cheap (c := (228:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_229 : EvP1 (229:ℤ) = EvP2 (229:ℤ) := by
  rw [EvP1_eq_cheap (c := (229:ℤ)) (by norm_num), EvP2_eq_cheap (c := (229:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_230 : EvP1 (230:ℤ) = EvP2 (230:ℤ) := by
  rw [EvP1_eq_cheap (c := (230:ℤ)) (by norm_num), EvP2_eq_cheap (c := (230:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_231 : EvP1 (231:ℤ) = EvP2 (231:ℤ) := by
  rw [EvP1_eq_cheap (c := (231:ℤ)) (by norm_num), EvP2_eq_cheap (c := (231:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_232 : EvP1 (232:ℤ) = EvP2 (232:ℤ) := by
  rw [EvP1_eq_cheap (c := (232:ℤ)) (by norm_num), EvP2_eq_cheap (c := (232:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_233 : EvP1 (233:ℤ) = EvP2 (233:ℤ) := by
  rw [EvP1_eq_cheap (c := (233:ℤ)) (by norm_num), EvP2_eq_cheap (c := (233:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_234 : EvP1 (234:ℤ) = EvP2 (234:ℤ) := by
  rw [EvP1_eq_cheap (c := (234:ℤ)) (by norm_num), EvP2_eq_cheap (c := (234:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_235 : EvP1 (235:ℤ) = EvP2 (235:ℤ) := by
  rw [EvP1_eq_cheap (c := (235:ℤ)) (by norm_num), EvP2_eq_cheap (c := (235:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_236 : EvP1 (236:ℤ) = EvP2 (236:ℤ) := by
  rw [EvP1_eq_cheap (c := (236:ℤ)) (by norm_num), EvP2_eq_cheap (c := (236:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_237 : EvP1 (237:ℤ) = EvP2 (237:ℤ) := by
  rw [EvP1_eq_cheap (c := (237:ℤ)) (by norm_num), EvP2_eq_cheap (c := (237:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_238 : EvP1 (238:ℤ) = EvP2 (238:ℤ) := by
  rw [EvP1_eq_cheap (c := (238:ℤ)) (by norm_num), EvP2_eq_cheap (c := (238:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_239 : EvP1 (239:ℤ) = EvP2 (239:ℤ) := by
  rw [EvP1_eq_cheap (c := (239:ℤ)) (by norm_num), EvP2_eq_cheap (c := (239:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_240 : EvP1 (240:ℤ) = EvP2 (240:ℤ) := by
  rw [EvP1_eq_cheap (c := (240:ℤ)) (by norm_num), EvP2_eq_cheap (c := (240:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_241 : EvP1 (241:ℤ) = EvP2 (241:ℤ) := by
  rw [EvP1_eq_cheap (c := (241:ℤ)) (by norm_num), EvP2_eq_cheap (c := (241:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_242 : EvP1 (242:ℤ) = EvP2 (242:ℤ) := by
  rw [EvP1_eq_cheap (c := (242:ℤ)) (by norm_num), EvP2_eq_cheap (c := (242:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_243 : EvP1 (243:ℤ) = EvP2 (243:ℤ) := by
  rw [EvP1_eq_cheap (c := (243:ℤ)) (by norm_num), EvP2_eq_cheap (c := (243:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_244 : EvP1 (244:ℤ) = EvP2 (244:ℤ) := by
  rw [EvP1_eq_cheap (c := (244:ℤ)) (by norm_num), EvP2_eq_cheap (c := (244:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_245 : EvP1 (245:ℤ) = EvP2 (245:ℤ) := by
  rw [EvP1_eq_cheap (c := (245:ℤ)) (by norm_num), EvP2_eq_cheap (c := (245:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_246 : EvP1 (246:ℤ) = EvP2 (246:ℤ) := by
  rw [EvP1_eq_cheap (c := (246:ℤ)) (by norm_num), EvP2_eq_cheap (c := (246:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_247 : EvP1 (247:ℤ) = EvP2 (247:ℤ) := by
  rw [EvP1_eq_cheap (c := (247:ℤ)) (by norm_num), EvP2_eq_cheap (c := (247:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_248 : EvP1 (248:ℤ) = EvP2 (248:ℤ) := by
  rw [EvP1_eq_cheap (c := (248:ℤ)) (by norm_num), EvP2_eq_cheap (c := (248:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_249 : EvP1 (249:ℤ) = EvP2 (249:ℤ) := by
  rw [EvP1_eq_cheap (c := (249:ℤ)) (by norm_num), EvP2_eq_cheap (c := (249:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_250 : EvP1 (250:ℤ) = EvP2 (250:ℤ) := by
  rw [EvP1_eq_cheap (c := (250:ℤ)) (by norm_num), EvP2_eq_cheap (c := (250:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_251 : EvP1 (251:ℤ) = EvP2 (251:ℤ) := by
  rw [EvP1_eq_cheap (c := (251:ℤ)) (by norm_num), EvP2_eq_cheap (c := (251:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_252 : EvP1 (252:ℤ) = EvP2 (252:ℤ) := by
  rw [EvP1_eq_cheap (c := (252:ℤ)) (by norm_num), EvP2_eq_cheap (c := (252:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_253 : EvP1 (253:ℤ) = EvP2 (253:ℤ) := by
  rw [EvP1_eq_cheap (c := (253:ℤ)) (by norm_num), EvP2_eq_cheap (c := (253:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_254 : EvP1 (254:ℤ) = EvP2 (254:ℤ) := by
  rw [EvP1_eq_cheap (c := (254:ℤ)) (by norm_num), EvP2_eq_cheap (c := (254:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_255 : EvP1 (255:ℤ) = EvP2 (255:ℤ) := by
  rw [EvP1_eq_cheap (c := (255:ℤ)) (by norm_num), EvP2_eq_cheap (c := (255:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_256 : EvP1 (256:ℤ) = EvP2 (256:ℤ) := by
  rw [EvP1_eq_cheap (c := (256:ℤ)) (by norm_num), EvP2_eq_cheap (c := (256:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_257 : EvP1 (257:ℤ) = EvP2 (257:ℤ) := by
  rw [EvP1_eq_cheap (c := (257:ℤ)) (by norm_num), EvP2_eq_cheap (c := (257:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_258 : EvP1 (258:ℤ) = EvP2 (258:ℤ) := by
  rw [EvP1_eq_cheap (c := (258:ℤ)) (by norm_num), EvP2_eq_cheap (c := (258:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_259 : EvP1 (259:ℤ) = EvP2 (259:ℤ) := by
  rw [EvP1_eq_cheap (c := (259:ℤ)) (by norm_num), EvP2_eq_cheap (c := (259:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_260 : EvP1 (260:ℤ) = EvP2 (260:ℤ) := by
  rw [EvP1_eq_cheap (c := (260:ℤ)) (by norm_num), EvP2_eq_cheap (c := (260:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_261 : EvP1 (261:ℤ) = EvP2 (261:ℤ) := by
  rw [EvP1_eq_cheap (c := (261:ℤ)) (by norm_num), EvP2_eq_cheap (c := (261:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_262 : EvP1 (262:ℤ) = EvP2 (262:ℤ) := by
  rw [EvP1_eq_cheap (c := (262:ℤ)) (by norm_num), EvP2_eq_cheap (c := (262:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_263 : EvP1 (263:ℤ) = EvP2 (263:ℤ) := by
  rw [EvP1_eq_cheap (c := (263:ℤ)) (by norm_num), EvP2_eq_cheap (c := (263:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_264 : EvP1 (264:ℤ) = EvP2 (264:ℤ) := by
  rw [EvP1_eq_cheap (c := (264:ℤ)) (by norm_num), EvP2_eq_cheap (c := (264:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_265 : EvP1 (265:ℤ) = EvP2 (265:ℤ) := by
  rw [EvP1_eq_cheap (c := (265:ℤ)) (by norm_num), EvP2_eq_cheap (c := (265:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_266 : EvP1 (266:ℤ) = EvP2 (266:ℤ) := by
  rw [EvP1_eq_cheap (c := (266:ℤ)) (by norm_num), EvP2_eq_cheap (c := (266:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_267 : EvP1 (267:ℤ) = EvP2 (267:ℤ) := by
  rw [EvP1_eq_cheap (c := (267:ℤ)) (by norm_num), EvP2_eq_cheap (c := (267:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_268 : EvP1 (268:ℤ) = EvP2 (268:ℤ) := by
  rw [EvP1_eq_cheap (c := (268:ℤ)) (by norm_num), EvP2_eq_cheap (c := (268:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_269 : EvP1 (269:ℤ) = EvP2 (269:ℤ) := by
  rw [EvP1_eq_cheap (c := (269:ℤ)) (by norm_num), EvP2_eq_cheap (c := (269:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_270 : EvP1 (270:ℤ) = EvP2 (270:ℤ) := by
  rw [EvP1_eq_cheap (c := (270:ℤ)) (by norm_num), EvP2_eq_cheap (c := (270:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_271 : EvP1 (271:ℤ) = EvP2 (271:ℤ) := by
  rw [EvP1_eq_cheap (c := (271:ℤ)) (by norm_num), EvP2_eq_cheap (c := (271:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_272 : EvP1 (272:ℤ) = EvP2 (272:ℤ) := by
  rw [EvP1_eq_cheap (c := (272:ℤ)) (by norm_num), EvP2_eq_cheap (c := (272:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_273 : EvP1 (273:ℤ) = EvP2 (273:ℤ) := by
  rw [EvP1_eq_cheap (c := (273:ℤ)) (by norm_num), EvP2_eq_cheap (c := (273:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_274 : EvP1 (274:ℤ) = EvP2 (274:ℤ) := by
  rw [EvP1_eq_cheap (c := (274:ℤ)) (by norm_num), EvP2_eq_cheap (c := (274:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_275 : EvP1 (275:ℤ) = EvP2 (275:ℤ) := by
  rw [EvP1_eq_cheap (c := (275:ℤ)) (by norm_num), EvP2_eq_cheap (c := (275:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_276 : EvP1 (276:ℤ) = EvP2 (276:ℤ) := by
  rw [EvP1_eq_cheap (c := (276:ℤ)) (by norm_num), EvP2_eq_cheap (c := (276:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_277 : EvP1 (277:ℤ) = EvP2 (277:ℤ) := by
  rw [EvP1_eq_cheap (c := (277:ℤ)) (by norm_num), EvP2_eq_cheap (c := (277:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_278 : EvP1 (278:ℤ) = EvP2 (278:ℤ) := by
  rw [EvP1_eq_cheap (c := (278:ℤ)) (by norm_num), EvP2_eq_cheap (c := (278:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_279 : EvP1 (279:ℤ) = EvP2 (279:ℤ) := by
  rw [EvP1_eq_cheap (c := (279:ℤ)) (by norm_num), EvP2_eq_cheap (c := (279:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_280 : EvP1 (280:ℤ) = EvP2 (280:ℤ) := by
  rw [EvP1_eq_cheap (c := (280:ℤ)) (by norm_num), EvP2_eq_cheap (c := (280:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_281 : EvP1 (281:ℤ) = EvP2 (281:ℤ) := by
  rw [EvP1_eq_cheap (c := (281:ℤ)) (by norm_num), EvP2_eq_cheap (c := (281:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_282 : EvP1 (282:ℤ) = EvP2 (282:ℤ) := by
  rw [EvP1_eq_cheap (c := (282:ℤ)) (by norm_num), EvP2_eq_cheap (c := (282:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_283 : EvP1 (283:ℤ) = EvP2 (283:ℤ) := by
  rw [EvP1_eq_cheap (c := (283:ℤ)) (by norm_num), EvP2_eq_cheap (c := (283:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_284 : EvP1 (284:ℤ) = EvP2 (284:ℤ) := by
  rw [EvP1_eq_cheap (c := (284:ℤ)) (by norm_num), EvP2_eq_cheap (c := (284:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_285 : EvP1 (285:ℤ) = EvP2 (285:ℤ) := by
  rw [EvP1_eq_cheap (c := (285:ℤ)) (by norm_num), EvP2_eq_cheap (c := (285:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_286 : EvP1 (286:ℤ) = EvP2 (286:ℤ) := by
  rw [EvP1_eq_cheap (c := (286:ℤ)) (by norm_num), EvP2_eq_cheap (c := (286:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_287 : EvP1 (287:ℤ) = EvP2 (287:ℤ) := by
  rw [EvP1_eq_cheap (c := (287:ℤ)) (by norm_num), EvP2_eq_cheap (c := (287:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_288 : EvP1 (288:ℤ) = EvP2 (288:ℤ) := by
  rw [EvP1_eq_cheap (c := (288:ℤ)) (by norm_num), EvP2_eq_cheap (c := (288:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_289 : EvP1 (289:ℤ) = EvP2 (289:ℤ) := by
  rw [EvP1_eq_cheap (c := (289:ℤ)) (by norm_num), EvP2_eq_cheap (c := (289:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_290 : EvP1 (290:ℤ) = EvP2 (290:ℤ) := by
  rw [EvP1_eq_cheap (c := (290:ℤ)) (by norm_num), EvP2_eq_cheap (c := (290:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_291 : EvP1 (291:ℤ) = EvP2 (291:ℤ) := by
  rw [EvP1_eq_cheap (c := (291:ℤ)) (by norm_num), EvP2_eq_cheap (c := (291:ℤ)) (by norm_num)]
  decide

set_option maxHeartbeats 0 in
lemma evc_292 : EvP1 (292:ℤ) = EvP2 (292:ℤ) := by
  rw [EvP1_eq_cheap (c := (292:ℤ)) (by norm_num), EvP2_eq_cheap (c := (292:ℤ)) (by norm_num)]
  decide

noncomputable def pts : Finset ℤ := (Finset.range 293).image (fun k : ℕ => (k : ℤ))

lemma pts_card : pts.card = 293 := by
  rw [pts, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Int.ofNat.inj h

theorem poly_eq : P1 = P2 := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' P1 P2 pts ?_ ?_
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_range] at hk
    rw [eval_P1_EvP1 (k : ℤ), eval_P2_EvP2 (k : ℤ)]
    interval_cases k
    · exact evc_0
    · exact evc_1
    · exact evc_2
    · exact evc_3
    · exact evc_4
    · exact evc_5
    · exact evc_6
    · exact evc_7
    · exact evc_8
    · exact evc_9
    · exact evc_10
    · exact evc_11
    · exact evc_12
    · exact evc_13
    · exact evc_14
    · exact evc_15
    · exact evc_16
    · exact evc_17
    · exact evc_18
    · exact evc_19
    · exact evc_20
    · exact evc_21
    · exact evc_22
    · exact evc_23
    · exact evc_24
    · exact evc_25
    · exact evc_26
    · exact evc_27
    · exact evc_28
    · exact evc_29
    · exact evc_30
    · exact evc_31
    · exact evc_32
    · exact evc_33
    · exact evc_34
    · exact evc_35
    · exact evc_36
    · exact evc_37
    · exact evc_38
    · exact evc_39
    · exact evc_40
    · exact evc_41
    · exact evc_42
    · exact evc_43
    · exact evc_44
    · exact evc_45
    · exact evc_46
    · exact evc_47
    · exact evc_48
    · exact evc_49
    · exact evc_50
    · exact evc_51
    · exact evc_52
    · exact evc_53
    · exact evc_54
    · exact evc_55
    · exact evc_56
    · exact evc_57
    · exact evc_58
    · exact evc_59
    · exact evc_60
    · exact evc_61
    · exact evc_62
    · exact evc_63
    · exact evc_64
    · exact evc_65
    · exact evc_66
    · exact evc_67
    · exact evc_68
    · exact evc_69
    · exact evc_70
    · exact evc_71
    · exact evc_72
    · exact evc_73
    · exact evc_74
    · exact evc_75
    · exact evc_76
    · exact evc_77
    · exact evc_78
    · exact evc_79
    · exact evc_80
    · exact evc_81
    · exact evc_82
    · exact evc_83
    · exact evc_84
    · exact evc_85
    · exact evc_86
    · exact evc_87
    · exact evc_88
    · exact evc_89
    · exact evc_90
    · exact evc_91
    · exact evc_92
    · exact evc_93
    · exact evc_94
    · exact evc_95
    · exact evc_96
    · exact evc_97
    · exact evc_98
    · exact evc_99
    · exact evc_100
    · exact evc_101
    · exact evc_102
    · exact evc_103
    · exact evc_104
    · exact evc_105
    · exact evc_106
    · exact evc_107
    · exact evc_108
    · exact evc_109
    · exact evc_110
    · exact evc_111
    · exact evc_112
    · exact evc_113
    · exact evc_114
    · exact evc_115
    · exact evc_116
    · exact evc_117
    · exact evc_118
    · exact evc_119
    · exact evc_120
    · exact evc_121
    · exact evc_122
    · exact evc_123
    · exact evc_124
    · exact evc_125
    · exact evc_126
    · exact evc_127
    · exact evc_128
    · exact evc_129
    · exact evc_130
    · exact evc_131
    · exact evc_132
    · exact evc_133
    · exact evc_134
    · exact evc_135
    · exact evc_136
    · exact evc_137
    · exact evc_138
    · exact evc_139
    · exact evc_140
    · exact evc_141
    · exact evc_142
    · exact evc_143
    · exact evc_144
    · exact evc_145
    · exact evc_146
    · exact evc_147
    · exact evc_148
    · exact evc_149
    · exact evc_150
    · exact evc_151
    · exact evc_152
    · exact evc_153
    · exact evc_154
    · exact evc_155
    · exact evc_156
    · exact evc_157
    · exact evc_158
    · exact evc_159
    · exact evc_160
    · exact evc_161
    · exact evc_162
    · exact evc_163
    · exact evc_164
    · exact evc_165
    · exact evc_166
    · exact evc_167
    · exact evc_168
    · exact evc_169
    · exact evc_170
    · exact evc_171
    · exact evc_172
    · exact evc_173
    · exact evc_174
    · exact evc_175
    · exact evc_176
    · exact evc_177
    · exact evc_178
    · exact evc_179
    · exact evc_180
    · exact evc_181
    · exact evc_182
    · exact evc_183
    · exact evc_184
    · exact evc_185
    · exact evc_186
    · exact evc_187
    · exact evc_188
    · exact evc_189
    · exact evc_190
    · exact evc_191
    · exact evc_192
    · exact evc_193
    · exact evc_194
    · exact evc_195
    · exact evc_196
    · exact evc_197
    · exact evc_198
    · exact evc_199
    · exact evc_200
    · exact evc_201
    · exact evc_202
    · exact evc_203
    · exact evc_204
    · exact evc_205
    · exact evc_206
    · exact evc_207
    · exact evc_208
    · exact evc_209
    · exact evc_210
    · exact evc_211
    · exact evc_212
    · exact evc_213
    · exact evc_214
    · exact evc_215
    · exact evc_216
    · exact evc_217
    · exact evc_218
    · exact evc_219
    · exact evc_220
    · exact evc_221
    · exact evc_222
    · exact evc_223
    · exact evc_224
    · exact evc_225
    · exact evc_226
    · exact evc_227
    · exact evc_228
    · exact evc_229
    · exact evc_230
    · exact evc_231
    · exact evc_232
    · exact evc_233
    · exact evc_234
    · exact evc_235
    · exact evc_236
    · exact evc_237
    · exact evc_238
    · exact evc_239
    · exact evc_240
    · exact evc_241
    · exact evc_242
    · exact evc_243
    · exact evc_244
    · exact evc_245
    · exact evc_246
    · exact evc_247
    · exact evc_248
    · exact evc_249
    · exact evc_250
    · exact evc_251
    · exact evc_252
    · exact evc_253
    · exact evc_254
    · exact evc_255
    · exact evc_256
    · exact evc_257
    · exact evc_258
    · exact evc_259
    · exact evc_260
    · exact evc_261
    · exact evc_262
    · exact evc_263
    · exact evc_264
    · exact evc_265
    · exact evc_266
    · exact evc_267
    · exact evc_268
    · exact evc_269
    · exact evc_270
    · exact evc_271
    · exact evc_272
    · exact evc_273
    · exact evc_274
    · exact evc_275
    · exact evc_276
    · exact evc_277
    · exact evc_278
    · exact evc_279
    · exact evc_280
    · exact evc_281
    · exact evc_282
    · exact evc_283
    · exact evc_284
    · exact evc_285
    · exact evc_286
    · exact evc_287
    · exact evc_288
    · exact evc_289
    · exact evc_290
    · exact evc_291
    · exact evc_292
  · rw [pts_card]
    exact degree_bound

def Df (m : ℕ) : ℤ := (Dpol).eval (m : ℤ)
def Pf (i : ℕ) (m : ℕ) : ℤ := (Ppol i).eval (m : ℤ)
def Qf (i : ℕ) (m : ℕ) : ℤ := (Qpol i).eval (m : ℤ)
def Rf (j : ℕ) (m : ℕ) : ℤ := (Rpol j).eval (m : ℤ)
def Tf (k : ℕ) (m : ℕ) : ℤ := (Tpol k).eval (m : ℤ)

lemma Pf_pos (i m : ℕ) (hi : i < 50) : 0 < Pf i m := by
  rw [Pf, Ppol, Polynomial.eval_prod]
  apply Finset.prod_pos
  intro j hj
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  positivity

lemma Df_pos (m : ℕ) : 0 < Df m := by
  rw [Df, Dpol, Polynomial.eval_prod]
  apply Finset.prod_pos
  intro τ hτ
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  positivity

lemma Df_eq_Pf_sq_mul_Qf (i m : ℕ) (hi : i < 50) : Df m = (Pf i m) ^ 2 * Qf i m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_Ppol_sq_mul_Qpol i hi)
  simpa [Df, Pf, Qf, Polynomial.eval_mul, Polynomial.eval_pow] using h

lemma Df_eq_sq_mul_Rf (j m : ℕ) (h1 : 25 ≤ j) (h2 : j ≤ 146) :
    Df m = (3 * (m : ℤ) + (j : ℤ)) ^ 2 * Rf j m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_sq_mul_Rpol j h1 h2)
  simpa [Df, Rf, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

lemma Df_eq_lin_mul_Tf (k m : ℕ) (h1 : 25 ≤ k) (h2 : k ≤ 143) :
    Df m = (3 * (m : ℤ) + (k : ℤ)) * (3 * (m : ℤ) + ((k + 3 : ℕ) : ℤ)) * Tf k m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_lin_mul_Tpol k h1 h2)
  simpa [Df, Tf, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h


/-! ## real-valued definitions -/

noncomputable def cTwentyFourPf (i : ℕ) (m : ℕ) : ℝ := ∏ j ∈ Finset.range 25, xm m (25 + 3 * j + i)

noncomputable def Vm24 (m : ℕ) : ℝ := (79766443076872509863361 : ℝ) * (Nat.choose (m + 48) 48 : ℝ) *
  (∑ i ∈ Finset.range 50, ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
    (175232954511896091869033107292160000 / cTwentyFourPf i m) ^ 2)

noncomputable def aj (j : ℕ) : ℝ := (cA j : ℝ) / (Lc : ℝ)
noncomputable def dj (k : ℕ) : ℝ := (cD k : ℝ) / (3 * (Lc : ℝ))

noncomputable def W124 (m : ℕ) : ℝ := ∑ j ∈ aIdx, aj j / (xm m j) ^ 2
noncomputable def W224 (m : ℕ) : ℝ := ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))
noncomputable def Vd24 (m : ℕ) : ℝ := W124 m + W224 m

lemma cTwentyFourPf_eq (i m : ℕ) : cTwentyFourPf i m = ((Pf i m : ℤ) : ℝ) := by
  have h : ((Pf i m : ℤ) : ℝ) = ∏ j ∈ Finset.range 25,
      ((3 : ℝ) * (m : ℝ) + ((25 + 3 * j + i : ℕ) : ℝ)) := by
    rw [Pf, Ppol, Polynomial.eval_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    ring
  rw [h, cTwentyFourPf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [xm_eq]

lemma eval_prodP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∏ r ∈ Finset.range 48, (Polynomial.X + C ((r : ℤ) + 1))) =
      ∏ r ∈ Finset.range 48, ((m : ℤ) + (r + 1)) := by
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

lemma eval_sumP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∑ i ∈ Finset.range 50,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ)) * Qpol i) =
      ∑ i ∈ Finset.range 50, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ) * (Qf i m) := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.eval_mul, Polynomial.eval_C, Qf]

lemma eval_P1_int (m : ℕ) :
    P1.eval (m : ℤ) = (79766443076872509863361 * 175232954511896091869033107292160000 ^ 2) *
      (∏ r ∈ Finset.range 48, ((m : ℤ) + (r + 1))) *
      (∑ i ∈ Finset.range 50, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 49 i : ℤ) * (Qf i m)) := by
  rw [P1, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_prodP m, eval_sumP m]
  ring

lemma eval_P1 (m : ℕ) :
    ((P1.eval (m : ℤ) : ℤ) : ℝ) = (79766443076872509863361 : ℝ) * (175232954511896091869033107292160000 : ℝ) ^ 2 *
      (∏ r ∈ Finset.range 48, ((m : ℝ) + (r + 1))) *
      (∑ i ∈ Finset.range 50, (Lc : ℝ) * (-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ) * ((Qf i m : ℤ) : ℝ)) := by
  rw [eval_P1_int m]
  push_cast
  ring

lemma eval_P2_int (m : ℕ) :
    P2.eval (m : ℤ) = 12413915592536072670862289047373375038521486354677760000000000 *
      ((∑ j ∈ aIdx, cA j * Rf j m) + (∑ k ∈ dIdx, cD k * Tf k m)) := by
  rw [P2, Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  rw [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Polynomial.eval_mul, Polynomial.eval_C, Rf]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [Polynomial.eval_mul, Polynomial.eval_C, Tf]

lemma eval_P2 (m : ℕ) :
    ((P2.eval (m : ℤ) : ℤ) : ℝ) = (12413915592536072670862289047373375038521486354677760000000000 : ℝ) *
      ((∑ j ∈ aIdx, (cA j : ℝ) * ((Rf j m : ℤ) : ℝ)) +
        (∑ k ∈ dIdx, (cD k : ℝ) * ((Tf k m : ℤ) : ℝ))) := by
  rw [eval_P2_int m]
  push_cast
  ring


/-! ## the factorial identity -/

lemma choose_fact_nat (m : ℕ) :
    (m + 48).choose 48 * (48 !) = ∏ r ∈ Finset.range 48, (m + r + 1) := by
  have h2 : (m + 1).ascFactorial 48 = 48 ! * (m + 48).choose 48 := by
    simpa using Nat.ascFactorial_eq_factorial_mul_choose m 48
  have h1 : (m + 1).ascFactorial 48 = ∏ i ∈ Finset.range 48, (m + 1 + i) :=
    Nat.ascFactorial_eq_prod_range (m + 1) 48
  rw [h2, Nat.mul_comm] at h1
  rw [h1]
  apply Finset.prod_congr rfl
  intro r hr
  omega

lemma choose_fact (m : ℕ) :
    (Nat.choose (m + 48) 48 : ℝ) * 12413915592536072670862289047373375038521486354677760000000000 = ∏ r ∈ Finset.range 48, ((m : ℝ) + (r + 1)) := by
  have h : ((m + 48).choose 48 : ℝ) * ((48 ! : ℕ) : ℝ) =
      ((∏ r ∈ Finset.range 48, (m + r + 1) : ℕ) : ℝ) := by
    exact_mod_cast choose_fact_nat m
  have h24 : ((48 ! : ℕ) : ℝ) = 12413915592536072670862289047373375038521486354677760000000000 := by norm_num
  rw [h24] at h
  rw [h]
  push_cast
  apply Finset.prod_congr rfl
  intro r hr
  ring


/-! ## the two clearing identities -/

lemma clear_left (m : ℕ) :
    Vm24 m * ((Df m : ℤ) : ℝ) * 12413915592536072670862289047373375038521486354677760000000000 * (Lc : ℝ) =
      ((P1.eval (m : ℤ) : ℤ) : ℝ) := by
  have hgoal : Vm24 m * ((Df m : ℤ) : ℝ) * 12413915592536072670862289047373375038521486354677760000000000 * (Lc : ℝ) =
      (79766443076872509863361 : ℝ) * ((Nat.choose (m + 48) 48 : ℝ) * 12413915592536072670862289047373375038521486354677760000000000) *
        ((∑ i ∈ Finset.range 50, ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
            (175232954511896091869033107292160000 / cTwentyFourPf i m) ^ 2) * ((Df m : ℤ) : ℝ)) * (Lc : ℝ) := by
    rw [Vm24]
    ring
  have hsum : (∑ i ∈ Finset.range 50, ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
        (175232954511896091869033107292160000 / cTwentyFourPf i m) ^ 2) * ((Df m : ℤ) : ℝ) =
      (175232954511896091869033107292160000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 50,
        ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cTwentyFourPf_eq i m]
    have hD : ((Df m : ℤ) : ℝ) = ((((Pf i m : ℤ)) : ℝ)) ^ 2 * ((Qf i m : ℤ) : ℝ) := by
      rw [Df_eq_Pf_sq_mul_Qf i m hi]
      simp only [Int.cast_mul, Int.cast_pow]
    rw [hD]
    have hne : (((Pf i m : ℤ)) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Pf_pos i m hi))
    field_simp
    try ring
  have hLc2 : ((175232954511896091869033107292160000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 50,
        ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ) =
      (175232954511896091869033107292160000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 50,
        (Lc : ℝ) * ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [show ((175232954511896091869033107292160000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 50,
          ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
        = (175232954511896091869033107292160000 : ℝ) ^ 2 * ((Lc : ℝ) * (∑ i ∈ Finset.range 50,
          ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) by ring]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hgoal, choose_fact m, hsum, eval_P1 m]
  rw [show (79766443076872509863361 : ℝ) * (∏ r ∈ Finset.range 48, ((m : ℝ) + (r + 1))) *
        ((175232954511896091869033107292160000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 50,
          ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
      = (79766443076872509863361 : ℝ) * (∏ r ∈ Finset.range 48, ((m : ℝ) + (r + 1))) *
        (((175232954511896091869033107292160000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 50,
          ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)) by ring]
  rw [hLc2]
  ring

lemma clear_right (m : ℕ) :
    Vd24 m * ((Df m : ℤ) : ℝ) * 12413915592536072670862289047373375038521486354677760000000000 * (Lc : ℝ) =
      ((P2.eval (m : ℤ) : ℤ) : ℝ) := by
  have hW1 : (∑ j ∈ aIdx, aj j / (xm m j) ^ 2) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) =
      ∑ j ∈ aIdx, (cA j : ℝ) * ((Rf j m : ℤ) : ℝ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj1, hj2⟩ := aIdx_bounds j hj
    have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
    have hD : ((Df m : ℤ) : ℝ) = (3 * (m : ℝ) + (j : ℝ)) ^ 2 * ((Rf j m : ℤ) : ℝ) := by
      rw [Df_eq_sq_mul_Rf j m hj1 hj2]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_ofNat, Int.cast_natCast]
    have h2 : (aj j) * (Lc : ℝ) = (cA j : ℝ) := by
      unfold aj
      field_simp
    rw [hD, xm_eq]
    have hne : 3 * (m : ℝ) + (j : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← h2]
    ring
  have hW2 : (∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) =
      ∑ k ∈ dIdx, (cD k : ℝ) * ((Tf k m : ℤ) : ℝ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hk1, hk2⟩ := dIdx_bounds k hk
    have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
    have hD : ((Df m : ℤ) : ℝ) =
        (3 * (m : ℝ) + (k : ℝ)) * (3 * (m : ℝ) + ((k + 3 : ℕ) : ℝ)) * ((Tf k m : ℤ) : ℝ) := by
      rw [Df_eq_lin_mul_Tf k m hk1 hk2]
      simp only [Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast]
    have h2 : (dj k) * (3 * (Lc : ℝ)) = (cD k : ℝ) := by
      unfold dj
      field_simp
    rw [hD, xm_eq, xm_eq]
    have hA : 3 * (m : ℝ) + (k : ℝ) ≠ 0 := by positivity
    have hB : 3 * (m : ℝ) + ((k + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← h2]
    push_cast
    ring
  rw [eval_P2 m, Vd24]
  rw [show (W124 m + W224 m) * ((Df m : ℤ) : ℝ) * 12413915592536072670862289047373375038521486354677760000000000 * (Lc : ℝ) =
      ((∑ j ∈ aIdx, aj j / (xm m j) ^ 2) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) +
        (∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) * ((Df m : ℤ) : ℝ) * (Lc : ℝ)) *
        12413915592536072670862289047373375038521486354677760000000000 by
    rw [W124, W224]
    ring]
  rw [hW1, hW2]
  ring

theorem vm24_decomp (m : ℕ) : Vm24 m = Vd24 m := by
  have h1 := clear_left m
  have h2 := clear_right m
  have hP : ((P1.eval (m : ℤ) : ℤ) : ℝ) = ((P2.eval (m : ℤ) : ℤ) : ℝ) := by rw [poly_eq]
  have hDf : ((Df m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Df_pos m))
  have hFT : (12413915592536072670862289047373375038521486354677760000000000 : ℝ) ≠ 0 := by norm_num
  have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
  have h := h1.trans (hP.trans h2.symm)
  have h' : (Vm24 m * ((Df m : ℤ) : ℝ)) * 12413915592536072670862289047373375038521486354677760000000000 =
      (Vd24 m * ((Df m : ℤ) : ℝ)) * 12413915592536072670862289047373375038521486354677760000000000 := mul_right_cancel₀ hLc h
  have h'' : Vm24 m * ((Df m : ℤ) : ℝ) = Vd24 m * ((Df m : ℤ) : ℝ) := mul_right_cancel₀ hFT h'
  exact mul_right_cancel₀ hDf h''

lemma denom_statement24 (m : ℕ) (i : ℕ) :
    (((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ) * ((3 * m + 88 + i : ℕ) : ℝ) * ((3 * m + 91 + i : ℕ) : ℝ) * ((3 * m + 94 + i : ℕ) : ℝ) * ((3 * m + 97 + i : ℕ) : ℝ))
      = cTwentyFourPf i m := by
  rw [cTwentyFourPf]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  simp only [xm_eq]
  push_cast
  ring

lemma inner_sum_statement24 (m : ℕ) :
    (∑ i ∈ Finset.range 50,
      ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
        (175232954511896091869033107292160000 / (((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ) * ((3 * m + 88 + i : ℕ) : ℝ) * ((3 * m + 91 + i : ℕ) : ℝ) * ((3 * m + 94 + i : ℕ) : ℝ) * ((3 * m + 97 + i : ℕ) : ℝ))) ^ 2)
    = (∑ i ∈ Finset.range 50,
      ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
        (175232954511896091869033107292160000 / cTwentyFourPf i m) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [denom_statement24 m i]

lemma vm24_eq_statement (m : ℕ) :
    (79766443076872509863361 : ℝ) * (Nat.choose (m + 48) 48 : ℝ) *
      (∑ i ∈ Finset.range 50,
        ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
          (175232954511896091869033107292160000 / (((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ) * ((3 * m + 88 + i : ℕ) : ℝ) * ((3 * m + 91 + i : ℕ) : ℝ) * ((3 * m + 94 + i : ℕ) : ℝ) * ((3 * m + 97 + i : ℕ) : ℝ))) ^ 2) =
      Vm24 m := by
  rw [Vm24, inner_sum_statement24 m]

/-! ## Small partial sums needed for the shifts -/

@[simp] lemma asum0 : Asum 0 = 0 / 1 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum1 : Asum 1 = 1 / 1 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum2 : Asum 2 = 17 / 16 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum3 : Asum 3 = 849 / 784 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum4 : Asum 4 = 21421 / 19600 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum5 : Asum 5 = 3639749 / 3312400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum6 : Asum 6 = 58443009 / 52998400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum7 : Asum 7 = 21150924649 / 19132422400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum8 : Asum 8 = 2564044988129 / 2315023110400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum9 : Asum 9 = 64193725627641 / 57875577760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum10 : Asum 10 = 64267546517641 / 57875577760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum11 : Asum 11 = 61818987781213001 / 55618430227360000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum12 : Asum 12 = 17879592076327397289 / 16073726335707040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum13 : Asum 13 = 24493235278827913928641 / 22004931353582937760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum14 : Asum 14 = 24506988360923903264741 / 22004931353582937760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum15 : Asum 15 = 45335426410701880074266109 / 40687118072774851918240000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum16 : Asum 16 = 23992612350779488272266331661 / 21523485460497896664748960000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum17 : Asum 17 = 1176077259993511208946453291389 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum18 : Asum 18 = 1176467293568793900121221301389 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum19 : Asum 19 = 1176815938457244940430832110989 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum20 : Asum 20 = 989965866939434094136472980101749 / 886961312341657823657639892640000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum21 : Asum 21 = 3684549952193975922105473598851248029 / 3300383043223308761830078040513440000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum22 : Asum 22 = 58965691356366205803538476323965724089 / 52806128691572940189281248648215040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum23 : Asum 23 = 264749794627419470792273501466930350475521 / 237046711696470928509683525181837314560000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum24 : Asum 24 = 264798171507357526083806089941457256049921 / 237046711696470928509683525181837314560000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum25 : Asum 25 = 1411346502674404727429112336823207554804589009 / 1263221926630493578028103505694011049290240000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum26 : Asum 26 = 1411565204531508344738327728704387265858829009 / 1263221926630493578028103505694011049290240000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum27 : Asum 27 = 8810841663407774073089931458349774937274242085169 / 7883768044100910420473393979036322958620387840000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum28 : Asum 28 = 14812995778199493444469293129980730750297656042129089 / 13252614082133630416815775278760058893440871959040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum29 : Asum 29 = 14814830050044771455599648254586787505853841629943489 / 13252614082133630416815775278760058893440871959040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum30 : Asum 30 = 14816541389673146149610084175981255488665494635103489 / 13252614082133630416815775278760058893440871959040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum31 : Asum 31 = 14818141753648769097372047196785356449768433998943489 / 13252614082133630416815775278760058893440871959040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum32 : Asum 32 = 32736588287330664343699056201518542412261830921655927201 / 29275024507433189590746047590780970095610886157519360000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum33 : Asum 33 = 308047834220001653999455165847678746527067178028018138394209 / 275448705590438880859329561781658147629602827856099658240000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum34 : Asum 34 = 308075379090560697887541098803856912341830138310803748360033 / 275448705590438880859329561781658147629602827856099658240000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum35 : Asum 35 = 3268647145477348882769782846771899641182105540167173066009830097 / 2922235317608966087036627320941611288202456400725361274268160000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum36 : Asum 36 = 9182360390475275253222079173412501494902585076429770482740179782473 / 8208559007163585738485886144524986108560700029637539819419261440000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum37 : Asum 37 = 109103832358243908869270008545458455247046173993091740645255495257001713 / 97525889564110562158950813283101359955809677052123610594520245168640000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum38 : Asum 38 = 109111607062450231458727833068201049424338569534948574479008247189811713 / 97525889564110562158950813283101359955809677052123610594520245168640000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum39 : Asum 39 = 109118981420829370253598075095670471077265284822438338079053201461658113 / 97525889564110562158950813283101359955809677052123610594520245168640000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum40 : Asum 40 = 379867555798298065493314637111349685159949408886170885755832824349324051353 / 339487621572668866875307781038475834006173485818442288479524973432035840000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum41 : Asum 41 = 45966779934416980543425577766349662944304342718911127112724197572494921253713 / 41078002210292932891912241505655575914746991784031516906022521785276336640000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum42 : Asum 42 = 45969451500637733205554344171234265934413262268324760796185827549197917893713 / 41078002210292932891912241505655575914746991784031516906022521785276336640000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum43 : Asum 43 = 741482361255996291805277929379343130832066254117594098398587235062798494044336977 / 662547097649814714613652543244718783928954230484644336177237253874722033666560000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum44 : Asum 44 = 741521565226271428770639683967700806499754357918214491554574053835217116649879377 / 662547097649814714613652543244718783928954230484644336177237253874722033666560000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum45 : Asum 45 = 741559020543002154912005145697772869294933788877029836929449809234271598080919377 / 662547097649814714613652543244718783928954230484644336177237253874722033666560000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum46 : Asum 46 = 741594841644734951987838496289427536184203304136030953080843474743239738329279377 / 662547097649814714613652543244718783928954230484644336177237253874722033666560000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum47 : Asum 47 = 14329016482515573822071641239351274145398920993442738688811154012768009706293673403017 / 12801072473692070101050380788031211624291324687193813219280400982113504412471605760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum48 : Asum 48 = 72235772356479430654588406082766780769862033559116644183601847478609065305529525526048697 / 64530206339881725379394969552465337798052567748144012438392501350834175743269364636160000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma bsum0 : Bsum 0 = 0 / 1 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum1 : Bsum 1 = 1 / 4 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum2 : Bsum 2 = 29 / 100 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum3 : Bsum 3 = 489 / 1600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum4 : Bsum 4 = 60769 / 193600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum5 : Bsum 5 = 3026081 / 9486400 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum6 : Bsum 6 = 884023809 / 2741569600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum7 : Bsum 7 = 890877733 / 2741569600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum8 : Bsum 8 = 474015890357 / 1450290318400 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum9 : Bsum 9 = 80471258049933 / 245099063809600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum10 : Bsum 10 = 67921427083803253 / 206128312663873600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum11 : Bsum 11 = 1089963588226225073 / 3298053002621977600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum12 : Bsum 12 = 1092655876391630769 / 3298053002621977600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum13 : Bsum 13 = 395273284628034202009 / 1190597133946533913600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum14 : Bsum 14 = 665644988593672027490729 / 2001393782164123508761600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum15 : Bsum 15 = 666678766373715479716329 / 2001393782164123508761600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum16 : Bsum 16 = 1474694788701701618202132361 / 4421078864800548830854374400 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum17 : Bsum 17 = 36911580506190545943361852769 / 110526971620013720771359360000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum18 : Bsum 18 = 103795156613509257275674803788121 / 310470263280618541646748442240000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum19 : Bsum 19 = 103894158610728842269822363878121 / 310470263280618541646748442240000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum20 : Bsum 20 = 361966036387227718482898397101979201 / 1080746986479833143472331327437440000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum21 : Bsum 21 = 348119547714745795747933442446861372161 / 1038597854007119650876910405667379840000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum22 : Bsum 22 = 348365369692025587381277089880155426561 / 1038597854007119650876910405667379840000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum23 : Bsum 23 = 20505292938504139981959879070978858033 / 61093991412183508875112376803963520000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum24 : Bsum 24 = 103428275694411553157934862773608386864353 / 307974810708817068239441491468780104320000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum25 : Bsum 25 = 141670303128326620540272687509937076643379257 / 421617515860370566419795401820759962814080000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum26 : Bsum 26 = 141741414195262085301011394779598193182899257 / 421617515860370566419795401820759962814080000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum27 : Bsum 27 = 141807291932115268202014487811132686927088957 / 421617515860370566419795401820759962814080000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum28 : Bsum 28 = 977332051636202453210097601932713840203529904773 / 2904523066762092832065970523143215383826197120000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum29 : Bsum 29 = 1807813094242028859193486958604373694382283343205277 / 5370463150443109646489979497291805244694638474880000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum30 : Bsum 30 = 14325057982641553703318100178602535838446761000003879117 / 42539438614659871509847127598048389343226231359524480000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum31 : Bsum 31 = 14330083908753871741067373232430282576318125157773199117 / 42539438614659871509847127598048389343226231359524480000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum32 : Bsum 32 = 14334797419957712170043533578978542785663634989502786317 / 42539438614659871509847127598048389343226231359524480000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum33 : Bsum 33 = 702622111530043507921469100102591700524779472808899409533 / 2084432492118333703982509252304371077818085336616699520000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum34 : Bsum 34 = 7169532592210092158010888799398842308131093487460199576166133 / 21263295852099122114325576882756889364822288518826951803520000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum35 : Bsum 35 = 7171498503439021440750748782468623825269113299638345559136133 / 21263295852099122114325576882756889364822288518826951803520000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum36 : Bsum 36 = 82127749661725455597269648387366031064870900456078245258353106717 / 243443474210682849086913529730683626337850381252049771198500480000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum37 : Bsum 37 = 82147868957114768229425591654285922273659152553702381603080255517 / 243443474210682849086913529730683626337850381252049771198500480000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum38 : Bsum 38 = 1049189582187609158370622293363307625138691569339477760460930283176573 / 3108529722196209299990798861131099224708011518207423528433652629120000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum39 : Bsum 39 = 1049420596584324096636079397916007617649445731907715529748120655696573 / 3108529722196209299990798861131099224708011518207423528433652629120000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum40 : Bsum 40 = 17843881870291488285430385537514663832843348164541857191226374859481741 / 52845005277335558099843580639228686820036195809526199983372094695040000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum41 : Bsum 41 = 66410295690673961799611425480251871293715107569212632158549183875805318261 / 196636264636965611689517963558569943657354684607246990138127564360243840000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum42 : Bsum 42 = 1660572010290268189968988865747990494252729456725687399147950600998109346669 / 4915906615924140292237949088964248591433867115181174753453189109006096000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum43 : Bsum 43 = 26573952854698904457757960474125039557058743443465667502337378745959013312329 / 78654505854786244675807185423427977462941873842898796055251025744097536000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum44 : Bsum 44 = 456114259445342685644260166881883231816148038107157218803667007685146724988877969 / 1349789974973986744881527109051447521241545497017986239104162852794457815296000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum45 : Bsum 45 = 2047834358143886812543304270910036689502998929437283251769437238211822262928897202841 / 6059207197658226497773175192531947922853297736113740227338587046194321132863744000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum46 : Bsum 46 = 38441862275200269811123051035903010573204640204344483092687906111043886374045335344122729 / 113725259892847253136704725188632130564033545209118790326917940270021213342719611136000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum47 : Bsum 47 = 38447664584378476303630025766779981600274233752569438133010708046771948680848535324282729 / 113725259892847253136704725188632130564033545209118790326917940270021213342719611136000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum48 : Bsum 48 = 38453225993733107202604875623750426713999307523668715300125330665984136133210152988282729 / 113725259892847253136704725188632130564033545209118790326917940270021213342719611136000000 := by
  norm_num [Bsum, f2, xm]

def cAval (j : ℕ) : ℝ := if j % 3 = 1 then (A - Asum (j / 3)) else (B - Bsum (j / 3))
def cDval (k : ℕ) : ℝ := 1 / xm 0 k

noncomputable def V1val24 : ℝ := ∑ j ∈ aIdx, aj j * cAval j
noncomputable def V2val24 : ℝ := ∑ k ∈ dIdx, dj k * cDval k
noncomputable def Vval24 : ℝ := V1val24 + V2val24

lemma aIdx_mod (j : ℕ) (hj : j ∈ aIdx) : j % 3 ≠ 0 := by
  simp only [aIdx, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

lemma hasSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (g : ι → ℝ)
    (h : ∀ i ∈ s, HasSum (f i) (g i)) : HasSum (fun m => ∑ i ∈ s, f i m) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hf : HasSum (fun m => f a m + ∑ i ∈ s, f i m) (g a + ∑ i ∈ s, g i) :=
        (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      refine hf.congr_fun (fun m => ?_)
      rw [Finset.sum_insert ha]

lemma hasSum_W124 : HasSum W124 V1val24 := by
  change HasSum (fun m => ∑ j ∈ aIdx, aj j / (xm m j) ^ 2) V1val24
  rw [V1val24]
  apply hasSum_finset_sum
  intro j hj
  obtain ⟨hj1, hj2⟩ := aIdx_bounds j hj
  by_cases h : j % 3 = 1
  · have hj' : 3 * (j / 3) + 1 = j := by
      have hmod := Nat.mod_add_div j 3
      omega
    have hh := (CdtTwoCore.hasSum_sq1 (j / 3)).mul_left (aj j)
    simpa [cAval, h, hj', div_eq_mul_inv, mul_comm] using hh
  · have hne0 : j % 3 ≠ 0 := aIdx_mod j hj
    have h2 : j % 3 = 2 := by
      have hlt := Nat.mod_lt j (by norm_num : 0 < 3)
      omega
    have hj' : 3 * (j / 3) + 2 = j := by
      have hmod : 3 * (j / 3) + j % 3 = j := Nat.div_add_mod j 3
      rw [h2] at hmod
      exact hmod
    have hh := (CdtTwoCore.hasSum_sq2 (j / 3)).mul_left (aj j)
    simpa [cAval, h, hj', div_eq_mul_inv, mul_comm] using hh

lemma hasSum_W224 : HasSum W224 V2val24 := by
  change HasSum (fun m => ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) V2val24
  rw [V2val24]
  apply hasSum_finset_sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := dIdx_bounds k hk
  have hh := (CdtTwoCore.hasSum_pair k (by omega)).mul_left (dj k)
  simpa [cDval, div_eq_mul_inv, mul_comm] using hh

lemma hasSum_Vm24 : HasSum Vm24 Vval24 := by
  have hsum : HasSum (fun m => W124 m + W224 m) Vval24 := by
    simpa [Vval24] using hasSum_W124.add hasSum_W224
  refine hsum.congr_fun (fun m => ?_)
  exact vm24_decomp m


set_option maxHeartbeats 0 in
lemma tsum_Vm24 : (∑' m : ℕ, Vm24 m) = 1360135024740956026161 * A - 1360135024740956026161 * B - 188052901998329938720023301915553943483 / 176961524070531200 := by
  have hval : Vval24 = 1360135024740956026161 * A - 1360135024740956026161 * B - 188052901998329938720023301915553943483 / 176961524070531200 := by
    unfold Vval24 V1val24 V2val24
    simp (maxSteps := 100000000) only [cAval, cDval, aj, dj, cA, cD, Lc, aIdx, dIdx, xm_eq,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      not_false_eq_true, asum0, asum1, asum2, asum3, asum4, asum5, asum6, asum7, asum8, asum9, asum10, asum11, asum12, asum13, asum14, asum15, asum16, asum17, asum18, asum19, asum20, asum21, asum22, asum23, asum24, asum25, asum26, asum27, asum28, asum29, asum30, asum31, asum32, asum33, asum34, asum35, asum36, asum37, asum38, asum39, asum40, asum41, asum42, asum43, asum44, asum45, asum46, asum47, asum48,
      bsum0, bsum1, bsum2, bsum3, bsum4, bsum5, bsum6, bsum7, bsum8, bsum9, bsum10, bsum11, bsum12, bsum13, bsum14, bsum15, bsum16, bsum17, bsum18, bsum19, bsum20, bsum21, bsum22, bsum23, bsum24, bsum25, bsum26, bsum27, bsum28, bsum29, bsum30, bsum31, bsum32, bsum33, bsum34, bsum35, bsum36, bsum37, bsum38, bsum39, bsum40, bsum41, bsum42, bsum43, bsum44, bsum45, bsum46, bsum47, bsum48]
    norm_num (maxSteps := 100000000)
    ring
  rw [hasSum_Vm24.tsum_eq]
  exact hval

end CdtTwentyFourCore
open CdtTwentyFourCore

theorem sum_cintegralTwentyFour_core :
    (∑' m : ℕ,
        (79766443076872509863361 : ℝ) * (Nat.choose (m + 48) 48 : ℝ) *
          (∑ i ∈ Finset.range 50,
            ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
              (175232954511896091869033107292160000 / (((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ) * ((3 * m + 88 + i : ℕ) : ℝ) * ((3 * m + 91 + i : ℕ) : ℝ) * ((3 * m + 94 + i : ℕ) : ℝ) * ((3 * m + 97 + i : ℕ) : ℝ))) ^ 2)) =
      1360135024740956026161 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 188052901998329938720023301915553943483 / 176961524070531200 := by
  have hMain := tsum_Vm24
  have hL : (∑' m : ℕ, Vm24 m) = (∑' m : ℕ,
        (79766443076872509863361 : ℝ) * (Nat.choose (m + 48) 48 : ℝ) *
          (∑ i ∈ Finset.range 50,
            ((-1 : ℝ) ^ i * (Nat.choose 49 i : ℝ)) *
              (175232954511896091869033107292160000 / (((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ) * ((3 * m + 64 + i : ℕ) : ℝ) * ((3 * m + 67 + i : ℕ) : ℝ) * ((3 * m + 70 + i : ℕ) : ℝ) * ((3 * m + 73 + i : ℕ) : ℝ) * ((3 * m + 76 + i : ℕ) : ℝ) * ((3 * m + 79 + i : ℕ) : ℝ) * ((3 * m + 82 + i : ℕ) : ℝ) * ((3 * m + 85 + i : ℕ) : ℝ) * ((3 * m + 88 + i : ℕ) : ℝ) * ((3 * m + 91 + i : ℕ) : ℝ) * ((3 * m + 94 + i : ℕ) : ℝ) * ((3 * m + 97 + i : ℕ) : ℝ))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm24_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
