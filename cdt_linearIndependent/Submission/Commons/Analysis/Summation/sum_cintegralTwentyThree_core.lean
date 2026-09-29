import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Submission.Commons.Analysis.Summation.sum_cintegralTwo_core_corrected

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section
open scoped BigOperators Nat
open Filter Topology
open Polynomial

namespace Commons.Analysis.Summation
namespace CdtTwentyThreeCore

/-! ## The clearing factor and the decomposition coefficients -/

def Lc : ℤ := 10948024351985531491968487200

def cA : ℕ → ℤ := fun j => if j = 25 then (-352265989636873049594253066726279445622400 : ℤ) else if j = 26 then (4820741693051036822492562981361608344256000 : ℤ) else if j = 28 then (-254535557998678623888236839807085988805920000 : ℤ) else if j = 29 then (995999667653580286361409887399175152554320000 : ℤ) else if j = 31 then (12010493329678494728878465643967598305599904000 : ℤ) else if j = 32 then (-117830662135575112772017291851853207956288216000 : ℤ) else if j = 34 then (2057097572214532263811571177454180874478299968000 : ℤ) else if j = 35 then (-4501331914656159954007225184662568325464729088000 : ℤ) else if j = 37 then (-34835227187623662397376378548099306500924627048000 : ℤ) else if j = 38 then (184495601370518247114757969344255180119022015360000 : ℤ) else if j = 40 then (-1101415452622120676469591504785354184176591375688000 : ℤ) else if j = 41 then (747722605066203164258105266369773294689895300825600 : ℤ) else if j = 43 then (19693341729559052467345927995043420807549410991200000 : ℤ) else if j = 44 then (-51139952288427432997912989126831010098106604270937600 : ℤ) else if j = 46 then (32617813554633633117086555470844862113561296324704000 : ℤ) else if j = 47 then (263372711985712692049325240962326700916815688722867200 : ℤ) else if j = 49 then (-2058525746758090875021976764000856309184599224508608000 : ℤ) else if j = 50 then (2412937782206829863419237445331394818863733208313088000 : ℤ) else if j = 52 then (9915553977833479956380385408629463262758725008532496000 : ℤ) else if j = 53 then (-26511327173370490816886735328639942820361490629217120000 : ℤ) else if j = 55 then (28606903632730625436985182580118094362979465651326400000 : ℤ) else if j = 56 then (47115177701094167832016589792277169004343409655456928000 : ℤ) else if j = 58 then (-384422791558273672314140950960578564850259408278225920000 : ℤ) else if j = 59 then (411685080382606938494063866375972181117843479791192960000 : ℤ) else if j = 61 then (973367193562821512854340595169927662648456628851690408000 : ℤ) else if j = 62 then (-2308232903146670352225540772482970161972683455775388288000 : ℤ) else if j = 64 then (1728968951733879230564581491285314182950662216074236612000 : ℤ) else if j = 65 then (2714623479711406687134104952525526417684210764265670784000 : ℤ) else if j = 67 then (-14701238377474246143613123013045335018478118818650083840000 : ℤ) else if j = 68 then (12389849818462825056214208067650660492343217445423568960000 : ℤ) else if j = 70 then (26987842982646473819052203259672035712321924470877748608000 : ℤ) else if j = 71 then (-49940376342804626606043244099307433762984647963099232768000 : ℤ) else if j = 73 then (16465768067146123267506023645938934752415011136049039360000 : ℤ) else if j = 74 then (52157872267111094697265421463054054724613889716606699904000 : ℤ) else if j = 76 then (-148289971118716740574860882742178823301871524037800181568000 : ℤ) else if j = 77 then (86478972275018320393150928108444776388417711213862591528000 : ℤ) else if j = 79 then (224602781961434755040581690175670092263515750564231750912000 : ℤ) else if j = 80 then (-311065291848690489769300772485365849847034439309448616064000 : ℤ) else if j = 82 then (0 : ℤ) else if j = 83 then (296043377499135113387892889400993005987330687728285984960000 : ℤ) else if j = 85 then (-440368287392909910155232502711256312858067503678902325184000 : ℤ) else if j = 86 then (144006820285826095610027500291127142408778738194097177728000 : ℤ) else if j = 88 then (571580816533595817899393166040901595889038693885772779360000 : ℤ) else if j = 89 then (-597056877744600235622370298826955242532128837266708460304000 : ℤ) else if j = 91 then (-125449816087406857971294006037991882155716442153875453542400 : ℤ) else if j = 92 then (494359330954013797687909445326704526005679425632246481312000 : ℤ) else if j = 94 then (-409815963722749396711560077205499900701834728643012853478400 : ℤ) else if j = 95 then (41478418916657430409957259573258034301811462250233214624000 : ℤ) else if j = 97 then (450055680500796256626893690020408794077171180296892676864000 : ℤ) else if j = 98 then (-367097871216111006689659083780845012452179982212891167040000 : ℤ) else if j = 100 then (-108301794880198876317371998218367756496575962997745954342400 : ℤ) else if j = 101 then (243304541061377581471602465280966980431057189839555958424000 : ℤ) else if j = 103 then (-127110280671573958376901895502817264872635815889813397760000 : ℤ) else if j = 104 then (-2798852923740802760579365885337503285976586084672778728000 : ℤ) else if j = 106 then (107107600006389940626379345262142693989766718688399265792000 : ℤ) else if j = 107 then (-73444753195582497414501486498442622139721151243567830944000 : ℤ) else if j = 109 then (-17495344436307141200302463315949413953145391799728505200000 : ℤ) else if j = 110 then (32922643316100023462499839318428569892119637698930642144000 : ℤ) else if j = 112 then (-13781675487565347751655995096413447596838046343748223416000 : ℤ) else if j = 113 then (857213713762758494812051401822854842990550494797894240000 : ℤ) else if j = 115 then (6785659883432768216156962485873853065306440284708697856000 : ℤ) else if j = 116 then (-4430117374254870638700703980345569696382051998846604451200 : ℤ) else if j = 118 then (-268800850889936886280036849321646671656039318144304320000 : ℤ) else if j = 119 then (921717101312316217618262609515239854336016800605278720000 : ℤ) else if j = 121 then (-433403158722473843253566667263976822578344734317168160000 : ℤ) else if j = 122 then (123448188653010283502101591746830951284223671302552844800 : ℤ) else if j = 124 then (70419702332270620948177641728362563938015580747707616000 : ℤ) else if j = 125 then (-52702853660419490600683374500913565206490336702153315200 : ℤ) else if j = 127 then (7226627455913411943460644324097011583790335695736512000 : ℤ) else if j = 128 then (581936225701576427424054749986689879413840460395100000 : ℤ) else if j = 130 then (-1610751426546523879570375874092860043677903876849024000 : ℤ) else if j = 131 then (762529770194441601340643009204029848155461726072320000 : ℤ) else if j = 133 then (-44275733105068675654276741228024021563482033157360000 : ℤ) else if j = 134 then (-9667098967519950951776933740236597333935364253440000 : ℤ) else if j = 136 then (6353314557021061493041602665596335305610467486304000 : ℤ) else if j = 137 then (-2284274427400514219769028588186717613052376869120000 : ℤ) else if j = 139 then (132279666220891666113542247783389712425447577792000 : ℤ) else if j = 140 then (-19950630916350277196758696709268157145746247040000 : ℤ) else 0

def cD : ℕ → ℤ := fun j => if j = 24 then (-46483068047658378213454288461813703442940 : ℤ) else if j = 25 then (2712256665212766827519573632383434958611556 : ℤ) else if j = 26 then (-19872292539929878338279072802971255720859800 : ℤ) else if j = 27 then (-153548252625009620621633237196253340483644380 : ℤ) else if j = 28 then (2085839751081657241582951200118738488449211756 : ℤ) else if j = 29 then (-5502718705528513404014561620126109497069489050 : ℤ) else if j = 30 then (-5447096376990463235038140271599958436610222540 : ℤ) else if j = 31 then (-14683413212378046837079921968561062965758690684 : ℤ) else if j = 32 then (106537211976323776648732354953866958292229167125 : ℤ) else if j = 33 then (2165145211358904294511325240371188838436585101860 : ℤ) else if j = 34 then (-12563049507824157751195642612882946846464318329164 : ℤ) else if j = 35 then (16408524177153522821958061573061524532008643005525 : ℤ) else if j = 36 then (8829091058907445661088829489404586460253191117820 : ℤ) else if j = 37 then (78409705969918035418292395064667161936461123991366 : ℤ) else if j = 38 then (-98914573131261549453368615563147576703903858340475 : ℤ) else if j = 39 then (-2039308776522193010180909670030459208744076651882820 : ℤ) else if j = 40 then (6561021647586720158586621556648241264486778257149296 : ℤ) else if j = 41 then (-5578469616273541807665755494119643512870246302103603 : ℤ) else if j = 42 then (12371190845197129595978579164758016920763081159033500 : ℤ) else if j = 43 then (-66027510927032687289279329849740941730231844621337704 : ℤ) else if j = 44 then (35641345446820979601176781366726220624776786592384885 : ℤ) else if j = 45 then (307195561108447897583230752865484852914456851333979500 : ℤ) else if j = 46 then (-489849362073972036145709215244696859844437389586324544 : ℤ) else if j = 47 then (462889558126530881217566280297655367214849509009929349 : ℤ) else if j = 48 then (-3308116921636846561559321548811474949600050841782244825 : ℤ) else if j = 49 then (8119332170444367408579480594941583865152167457563993136 : ℤ) else if j = 50 then (-3730209248692507653410022129469039350829167300644806491 : ℤ) else if j = 51 then (-1621731338078074790339629691083277061706338308509964265 : ℤ) else if j = 52 then (-15909674630346267654124789560985141758112461169991885524 : ℤ) else if j = 53 then (-9636565227819887717019271055410932194514598956256751191 : ℤ) else if j = 54 then (147536781539881102623396060970129643535680158559205358095 : ℤ) else if j = 55 then (-198353651543378956983442743835364176815964029016585587524 : ℤ) else if j = 56 then (144318337842316321149780445040494013984445183441352044589 : ℤ) else if j = 57 then (-590793500873857025141891418663081613427562483875618006925 : ℤ) else if j = 58 then (1122857557193018631103509212488311221606591326285494047676 : ℤ) else if j = 59 then (-179709193315342804371083308415185252764672024005020187811 : ℤ) else if j = 60 then (-651357457809460364016393092731624459102692970331286174105 : ℤ) else if j = 61 then (-671246962219025141066717433905068192919829169977974017354 : ℤ) else if j = 62 then (-1937606264726157961707594651636470626507482631771193904691 : ℤ) else if j = 63 then (10403691664585555132965478635381438777728327827448518673295 : ℤ) else if j = 64 then (-10753974715783486403010112634555642284958939634533979754649 : ℤ) else if j = 65 then (7133234821726728814432935261624647421836024204479781861149 : ℤ) else if j = 66 then (-23923454436143320677824118942271051157486844597471941051937 : ℤ) else if j = 67 then (33825828028921985764158655282198457165397953579264450243751 : ℤ) else if j = 68 then (1135678098720567259363525188535278997023104356656020983749 : ℤ) else if j = 69 then (-16068482916911268858566314419077277908263701808575712940883 : ℤ) else if j = 70 then (-11663343360645580415277268623403489764001077049598147043529 : ℤ) else if j = 71 then (-52185599491723839756965536707443750914624094042787850859131 : ℤ) else if j = 72 then (171170016829805659249252092377922998962026047571763495746921 : ℤ) else if j = 73 then (-133957289671491880959410380598597459474805205679648982605129 : ℤ) else if j = 74 then (97034829265527678957453059445499601818400565264017246843509 : ℤ) else if j = 75 then (-276904876316642497119971144076303904664479920189559803917295 : ℤ) else if j = 76 then (281782670453449084584728842343918755545016191514862539519551 : ℤ) else if j = 77 then (36872285176231911084935983805986038489434834521322803583739 : ℤ) else if j = 78 then (-64123415052263913007746215673722072884041114125964942194895 : ℤ) else if j = 79 then (-81239568474885880036509720654646112790930344012352427289569 : ℤ) else if j = 80 then (-357511482567354752322959017208865674258452206272339936029501 : ℤ) else if j = 81 then (794029795159880443113000384232439128343879351139027430823145 : ℤ) else if j = 82 then (-475789161980529469766595714901294239528725793450358240089569 : ℤ) else if j = 83 then (421330672150296994252225985382967149344791581316733871658099 : ℤ) else if j = 84 then (-973363461686183990485553695878655271585894310740012569059735 : ℤ) else if j = 85 then (706811613615179232353664016617762963075484758409816567361271 : ℤ) else if j = 86 then (121663658372598183530944343056377772416113885392993871024979 : ℤ) else if j = 87 then (-8560620070119773083461661160462365683280078036552852047015 : ℤ) else if j = 88 then (-151841707151642688649036146669840757482957133492566623037829 : ℤ) else if j = 89 then (-730066598591816393803238622187006625480596350371366769981361 : ℤ) else if j = 90 then (1139193189280227717059668229771631823589538832768110409270305 : ℤ) else if j = 91 then (-542557426084766459953619653085229596490905449337026139089541 : ℤ) else if j = 92 then (579035447996660102939220188673359910712300407996259885723159 : ℤ) else if j = 93 then (-1044368697673042705586649972559572618414113864302726897959795 : ℤ) else if j = 94 then (538096158255582297908556505367343189869376222447175309560267 : ℤ) else if j = 95 then (123020361825029036148401612174530549489143416050546169363199 : ℤ) else if j = 96 then (43210880584883267010314892764279586345269143946670297733200 : ℤ) else if j = 97 then (-48393914398700254711347646747988234069577361434844931349013 : ℤ) else if j = 98 then (-465249945532790046439831091742460445275351214495280728149201 : ℤ) else if j = 99 then (528183301637483923909537362068636546039812310681958964327920 : ℤ) else if j = 100 then (-208618258803990600264442743692135301033732019901563210910525 : ℤ) else if j = 101 then (231316948267179255963367296902172339183619346392175764204189 : ℤ) else if j = 102 then (-325773207829582395470595530810196747901355436408618666521760 : ℤ) else if j = 103 then (112949052686200131211782126763232282707316518686855433733475 : ℤ) else if j = 104 then (52072689592442973887742508999019519782808170597464224966859 : ℤ) else if j = 105 then (-3485422915131939794735717481276398652158098974219797533560 : ℤ) else if j = 106 then (9936232599706171896460207432726340811667413417413317727075 : ℤ) else if j = 107 then (-88502842663061331081969479265563796238544819501511721357981 : ℤ) else if j = 108 then (76661911797124539679135700067978103343047122845472082476240 : ℤ) else if j = 109 then (-24138034556175031174871706480379768776778906772471187170675 : ℤ) else if j = 110 then (21202266566836187262995678760451855674739581509030249352859 : ℤ) else if j = 111 then (-24570402402037645543656459387782146491811330829160735661920 : ℤ) else if j = 112 then (4045927380074814365605241780844877660585477982153337553650 : ℤ) else if j = 113 then (7376424710480115229430129776492718126476490671147751702259 : ℤ) else if j = 114 then (-3048514437565717187706646303201883797622508212044208670720 : ℤ) else if j = 115 then (1783403456727990356436946392489379218969295503052341994450 : ℤ) else if j = 116 then (-3957404244350174978283474463597189311416297777941158244169 : ℤ) else if j = 117 then (2714571471213184405309969537667410007578316083710297409140 : ℤ) else if j = 118 then (-479695409434650383378195989567311258167723154689513292550 : ℤ) else if j = 119 then (97430283804395499471552263640324558972385198890328466231 : ℤ) else if j = 120 then (-203769458709671259195685951516217962954678779830433600120 : ℤ) else if j = 121 then (-62560154065863425668124631080091680656976442226591939050 : ℤ) else if j = 122 then (186103445427064132762069554911849324437097853487835836743 : ℤ) else if j = 123 then (-83532749487425705308544368829010251072135191564181638920 : ℤ) else if j = 124 then (17834545685573062470904144713313537949665102170641429650 : ℤ) else if j = 125 then (-15580922566632234162623125765747920516243889908842505245 : ℤ) else if j = 126 then (8911528854626354154797462453152457236839911375863410600 : ℤ) else if j = 127 then (1500644218155509434482603579324669187172059589361531050 : ℤ) else if j = 128 then (-2866412250480011677165896504233264121634841319064740520 : ℤ) else if j = 129 then (864136492710306385371536570764440149771598649077533640 : ℤ) else if j = 130 then (-189053434775929595160183003111150103281815219899983750 : ℤ) else if j = 131 then (148426997188151138168098244924078425199175319106268600 : ℤ) else if j = 132 then (-47378404473224644226838285024467208493062698970152400 : ℤ) else if j = 133 then (-15135214530357272970651249280150344650497217975998500 : ℤ) else if j = 134 then (12404971272958564264022506929942365757933039297319560 : ℤ) else if j = 135 then (-2280244065556266299687404092086657093249006902306800 : ℤ) else if j = 136 then (-67663401291166856054327664549532240427544484599000 : ℤ) else if j = 137 then (46246979392015402335934020901584463852887474131640 : ℤ) else 0

def aIdx : Finset ℕ := {25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 73, 74, 76, 77, 79, 80, 82, 83, 85, 86, 88, 89, 91, 92, 94, 95, 97, 98, 100, 101, 103, 104, 106, 107, 109, 110, 112, 113, 115, 116, 118, 119, 121, 122, 124, 125, 127, 128, 130, 131, 133, 134, 136, 137, 139, 140}
def dIdx : Finset ℕ := {24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137}

/-! ## index bounds -/

lemma aIdx_bounds (j : ℕ) (hj : j ∈ aIdx) : 24 ≤ j ∧ j ≤ 140 := by
  simp only [aIdx, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

lemma dIdx_bounds (k : ℕ) (hk : k ∈ dIdx) : 24 ≤ k ∧ k ≤ 137 := by
  simp only [dIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  omega



def Sf (i : ℕ) : Finset ℕ := (Finset.range 24).image (fun j => 3 * j + i)

/-! ## polynomials -/

noncomputable def Dpol : ℤ[X] := ∏ τ ∈ Finset.range 117, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2
noncomputable def Qpol (i : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 117, (if τ ∈ Sf i then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Rpol (j : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 117, (if (24 + τ : ℕ) = j then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Tpol (k : ℕ) : ℤ[X] :=
  (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
    (∏ τ ∈ Finset.range 117, (if (24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3 then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)))
noncomputable def Ppol (i : ℕ) : ℤ[X] := ∏ j ∈ Finset.range 24, (C (3:ℤ) * X + C ((24 + 3 * j + i : ℕ) : ℤ))

noncomputable def P1 : ℤ[X] :=
  C ((52498185259417850763970702631828429551599349184611613115068256257741236945394073600000000 : ℤ)) *
    ((∏ r ∈ Finset.range 46, (Polynomial.X + C (((r : ℤ) + 1)))) *
    (∑ i ∈ Finset.range 48, C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) * Qpol i))

noncomputable def P2 : ℤ[X] :=
  C ((5502622159812088949850305428800254892961651752960000000000 : ℤ)) *
    ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k))

/-! ## generic product lemmas -/

lemma prod_ite_one_eq {ι M : Type*} [CommMonoid M] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (f : ι → M) :
    (∏ i ∈ s, (if p i then (1 : M) else f i)) = ∏ i ∈ s.filter (fun i => ¬ p i), f i := by
  rw [Finset.prod_ite]
  simp

lemma Sf_subset (i : ℕ) (hi : i < 48) : Sf i ⊆ Finset.range 117 := by
  intro τ hτ
  simp only [Sf, Finset.mem_image, Finset.mem_range] at hτ ⊢
  obtain ⟨j, hj, rfl⟩ := hτ
  omega

lemma Sf_card (i : ℕ) : (Sf i).card = 24 := by
  rw [Sf, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have h : 3 * x + i = 3 * y + i := hxy
    omega

lemma prod_Sf_eq (i : ℕ) (F : ℕ → ℤ[X]) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 24, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma Ppol_sq_eq (i : ℕ) :
    (Ppol i) ^ 2 = ∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Ppol, prod_Sf_eq i (fun τ => (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  have h : (24 + (3 * j + i) : ℕ) = 24 + 3 * j + i := by omega
  rw [h]

lemma Qpol_eq (i : ℕ) (hi : i < 48) :
    Qpol i = ∏ τ ∈ (Finset.range 117) \ Sf i, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Qpol, prod_ite_one_eq, Finset.sdiff_eq_filter]

lemma prod_range_split (i : ℕ) (hi : i < 48) (F : ℕ → ℤ[X]) :
    (∏ τ ∈ Finset.range 117, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 117) \ Sf i, F τ) := by
  rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset (Sf_subset i hi)]

lemma Dpol_split (i : ℕ) (hi : i < 48) :
    Dpol = (∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2) *
      (∏ τ ∈ (Finset.range 117) \ Sf i, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2) := by
  unfold Dpol
  exact prod_range_split i hi _

lemma Dpol_eq_Ppol_sq_mul_Qpol (i : ℕ) (hi : i < 48) : Dpol = Ppol i ^ 2 * Qpol i := by
  rw [Dpol_split i hi, ← Ppol_sq_eq i, ← Qpol_eq i hi]

lemma Rpol_eq (j : ℕ) :
    Rpol j = ∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = j)),
      (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Rpol, prod_ite_one_eq]

lemma prod_filter_step (j : ℕ) :
    (∏ τ ∈ Finset.range 117, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 117).filter (fun τ => (24 + τ : ℕ) = j),
            (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = j)),
            (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 117) (fun τ => (24 + τ : ℕ) = j) _).symm

lemma filter_eq_singleton (j : ℕ) (h1 : 24 ≤ j) (h2 : j ≤ 140) :
    (Finset.range 117).filter (fun τ => (24 + τ : ℕ) = j) = {j - 24} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hj⟩; omega
  · rintro rfl; constructor <;> omega

lemma Dpol_eq_sq_mul_Rpol (j : ℕ) (h1 : 24 ≤ j) (h2 : j ≤ 140) :
    Dpol = (C (3:ℤ) * X + C (j : ℤ)) ^ 2 * Rpol j := by
  rw [Dpol, prod_filter_step j, Rpol_eq j, filter_eq_singleton j h1 h2, Finset.prod_singleton]
  have e : ((24 + (j - 24) : ℕ) : ℤ) = (j : ℤ) := by omega
  rw [e]

lemma prod_filter_step2 (k : ℕ) :
    (∏ τ ∈ Finset.range 117, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 117).filter (fun τ => ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 117)
    (fun τ => ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)) _).symm

lemma filter_eq_pair (k : ℕ) (h1 : 24 ≤ k) (h2 : k ≤ 137) :
    (Finset.range 117).filter (fun τ => ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)) = {k - 24, k - 21} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hk | hk⟩
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> constructor <;> omega

lemma Dpol_eq_lin_mul_Tpol (k : ℕ) (h1 : 24 ≤ k) (h2 : k ≤ 137) :
    Dpol = (C (3:ℤ) * X + C (k : ℤ)) * (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) * Tpol k := by
  have hne : k - 24 ∉ ({k - 21} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [Tpol, prod_ite_one_eq, Dpol, prod_filter_step2 k, filter_eq_pair k h1 h2,
    Finset.prod_insert hne, Finset.prod_singleton]
  have e1 : ((24 + (k - 24) : ℕ) : ℤ) = (k : ℤ) := by omega
  have e2 : ((24 + (k - 21) : ℕ) : ℤ) = ((k + 3 : ℕ) : ℤ) := by omega
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
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 2 * s.card := by
  have h1 : (∏ τ ∈ s, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤
      ∑ τ ∈ s, ((C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2).natDegree :=
    Polynomial.natDegree_prod_le s (fun τ => (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)
  have h2 : (∑ τ ∈ s, ((C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2).natDegree) ≤ ∑ _τ ∈ s, 2 :=
    Finset.sum_le_sum (fun τ _ => natDegree_sq_lin_le _)
  have h3 : (∑ _τ ∈ s, (2 : ℕ)) = 2 * s.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  linarith

lemma natDegree_prod_sq_le_234 (s : Finset ℕ) (h : s.card ≤ 117) :
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 234 :=
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
    ((Finset.range 117).filter p).card ≤ 117 := by
  have h := Finset.card_le_card (Finset.filter_subset p (Finset.range 117))
  rwa [Finset.card_range] at h

lemma card_sdiff_le (s : Finset ℕ) : ((Finset.range 117) \ s).card ≤ 117 := by
  have h := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range 117) (t := s))
  rwa [Finset.card_range] at h

lemma natDegree_Qpol_le (i : ℕ) (hi : i < 48) : (Qpol i).natDegree ≤ 234 := by
  rw [Qpol_eq i hi]
  exact natDegree_prod_sq_le_234 _ (card_sdiff_le _)

lemma natDegree_Rpol_le (j : ℕ) : (Rpol j).natDegree ≤ 234 := by
  rw [Rpol_eq j]
  exact natDegree_prod_sq_le_234 _ (filter_card_le _)

lemma Tpol_eq' (k : ℕ) :
    Tpol k = (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)) := by
  rw [Tpol, prod_ite_one_eq]

lemma natDegree_Tpol_le (k : ℕ) : (Tpol k).natDegree ≤ 236 := by
  have h1 : (Tpol k).natDegree ≤ (C (3:ℤ) * X + C (k : ℤ)).natDegree +
      ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
        (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
          (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)).natDegree := by
    rw [Tpol_eq' k]
    exact Polynomial.natDegree_mul_le
  have h2 : ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2)).natDegree ≤ 1 + 234 := by
    have hm := Polynomial.natDegree_mul_le (p := (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)))
      (q := (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2))
    have ha : (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
    have hb : (∏ τ ∈ (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((24 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 234 :=
      natDegree_prod_sq_le_234 _ (filter_card_le _)
    linarith
  have h3 : (C (3:ℤ) * X + C (k : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
  linarith

lemma natDegree_P1_le : P1.natDegree ≤ 280 := by
  have h1 : P1.natDegree ≤ (C ((8862938119652501095929 : ℤ) * (2433791034887445720403237601280000 : ℤ) ^ 2)).natDegree +
      ((∏ r ∈ Finset.range 46, (Polynomial.X + C (((r : ℤ) + 1)))) *
        (∑ i ∈ Finset.range 48,
          C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) * Qpol i)).natDegree := by
    rw [P1]
    exact Polynomial.natDegree_mul_le
  have h2 : ((∏ r ∈ Finset.range 46, (Polynomial.X + C (((r : ℤ) + 1)))) *
      (∑ i ∈ Finset.range 48,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) * Qpol i)).natDegree ≤ 46 + 234 := by
    refine le_trans (Polynomial.natDegree_mul_le) (add_le_add ?_ ?_)
    · have hp : (∏ r ∈ Finset.range 46, (Polynomial.X + C (((r : ℤ) + 1)))).natDegree ≤
          ∑ r ∈ Finset.range 46, (Polynomial.X + C (((r : ℤ) + 1))).natDegree :=
        Polynomial.natDegree_prod_le _ _
      have hq : (∑ r ∈ Finset.range 46, (Polynomial.X + C (((r : ℤ) + 1))).natDegree) = 46 := by
        rw [Finset.sum_congr rfl (fun r _ => Polynomial.natDegree_X_add_C _)]
        simp
      omega
    · exact natDegree_sum_le' _ _ 234 (fun i hi => by
        rw [Finset.mem_range] at hi
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Qpol_le i hi))
  have h3 : (C ((8862938119652501095929 : ℤ) * (2433791034887445720403237601280000 : ℤ) ^ 2)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma natDegree_P2_le : P2.natDegree ≤ 236 := by
  have h1 : P2.natDegree ≤ (C ((5502622159812088949850305428800254892961651752960000000000 : ℤ))).natDegree +
      ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree := by
    rw [P2]
    exact Polynomial.natDegree_mul_le
  have hR : (∑ j ∈ aIdx, C (cA j) * Rpol j).natDegree ≤ 234 :=
    natDegree_sum_le' _ _ 234 (fun j _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Rpol_le j))
  have hT : (∑ k ∈ dIdx, C (cD k) * Tpol k).natDegree ≤ 236 :=
    natDegree_sum_le' _ _ 236 (fun k _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Tpol_le k))
  have h2 : ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree ≤
      236 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (le_trans hR (by norm_num)) hT)
  have h3 : (C ((5502622159812088949850305428800254892961651752960000000000 : ℤ))).natDegree = 0 := Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma degree_bound : max P1.natDegree P2.natDegree < 281 := by
  rw [max_lt_iff]
  constructor
  · exact lt_of_le_of_lt natDegree_P1_le (by norm_num)
  · exact lt_of_le_of_lt natDegree_P2_le (by norm_num)

/-! ## evaluation of the polynomials (integer form) -/

def EvP1 (c : ℤ) : ℤ := (8862938119652501095929 * 2433791034887445720403237601280000 ^ 2) *
  ((∏ r ∈ Finset.range 46, (c + ((r : ℤ) + 1))) *
   (∑ i ∈ Finset.range 48, (Lc * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) *
     (∏ τ ∈ Finset.range 117, (if τ ∈ Sf i then 1 else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2))))

def EvP2 (c : ℤ) : ℤ := 5502622159812088949850305428800254892961651752960000000000 *
  ((∑ j ∈ aIdx, cA j * (∏ τ ∈ Finset.range 117, (if (24 + τ : ℕ) = j then 1 else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2)))
   + (∑ k ∈ dIdx, cD k * ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) * (∏ τ ∈ Finset.range 117, (if (24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3 then 1 else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2)))))

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

def Pall (c : ℤ) : ℤ := ∏ τ ∈ Finset.range 117, (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2

lemma prod_Sf_eqZ (i : ℕ) (F : ℕ → ℤ) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 24, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma prod_range_splitZ (i : ℕ) (hi : i < 48) (F : ℕ → ℤ) :
    (∏ τ ∈ Finset.range 117, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 117) \ Sf i, F τ) := by
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

lemma filter_not_eq_erase (j : ℕ) (h1 : 24 ≤ j) (h2 : j ≤ 140) :
    (Finset.range 117).filter (fun τ => ¬ ((24 + τ : ℕ) = j)) =
      (Finset.range 117).erase (j - 24) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨hlt, hne⟩
    exact ⟨fun h => hne (by omega), hlt⟩
  · rintro ⟨hne, hlt⟩
    exact ⟨hlt, fun h => hne (by omega)⟩

lemma filter_not_pair_eq_erase (k : ℕ) (h1 : 24 ≤ k) (h2 : k ≤ 137) :
    (Finset.range 117).filter
        (fun τ => ¬ ((24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3)) =
      ((Finset.range 117).erase (k - 24)).erase (k - 21) := by
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

lemma prod_ite_eq_div {c : ℤ} (hc : 0 ≤ c) (j : ℕ) (h1 : 24 ≤ j) (h2 : j ≤ 140) :
    (∏ τ ∈ Finset.range 117,
        (if (24 + τ : ℕ) = j then (1 : ℤ)
          else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (3 * c + ((24 + (j - 24) : ℕ) : ℤ)) ^ 2 := by
  have hmem : j - 24 ∈ Finset.range 117 := by
    simp only [Finset.mem_range]; omega
  have hne : (3 * c + ((24 + (j - 24) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hj : (24 + (j - 24) : ℕ) = j := by omega
    rw [hj]; exact sqf_ne_zero hc (by omega : 0 < j)
  rw [prod_ite_one_eq, filter_not_eq_erase j h1 h2, Pall]
  exact prod_erase_eq_div _ _ hmem _ hne

lemma prod_ite_pair_eq_div {c : ℤ} (hc : 0 ≤ c) (k : ℕ) (h1 : 24 ≤ k)
    (h2 : k ≤ 137) :
    (∏ τ ∈ Finset.range 117,
        (if (24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3 then (1 : ℤ)
          else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / ((3 * c + ((24 + (k - 24) : ℕ) : ℤ)) ^ 2 *
          (3 * c + ((24 + (k - 21) : ℕ) : ℤ)) ^ 2) := by
  have hmem1 : k - 24 ∈ Finset.range 117 := by
    simp only [Finset.mem_range]; omega
  have hmem2 : k - 21 ∈ (Finset.range 117).erase (k - 24) := by
    simp only [Finset.mem_erase, Finset.mem_range]
    constructor
    · omega
    · omega
  have hne1 : (3 * c + ((24 + (k - 24) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (24 + (k - 24) : ℕ) = k := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k)
  have hne2 : (3 * c + ((24 + (k - 21) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (24 + (k - 21) : ℕ) = k + 3 := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k + 3)
  rw [prod_ite_one_eq, filter_not_pair_eq_erase k h1 h2, Pall]
  exact prod_erase_pair_eq_div _ _ _ hmem1 hmem2 _ hne1 hne2

lemma prod_ite_Sf_eq_div {c : ℤ} (hc : 0 ≤ c) (i : ℕ) (hi : i < 48) :
    (∏ τ ∈ Finset.range 117,
        (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (∏ j ∈ Finset.range 24,
          (3 * c + ((24 + (3 * j + i) : ℕ) : ℤ)) ^ 2) := by
  have hSf : (∏ τ ∈ Sf i, (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ j ∈ Finset.range 24, (3 * c + ((24 + (3 * j + i) : ℕ) : ℤ)) ^ 2) :=
    prod_Sf_eqZ i _
  have hne : (∏ j ∈ Finset.range 24,
      (3 * c + ((24 + (3 * j + i) : ℕ) : ℤ)) ^ 2) ≠ 0 := by
    rw [← hSf]
    exact Finset.prod_ne_zero_iff.mpr (fun τ _ => sqf_ne_zero hc (by omega : 0 < 24 + τ))
  have hsplit : Pall c =
      (∏ j ∈ Finset.range 24, (3 * c + ((24 + (3 * j + i) : ℕ) : ℤ)) ^ 2) *
        (∏ τ ∈ (Finset.range 117) \ Sf i,
          (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2) := by
    rw [Pall, prod_range_splitZ i hi, hSf]
  rw [prod_ite_one_eq, ← Finset.sdiff_eq_filter, hsplit,
    Int.mul_ediv_cancel_left _ hne]

def EvP1cheap (c : ℤ) : ℤ :=
  (8862938119652501095929 * 2433791034887445720403237601280000 ^ 2) *
    ((∏ r ∈ Finset.range 46, (c + ((r : ℤ) + 1))) *
     (∑ i ∈ Finset.range 48, (Lc * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) *
       (Pall c / (∏ j ∈ Finset.range 24,
         (3 * c + ((24 + (3 * j + i) : ℕ) : ℤ)) ^ 2))))

def EvP2cheap (c : ℤ) : ℤ :=
  (5502622159812088949850305428800254892961651752960000000000) *
    ((∑ j ∈ aIdx, cA j * (Pall c / (3 * c + ((24 + (j - 24) : ℕ) : ℤ)) ^ 2))
     + (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((24 + (k - 24) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((24 + (k - 21) : ℕ) : ℤ)) ^ 2)))))

lemma EvP1_sum_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ i ∈ Finset.range 48, (Lc * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) *
        (∏ τ ∈ Finset.range 117,
          (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ i ∈ Finset.range 48, (Lc * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) *
        (Pall c / (∏ j ∈ Finset.range 24,
          (3 * c + ((24 + (3 * j + i) : ℕ) : ℤ)) ^ 2))) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [prod_ite_Sf_eq_div hc i hi]

lemma EvP2_sum1_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ j ∈ aIdx, cA j *
        (∏ τ ∈ Finset.range 117,
          (if (24 + τ : ℕ) = j then (1 : ℤ)
            else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ j ∈ aIdx, cA j *
        (Pall c / (3 * c + ((24 + (j - 24) : ℕ) : ℤ)) ^ 2)) := by
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨h1, h2⟩ := aIdx_bounds j hj
  rw [prod_ite_eq_div hc j h1 h2]

lemma EvP2_sum2_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ k ∈ dIdx, cD k *
        ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
          (∏ τ ∈ Finset.range 117,
            (if (24 + τ : ℕ) = k ∨ (24 + τ : ℕ) = k + 3 then (1 : ℤ)
              else (3 * c + ((24 + τ : ℕ) : ℤ)) ^ 2))))
      = (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((24 + (k - 24) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((24 + (k - 21) : ℕ) : ℤ)) ^ 2)))) := by
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

noncomputable def pts : Finset ℤ := (Finset.range 281).image (fun k : ℕ => (k : ℤ))

lemma pts_card : pts.card = 281 := by
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
  · rw [pts_card]
    exact degree_bound

def Df (m : ℕ) : ℤ := (Dpol).eval (m : ℤ)
def Pf (i : ℕ) (m : ℕ) : ℤ := (Ppol i).eval (m : ℤ)
def Qf (i : ℕ) (m : ℕ) : ℤ := (Qpol i).eval (m : ℤ)
def Rf (j : ℕ) (m : ℕ) : ℤ := (Rpol j).eval (m : ℤ)
def Tf (k : ℕ) (m : ℕ) : ℤ := (Tpol k).eval (m : ℤ)

lemma Pf_pos (i m : ℕ) (hi : i < 48) : 0 < Pf i m := by
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

lemma Df_eq_Pf_sq_mul_Qf (i m : ℕ) (hi : i < 48) : Df m = (Pf i m) ^ 2 * Qf i m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_Ppol_sq_mul_Qpol i hi)
  simpa [Df, Pf, Qf, Polynomial.eval_mul, Polynomial.eval_pow] using h

lemma Df_eq_sq_mul_Rf (j m : ℕ) (h1 : 24 ≤ j) (h2 : j ≤ 140) :
    Df m = (3 * (m : ℤ) + (j : ℤ)) ^ 2 * Rf j m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_sq_mul_Rpol j h1 h2)
  simpa [Df, Rf, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

lemma Df_eq_lin_mul_Tf (k m : ℕ) (h1 : 24 ≤ k) (h2 : k ≤ 137) :
    Df m = (3 * (m : ℤ) + (k : ℤ)) * (3 * (m : ℤ) + ((k + 3 : ℕ) : ℤ)) * Tf k m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_lin_mul_Tpol k h1 h2)
  simpa [Df, Tf, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h


/-! ## real-valued definitions -/

noncomputable def cTwentyThreePf (i : ℕ) (m : ℕ) : ℝ := ∏ j ∈ Finset.range 24, xm m (24 + 3 * j + i)

noncomputable def Vm23 (m : ℕ) : ℝ := (8862938119652501095929 : ℝ) * (Nat.choose (m + 46) 46 : ℝ) *
  (∑ i ∈ Finset.range 48, ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
    (2433791034887445720403237601280000 / cTwentyThreePf i m) ^ 2)

noncomputable def aj (j : ℕ) : ℝ := (cA j : ℝ) / (Lc : ℝ)
noncomputable def dj (k : ℕ) : ℝ := (cD k : ℝ) / (3 * (Lc : ℝ))

noncomputable def W123 (m : ℕ) : ℝ := ∑ j ∈ aIdx, aj j / (xm m j) ^ 2
noncomputable def W223 (m : ℕ) : ℝ := ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))
noncomputable def Vd23 (m : ℕ) : ℝ := W123 m + W223 m

lemma cTwentyThreePf_eq (i m : ℕ) : cTwentyThreePf i m = ((Pf i m : ℤ) : ℝ) := by
  have h : ((Pf i m : ℤ) : ℝ) = ∏ j ∈ Finset.range 24,
      ((3 : ℝ) * (m : ℝ) + ((24 + 3 * j + i : ℕ) : ℝ)) := by
    rw [Pf, Ppol, Polynomial.eval_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    ring
  rw [h, cTwentyThreePf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [xm_eq]

lemma eval_prodP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∏ r ∈ Finset.range 46, (Polynomial.X + C ((r : ℤ) + 1))) =
      ∏ r ∈ Finset.range 46, ((m : ℤ) + (r + 1)) := by
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

lemma eval_sumP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∑ i ∈ Finset.range 48,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ)) * Qpol i) =
      ∑ i ∈ Finset.range 48, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ) * (Qf i m) := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.eval_mul, Polynomial.eval_C, Qf]

lemma eval_P1_int (m : ℕ) :
    P1.eval (m : ℤ) = (8862938119652501095929 * 2433791034887445720403237601280000 ^ 2) *
      (∏ r ∈ Finset.range 46, ((m : ℤ) + (r + 1))) *
      (∑ i ∈ Finset.range 48, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 47 i : ℤ) * (Qf i m)) := by
  rw [P1, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_prodP m, eval_sumP m]
  ring

lemma eval_P1 (m : ℕ) :
    ((P1.eval (m : ℤ) : ℤ) : ℝ) = (8862938119652501095929 : ℝ) * (2433791034887445720403237601280000 : ℝ) ^ 2 *
      (∏ r ∈ Finset.range 46, ((m : ℝ) + (r + 1))) *
      (∑ i ∈ Finset.range 48, (Lc : ℝ) * (-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ) * ((Qf i m : ℤ) : ℝ)) := by
  rw [eval_P1_int m]
  push_cast
  ring

lemma eval_P2_int (m : ℕ) :
    P2.eval (m : ℤ) = 5502622159812088949850305428800254892961651752960000000000 *
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
    ((P2.eval (m : ℤ) : ℤ) : ℝ) = (5502622159812088949850305428800254892961651752960000000000 : ℝ) *
      ((∑ j ∈ aIdx, (cA j : ℝ) * ((Rf j m : ℤ) : ℝ)) +
        (∑ k ∈ dIdx, (cD k : ℝ) * ((Tf k m : ℤ) : ℝ))) := by
  rw [eval_P2_int m]
  push_cast
  ring


/-! ## the factorial identity -/

lemma choose_fact_nat (m : ℕ) :
    (m + 46).choose 46 * (46 !) = ∏ r ∈ Finset.range 46, (m + r + 1) := by
  have h2 : (m + 1).ascFactorial 46 = 46 ! * (m + 46).choose 46 := by
    simpa using Nat.ascFactorial_eq_factorial_mul_choose m 46
  have h1 : (m + 1).ascFactorial 46 = ∏ i ∈ Finset.range 46, (m + 1 + i) :=
    Nat.ascFactorial_eq_prod_range (m + 1) 46
  rw [h2, Nat.mul_comm] at h1
  rw [h1]
  apply Finset.prod_congr rfl
  intro r hr
  omega

lemma choose_fact (m : ℕ) :
    (Nat.choose (m + 46) 46 : ℝ) * 5502622159812088949850305428800254892961651752960000000000 = ∏ r ∈ Finset.range 46, ((m : ℝ) + (r + 1)) := by
  have h : ((m + 46).choose 46 : ℝ) * ((46 ! : ℕ) : ℝ) =
      ((∏ r ∈ Finset.range 46, (m + r + 1) : ℕ) : ℝ) := by
    exact_mod_cast choose_fact_nat m
  have h24 : ((46 ! : ℕ) : ℝ) = 5502622159812088949850305428800254892961651752960000000000 := by norm_num
  rw [h24] at h
  rw [h]
  push_cast
  apply Finset.prod_congr rfl
  intro r hr
  ring


/-! ## the two clearing identities -/

lemma clear_left (m : ℕ) :
    Vm23 m * ((Df m : ℤ) : ℝ) * 5502622159812088949850305428800254892961651752960000000000 * (Lc : ℝ) =
      ((P1.eval (m : ℤ) : ℤ) : ℝ) := by
  have hgoal : Vm23 m * ((Df m : ℤ) : ℝ) * 5502622159812088949850305428800254892961651752960000000000 * (Lc : ℝ) =
      (8862938119652501095929 : ℝ) * ((Nat.choose (m + 46) 46 : ℝ) * 5502622159812088949850305428800254892961651752960000000000) *
        ((∑ i ∈ Finset.range 48, ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
            (2433791034887445720403237601280000 / cTwentyThreePf i m) ^ 2) * ((Df m : ℤ) : ℝ)) * (Lc : ℝ) := by
    rw [Vm23]
    ring
  have hsum : (∑ i ∈ Finset.range 48, ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
        (2433791034887445720403237601280000 / cTwentyThreePf i m) ^ 2) * ((Df m : ℤ) : ℝ) =
      (2433791034887445720403237601280000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 48,
        ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cTwentyThreePf_eq i m]
    have hD : ((Df m : ℤ) : ℝ) = ((((Pf i m : ℤ)) : ℝ)) ^ 2 * ((Qf i m : ℤ) : ℝ) := by
      rw [Df_eq_Pf_sq_mul_Qf i m hi]
      simp only [Int.cast_mul, Int.cast_pow]
    rw [hD]
    have hne : (((Pf i m : ℤ)) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Pf_pos i m hi))
    field_simp
    try ring
  have hLc2 : ((2433791034887445720403237601280000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 48,
        ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ) =
      (2433791034887445720403237601280000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 48,
        (Lc : ℝ) * ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [show ((2433791034887445720403237601280000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 48,
          ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
        = (2433791034887445720403237601280000 : ℝ) ^ 2 * ((Lc : ℝ) * (∑ i ∈ Finset.range 48,
          ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) by ring]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hgoal, choose_fact m, hsum, eval_P1 m]
  rw [show (8862938119652501095929 : ℝ) * (∏ r ∈ Finset.range 46, ((m : ℝ) + (r + 1))) *
        ((2433791034887445720403237601280000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 48,
          ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
      = (8862938119652501095929 : ℝ) * (∏ r ∈ Finset.range 46, ((m : ℝ) + (r + 1))) *
        (((2433791034887445720403237601280000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 48,
          ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)) by ring]
  rw [hLc2]
  ring

lemma clear_right (m : ℕ) :
    Vd23 m * ((Df m : ℤ) : ℝ) * 5502622159812088949850305428800254892961651752960000000000 * (Lc : ℝ) =
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
  rw [eval_P2 m, Vd23]
  rw [show (W123 m + W223 m) * ((Df m : ℤ) : ℝ) * 5502622159812088949850305428800254892961651752960000000000 * (Lc : ℝ) =
      ((∑ j ∈ aIdx, aj j / (xm m j) ^ 2) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) +
        (∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) * ((Df m : ℤ) : ℝ) * (Lc : ℝ)) *
        5502622159812088949850305428800254892961651752960000000000 by
    rw [W123, W223]
    ring]
  rw [hW1, hW2]
  ring

theorem vm23_decomp (m : ℕ) : Vm23 m = Vd23 m := by
  have h1 := clear_left m
  have h2 := clear_right m
  have hP : ((P1.eval (m : ℤ) : ℤ) : ℝ) = ((P2.eval (m : ℤ) : ℤ) : ℝ) := by rw [poly_eq]
  have hDf : ((Df m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Df_pos m))
  have hFT : (5502622159812088949850305428800254892961651752960000000000 : ℝ) ≠ 0 := by norm_num
  have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
  have h := h1.trans (hP.trans h2.symm)
  have h' : (Vm23 m * ((Df m : ℤ) : ℝ)) * 5502622159812088949850305428800254892961651752960000000000 =
      (Vd23 m * ((Df m : ℤ) : ℝ)) * 5502622159812088949850305428800254892961651752960000000000 := mul_right_cancel₀ hLc h
  have h'' : Vm23 m * ((Df m : ℤ) : ℝ) = Vd23 m * ((Df m : ℤ) : ℝ) := mul_right_cancel₀ hFT h'
  exact mul_right_cancel₀ hDf h''

lemma denom_statement23 (m : ℕ) (i : ℕ) :
    (((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ) * ((3 * m + 84 + i : ℕ) : ℝ) * ((3 * m + 87 + i : ℕ) : ℝ) * ((3 * m + 90 + i : ℕ) : ℝ) * ((3 * m + 93 + i : ℕ) : ℝ))
      = cTwentyThreePf i m := by
  rw [cTwentyThreePf]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  simp only [xm_eq]
  push_cast
  ring

lemma inner_sum_statement23 (m : ℕ) :
    (∑ i ∈ Finset.range 48,
      ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
        (2433791034887445720403237601280000 / (((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ) * ((3 * m + 84 + i : ℕ) : ℝ) * ((3 * m + 87 + i : ℕ) : ℝ) * ((3 * m + 90 + i : ℕ) : ℝ) * ((3 * m + 93 + i : ℕ) : ℝ))) ^ 2)
    = (∑ i ∈ Finset.range 48,
      ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
        (2433791034887445720403237601280000 / cTwentyThreePf i m) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [denom_statement23 m i]

lemma vm23_eq_statement (m : ℕ) :
    (8862938119652501095929 : ℝ) * (Nat.choose (m + 46) 46 : ℝ) *
      (∑ i ∈ Finset.range 48,
        ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
          (2433791034887445720403237601280000 / (((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ) * ((3 * m + 84 + i : ℕ) : ℝ) * ((3 * m + 87 + i : ℕ) : ℝ) * ((3 * m + 90 + i : ℕ) : ℝ) * ((3 * m + 93 + i : ℕ) : ℝ))) ^ 2) =
      Vm23 m := by
  rw [Vm23, inner_sum_statement23 m]

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

def cAval (j : ℕ) : ℝ := if j % 3 = 1 then (A - Asum (j / 3)) else (B - Bsum (j / 3))
def cDval (k : ℕ) : ℝ := 1 / xm 0 k

noncomputable def V1val23 : ℝ := ∑ j ∈ aIdx, aj j * cAval j
noncomputable def V2val23 : ℝ := ∑ k ∈ dIdx, dj k * cDval k
noncomputable def Vval23 : ℝ := V1val23 + V2val23

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

lemma hasSum_W123 : HasSum W123 V1val23 := by
  change HasSum (fun m => ∑ j ∈ aIdx, aj j / (xm m j) ^ 2) V1val23
  rw [V1val23]
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

lemma hasSum_W223 : HasSum W223 V2val23 := by
  change HasSum (fun m => ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) V2val23
  rw [V2val23]
  apply hasSum_finset_sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := dIdx_bounds k hk
  have hh := (CdtTwoCore.hasSum_pair k (by omega)).mul_left (dj k)
  simpa [cDval, div_eq_mul_inv, mul_comm] using hh

lemma hasSum_Vm23 : HasSum Vm23 Vval23 := by
  have hsum : HasSum (fun m => W123 m + W223 m) Vval23 := by
    simpa [Vval23] using hasSum_W123.add hasSum_W223
  refine hsum.congr_fun (fun m => ?_)
  exact vm23_decomp m


set_option maxHeartbeats 0 in
lemma tsum_Vm23 : (∑' m : ℕ, Vm23 m) = 157626238006835196237 * A - 157626238006835196237 * B - 21793477080637841759891355106455157611 / 176961524070531200 := by
  have hval : Vval23 = 157626238006835196237 * A - 157626238006835196237 * B - 21793477080637841759891355106455157611 / 176961524070531200 := by
    unfold Vval23 V1val23 V2val23
    simp (maxSteps := 100000000) only [cAval, cDval, aj, dj, cA, cD, Lc, aIdx, dIdx, xm_eq,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      not_false_eq_true, asum0, asum1, asum2, asum3, asum4, asum5, asum6, asum7, asum8, asum9, asum10, asum11, asum12, asum13, asum14, asum15, asum16, asum17, asum18, asum19, asum20, asum21, asum22, asum23, asum24, asum25, asum26, asum27, asum28, asum29, asum30, asum31, asum32, asum33, asum34, asum35, asum36, asum37, asum38, asum39, asum40, asum41, asum42, asum43, asum44, asum45, asum46,
      bsum0, bsum1, bsum2, bsum3, bsum4, bsum5, bsum6, bsum7, bsum8, bsum9, bsum10, bsum11, bsum12, bsum13, bsum14, bsum15, bsum16, bsum17, bsum18, bsum19, bsum20, bsum21, bsum22, bsum23, bsum24, bsum25, bsum26, bsum27, bsum28, bsum29, bsum30, bsum31, bsum32, bsum33, bsum34, bsum35, bsum36, bsum37, bsum38, bsum39, bsum40, bsum41, bsum42, bsum43, bsum44, bsum45, bsum46]
    norm_num (maxSteps := 100000000)
    ring
  rw [hasSum_Vm23.tsum_eq]
  exact hval

end CdtTwentyThreeCore
open CdtTwentyThreeCore

theorem sum_cintegralTwentyThree_core :
    (∑' m : ℕ,
        (8862938119652501095929 : ℝ) * (Nat.choose (m + 46) 46 : ℝ) *
          (∑ i ∈ Finset.range 48,
            ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
              (2433791034887445720403237601280000 / (((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ) * ((3 * m + 84 + i : ℕ) : ℝ) * ((3 * m + 87 + i : ℕ) : ℝ) * ((3 * m + 90 + i : ℕ) : ℝ) * ((3 * m + 93 + i : ℕ) : ℝ))) ^ 2)) =
      157626238006835196237 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 21793477080637841759891355106455157611 / 176961524070531200 := by
  have hMain := tsum_Vm23
  have hL : (∑' m : ℕ, Vm23 m) = (∑' m : ℕ,
        (8862938119652501095929 : ℝ) * (Nat.choose (m + 46) 46 : ℝ) *
          (∑ i ∈ Finset.range 48,
            ((-1 : ℝ) ^ i * (Nat.choose 47 i : ℝ)) *
              (2433791034887445720403237601280000 / (((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ) * ((3 * m + 48 + i : ℕ) : ℝ) * ((3 * m + 51 + i : ℕ) : ℝ) * ((3 * m + 54 + i : ℕ) : ℝ) * ((3 * m + 57 + i : ℕ) : ℝ) * ((3 * m + 60 + i : ℕ) : ℝ) * ((3 * m + 63 + i : ℕ) : ℝ) * ((3 * m + 66 + i : ℕ) : ℝ) * ((3 * m + 69 + i : ℕ) : ℝ) * ((3 * m + 72 + i : ℕ) : ℝ) * ((3 * m + 75 + i : ℕ) : ℝ) * ((3 * m + 78 + i : ℕ) : ℝ) * ((3 * m + 81 + i : ℕ) : ℝ) * ((3 * m + 84 + i : ℕ) : ℝ) * ((3 * m + 87 + i : ℕ) : ℝ) * ((3 * m + 90 + i : ℕ) : ℝ) * ((3 * m + 93 + i : ℕ) : ℝ))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm23_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation