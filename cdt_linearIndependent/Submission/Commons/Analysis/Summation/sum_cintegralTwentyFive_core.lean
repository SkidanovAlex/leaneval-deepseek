import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Submission.Commons.Analysis.Summation.sum_cintegralTwo_core_corrected
import Submission.Commons.Analysis.Summation.cintegralTwentyFive_evc_0
import Submission.Commons.Analysis.Summation.cintegralTwentyFive_evc_1
import Submission.Commons.Analysis.Summation.cintegralTwentyFive_evc_2
import Submission.Commons.Analysis.Summation.cintegralTwentyFive_evc_3

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section
open scoped BigOperators Nat
open Filter Topology
open Polynomial

namespace Commons.Analysis.Summation
namespace CdtTwentyFiveCore

/-! ## The clearing factor and the decomposition coefficients -/

def Lc : ℤ := 635629413847630563680758639200

def cA : ℕ → ℤ := fun j => if j = 26 then (9537578431498586698989867878081138754326400 : ℤ) else if j = 28 then (-4226208154128862986880840083374761343697780000 : ℤ) else if j = 29 then (40396259614702078502495795238453339304614720000 : ℤ) else if j = 31 then (-1180816414683781790216430918770591515367991528000 : ℤ) else if j = 32 then (2436653971217968781870688006053674222439490744000 : ℤ) else if j = 34 then (142023563032882805300174105696965655357438349840000 : ℤ) else if j = 35 then (-824664650780510656328571878370631994458587383040000 : ℤ) else if j = 37 then (8462042571679125805596260127022894005185778704064000 : ℤ) else if j = 38 then (-9171443148368735382292823616398358931377514410240000 : ℤ) else if j = 40 then (-315962838606307478951876246334470916721994266829880000 : ℤ) else if j = 41 then (1152054981775961261521459058638016557260756851050752000 : ℤ) else if j = 43 then (-3437319220911307414787238251894938329504416739138480000 : ℤ) else if j = 44 then (-4785399702463597010542780393114029840479567012041680000 : ℤ) else if j = 46 then (137432523881072892350465105111556083147718009728096688000 : ℤ) else if j = 47 then (-279751193099343533608202470567567841043019217494609824000 : ℤ) else if j = 49 then (-417832353655838766424063244353745034419003909929647360000 : ℤ) else if j = 50 then (2819034857278679147932343039569827018328465449245734560000 : ℤ) else if j = 52 then (-12268476877000674242717458146356776653300831204661634306400 : ℤ) else if j = 53 then (7638723336302216327607595239395674469813507124835793280000 : ℤ) else if j = 55 then (103984808675267004151938618661875549471990257391431470680000 : ℤ) else if j = 56 then (-215257380817337929302981478712554746736647391380147305232000 : ℤ) else if j = 58 then (5894713240266816381687097136834175003769780362836917080000 : ℤ) else if j = 59 then (805319677722289088694553945250243784635122591529846516160000 : ℤ) else if j = 61 then (-3347969943892425821458402177654578061084748164219629893856000 : ℤ) else if j = 62 then (2414948355426235894718014800976470283240426420810980549696000 : ℤ) else if j = 64 then (14075995606743931308934755197462039532466109475246346165260000 : ℤ) else if j = 65 then (-26271725480915958545595477464147345169395622242320681605120000 : ℤ) else if j = 67 then (2300099257478712887738474618397001802541695230970854191744000 : ℤ) else if j = 68 then (59229500827125936910252307418310120185146070882769484538480000 : ℤ) else if j = 70 then (-180922196731538551470297130553252198407601840564257993057920000 : ℤ) else if j = 71 then (102272230347181094175561221804041056083554207436263544715552000 : ℤ) else if j = 73 then (521292437287977223365982767094162882738430794957259167975680000 : ℤ) else if j = 74 then (-798341231731963732236161736248218606953235993709995590872640000 : ℤ) else if j = 76 then (-109940868185126174406056496681950061691119557282716333878163200 : ℤ) else if j = 77 then (1394020185795746149361368794195494024268380768070837989950003200 : ℤ) else if j = 79 then (-2605921910638866658882800677250844418495117454865198325064000000 : ℤ) else if j = 80 then (822815330404081496541470340019756058695733900192458474740000000 : ℤ) else if j = 82 then (6060999205781117177648707371276505101228243701043646303515360000 : ℤ) else if j = 83 then (-7223299392075926390681117075952826984726743134876527219152000000 : ℤ) else if j = 85 then (-2831905522653347627508852584824000950094267765763783152560000000 : ℤ) else if j = 86 then (10788097299788791509895213344892312841609823188169995466107520000 : ℤ) else if j = 88 then (-11310099423629548533068717007582096744251108305763189811798000000 : ℤ) else if j = 89 then (0 : ℤ) else if j = 91 then (23332923817696095796391276925347809443517152544040615578950720000 : ℤ) else if j = 92 then (-21150639531911734174369355261733033424611062162462383529095020000 : ℤ) else if j = 94 then (-12865204746813608204745101090788679109468012963091793660040000000 : ℤ) else if j = 95 then (27827704839231074716106703081797854674766981182145155684777000000 : ℤ) else if j = 97 then (-15635517710981385836161465335497199761133066565204782414090240000 : ℤ) else if j = 98 then (-6257444550323664820547190182048730585742796502135499314990000000 : ℤ) else if j = 100 then (30632593381092676678435254395792321225746368636110842852932000000 : ℤ) else if j = 101 then (-21074355156557604653252630827821459536569331188463191506475123200 : ℤ) else if j = 103 then (-15947232219607309963176712412549583878622144345552360904021440000 : ℤ) else if j = 104 then (24222402317520480455563454681827546165589297637570139641821640000 : ℤ) else if j = 106 then (-7293415466812866740079952170485615842857815545455031569071904000 : ℤ) else if j = 107 then (-6305116937553465849915243273840207702764680290191853285208752000 : ℤ) else if j = 109 then (13884572497139501696195926557404232710250309332734845839368320000 : ℤ) else if j = 110 then (-7535010701158266147666438948246910151542135274840793826806480000 : ℤ) else if j = 112 then (-5798247161421243368951558712107316569959478555443011991289808000 : ℤ) else if j = 113 then (7028481775953024506041882174738648412999865592237651017285120000 : ℤ) else if j = 115 then (-1377756770027884126023730292602848941907640610392525206426240000 : ℤ) else if j = 116 then (-1390165511949720801754646529955817844418363989586833821366196000 : ℤ) else if j = 118 then (2122725614670240863002757533166761505451463061345183874360960000 : ℤ) else if j = 119 then (-1025455136975261572290984191702727573657390824770474636631160000 : ℤ) else if j = 121 then (-566347214815585612561056570136054371561329959334069459857536000 : ℤ) else if j = 122 then (626832991959731291078573599780550600208892814190600756908232000 : ℤ) else if j = 124 then (-128897222211060952776668256431720370466340813460867720020280000 : ℤ) else if j = 125 then (-52956650757978876083444553591432672422257162741893866213280000 : ℤ) else if j = 127 then (95641264070021972289339068062631036815124160391468989385372800 : ℤ) else if j = 128 then (-48858506140027029491923077307326996686788643034234688623900000 : ℤ) else if j = 130 then (-9379602610311204936080937212704614156487387577841472113360000 : ℤ) else if j = 131 then (12872402402011823950721120493057285267646075785719743714560000 : ℤ) else if j = 133 then (-3883060288754005510104247018386764536115305539760120436160000 : ℤ) else if j = 134 then (630188370555581385510809141886921096011966048554805779200000 : ℤ) else if j = 136 then (768356367034579246698664536390076933966074062837805794472000 : ℤ) else if j = 137 then (-477933581658252553381107284979095176847196823136265146880000 : ℤ) else if j = 139 then (41525203925599658439191190783694716903618742359704220480000 : ℤ) else if j = 140 then (13604256378726222390911062860100446333686280909679425600000 : ℤ) else if j = 142 then (-12282193432779832849770630679666660549934693047349692608000 : ℤ) else if j = 143 then (5212100102987946006842898464841584638846336969250697600000 : ℤ) else if j = 145 then (-209033603666267655469395781145765062094531234682908160000 : ℤ) else if j = 146 then (-85316925580124567297526329944409448709855392178503360000 : ℤ) else if j = 148 then (36894847685827922247748208951517972057473675711579640000 : ℤ) else if j = 149 then (-12373369558655197005501980899854752668758207269356800000 : ℤ) else if j = 151 then (638647655848249414346986540915164896433462456761846400 : ℤ) else if j = 152 then (-91268914071268532367316591786057334041830340749216000 : ℤ) else 0

def cD : ℕ → ℤ := fun j => if j = 26 then (-39915563617908591262359599422234590790801702 : ℤ) else if j = 27 then (-1032075512651085512199151883534682695353053576 : ℤ) else if j = 28 then (33417166804431587650048627244671975264392092325 : ℤ) else if j = 29 then (-177339836490256335614515525163646642652494916302 : ℤ) else if j = 30 then (-969546840128517307021037413322483870590688086176 : ℤ) else if j = 31 then (10786769886237807046982307992476122352875394782495 : ℤ) else if j = 32 then (-23866769037861319350538379407854585407342188661597 : ℤ) else if j = 33 then (38813188286548934972967734214438797391262138048224 : ℤ) else if j = 34 then (-614993221447946797159848468081128561413377306757605 : ℤ) else if j = 35 then (1471407628967357016195557873448147535733420062585603 : ℤ) else if j = 36 then (11741373792501110604899373919871540037737558116365444 : ℤ) else if j = 37 then (-59866740772698814387954182079819468122813555097436565 : ℤ) else if j = 38 then (73762012095881089404957525346785286109255890288888803 : ℤ) else if j = 39 then (-146142038638129895639256104421407991103215772788552756 : ℤ) else if j = 40 then (1226576357539203440030598051303060770604314649020765385 : ℤ) else if j = 41 then (-1396074602015489191114869616156203324621299577416709757 : ℤ) else if j = 42 then (-10117169812395966463886699629167261421800688427406047736 : ℤ) else if j = 43 then (27895348071174759322655277904143299021137224291667370085 : ℤ) else if j = 44 then (-24892994191248877586701967834774910020427114921132848607 : ℤ) else if j = 45 then (143196055272676786285526129449194575049858591232753856664 : ℤ) else if j = 46 then (-563421006004745479092125144607163025790503708630607303735 : ℤ) else if j = 47 then (376580105311584612020762619187946500210967914522913469213 : ℤ) else if j = 48 then (1174832072660242974170307668932525184154444616643601842814 : ℤ) else if j = 49 then (-724681013682978859223834315784674499680871140723918713335 : ℤ) else if j = 50 then (1660970439614857625011787545163608964948446933020303350913 : ℤ) else if j = 51 then (-26159238752782745930636666421003628509064560999069971461938 : ℤ) else if j = 52 then (58490207949959367810402380681066451003482076185261751953136 : ℤ) else if j = 53 then (-34503255606925166554161790238573342731549001595696091084687 : ℤ) else if j = 54 then (64348535478236509032237667262123067019112633125284167483262 : ℤ) else if j = 55 then (-270000544327469070407601911976789037994071186605549079505814 : ℤ) else if j = 56 then (23324544532098999080433205322942757061568249303478381908103 : ℤ) else if j = 57 then (997678039752509840955811153933816507090541159517591095855502 : ℤ) else if j = 58 then (-1083125119385580410986496014106150049588050892633230658220764 : ℤ) else if j = 59 then (1215049425611871997779994714915916234881532685373325133799903 : ℤ) else if j = 60 then (-6908562486245103077355901383967514455336097156444863224892773 : ℤ) else if j = 61 then (12113268092164545744086159847605476505984684510513094125066076 : ℤ) else if j = 62 then (-4239281995933741697136918873880441769802580381504302599481017 : ℤ) else if j = 63 then (4331979511909640988908081405360727580833405727810532684200077 : ℤ) else if j = 64 then (-23788777333929926321699194629702892524692092720621976641412199 : ℤ) else if j = 65 then (-12692895419651005552519854494875631271199992592077484084018617 : ℤ) else if j = 66 then (105296118454229363454525044180361934135933635507296318075929047 : ℤ) else if j = 67 then (-95987190379445864888469527984466172488450500640180654753135159 : ℤ) else if j = 68 then (99846967749512406326789977251558146729621808928535041432575533 : ℤ) else if j = 69 then (-399725797191910089539523614115670994118917539064284678126944753 : ℤ) else if j = 70 then (537675404450368460115303575029636601911330338189264094923823641 : ℤ) else if j = 71 then (-108467553461527004499663784055990670527681234352497608030712607 : ℤ) else if j = 72 then (144683993279263844500158929277505363393648747124456238903493482 : ℤ) else if j = 73 then (-636336890510085961735844993700797208049186928366089025852231559 : ℤ) else if j = 74 then (-631012358919449094535626504888596929827600200209227616340964807 : ℤ) else if j = 75 then (2552689922631586215661866856870135325685698561293810904781998082 : ℤ) else if j = 76 then (-1817930743102325863808933287879460407503525783358858097840648811 : ℤ) else if j = 77 then (2135428583681650188417654745207019000570781897541978159925669529 : ℤ) else if j = 78 then (-6698252871368342934203376681472741914256091769940363970018886918 : ℤ) else if j = 79 then (6783053976276612916105195837539907249043319727802550097163916189 : ℤ) else if j = 80 then (-959120884404460132080850954367577339605722085046576158171317971 : ℤ) else if j = 81 then (2663829675217434355325616056317196365643432373472575435351756282 : ℤ) else if j = 82 then (-5850119656016408245901806134376761583966907337265865546017900911 : ℤ) else if j = 83 then (-7048988440455655930744912461625899251663160939172746140770687971 : ℤ) else if j = 84 then (17843161582265615212643551170007650976232221049194511220252315657 : ℤ) else if j = 85 then (-9849894333751846468351806580498560639731552527502221758723550911 : ℤ) else if j = 86 then (14748370702309716203880824716885373185352395747161050817078005229 : ℤ) else if j = 87 then (-36198643808929805935024303121926259330126619053749120828097982693 : ℤ) else if j = 88 then (27489841917345397571015274865915417815265724631300160312729222839 : ℤ) else if j = 89 then (-4116433602712684261048599327043432596345165642945560114318394771 : ℤ) else if j = 90 then (15146194983803062352809625706509334014880817289839515048322063557 : ℤ) else if j = 91 then (-17944279117111545266361670809833141449269096896986982265486557361 : ℤ) else if j = 92 then (-23852475518910156775601640648741302895904738091303054431744350846 : ℤ) else if j = 93 then (40363923240591846678929846907829969180239175365557902011387238557 : ℤ) else if j = 94 then (-18019654608567338776064952621781027734008454707438586152598032361 : ℤ) else if j = 95 then (34783836331270629644641198719542683964445757381084433318903425404 : ℤ) else if j = 96 then (-65826281889148067524802096110626370160361119427632039847254730618 : ℤ) else if j = 97 then (37744606003593501588097248383898219097132511202820514593679190039 : ℤ) else if j = 98 then (-7174630112615680757983315933188371055802459553545165193366112096 : ℤ) else if j = 99 then (24486214251175026514287605845944829192210490746178992899547289382 : ℤ) else if j = 100 then (-17222188669715675313321830823413658656631851047865331543353992461 : ℤ) else if j = 101 then (-27230800836284025343882801956339722473776530388482935352693512944 : ℤ) else if j = 102 then (32082346228236253678769028547435454474810815201815816611476105158 : ℤ) else if j = 103 then (-12793373540177308697973894329229438249952797901036549262907956661 : ℤ) else if j = 104 then (27771985420044473902491348327437999374925295865603106744523192906 : ℤ) else if j = 105 then (-40479083810684618999416541943675634731524573280701661053060377242 : ℤ) else if j = 106 then (17561386692280595343754257554431516120611492741008074402540913919 : ℤ) else if j = 107 then (-3427663598407370352478065817473603141772582806456839204044499474 : ℤ) else if j = 108 then (10937249157904761159572844308035934210556861062706588399840154608 : ℤ) else if j = 109 then (-4369452242607120170126194620012222848884482746629264670044358481 : ℤ) else if j = 110 then (-10919551490879631496845523579295968437032852930392261053365649174 : ℤ) else if j = 111 then (9580414275093645911703751050362542897544052334716625982403913188 : ℤ) else if j = 112 then (-3674761077281686955105971685109314876360246813516272526661164271 : ℤ) else if j = 113 then (7015310075033397256799838677228357029769237770762637406157227626 : ℤ) else if j = 114 then (-8006896574340173016719502542447707897972040617644068633456621112 : ℤ) else if j = 115 then (2505400772646953972754675050066431541212423693428430837171202529 : ℤ) else if j = 116 then (-84175496173762238515648297848573176004874997883284356561084939 : ℤ) else if j = 117 then (1072229492520216165887603490137912011183538436501957517773382968 : ℤ) else if j = 118 then (-73905465773419770556747273272410675728681603031561182199074671 : ℤ) else if j = 119 then (-1456507297232114566430271920861885888738320726619717518808626089 : ℤ) else if j = 120 then (1036499142807068336084519169058093400357045302656249169334352318 : ℤ) else if j = 121 then (-344061771851587190897484838738496809167527479930150543544292351 : ℤ) else if j = 122 then (455476831368408022178258324276731261023453172377925055702012041 : ℤ) else if j = 123 then (-423133464500229566172343912508425700515402939752959633797535082 : ℤ) else if j = 124 then (70503109189118905874464481146829225119722494555417566192787874 : ℤ) else if j = 125 then (59800032467305517531903560304654138278384058777710059071807841 : ℤ) else if j = 126 then (-6855978080132889954060482290604111508087544238039472747185730 : ℤ) else if j = 127 then (18346878962073694082836647667423322979157760635764489497015628 : ℤ) else if j = 128 then (-49045438290746112659182656511769071344254424070393237618055934 : ℤ) else if j = 129 then (29254093537275631438750521845969564178484574379295860825419070 : ℤ) else if j = 130 then (-5556782009039998128541894312677347628503632367867073932935422 : ℤ) else if j = 131 then (3108969150752355148959615100351517558568189994358359432055826 : ℤ) else if j = 132 then (-3016779491027054256686982494632065184696286627453549874317520 : ℤ) else if j = 133 then (-510639751844690811154565811380292570975225904171155857679222 : ℤ) else if j = 134 then (1610443483109702850450763135039465572729768277947123945089026 : ℤ) else if j = 135 then (-638148007051996127351191636531121465966471882777886613513620 : ℤ) else if j = 136 then (160141419179347278342876442136839250721936056452975190565063 : ℤ) else if j = 137 then (-157370815188900388861980966997828109848093052149390403351454 : ℤ) else if j = 138 then (77423631125284652878238923820945116099323962601422202489780 : ℤ) else if j = 139 then (10655421955847173657759600759850549939000677425735355436463 : ℤ) else if j = 140 then (-19175541963896871323409875555349739924731932487190021441354 : ℤ) else if j = 141 then (5260820679951234279479514011408022910447351345786972258260 : ℤ) else if j = 142 then (-1329369099869429066426852176561267797934247138730262975977 : ℤ) else if j = 143 then (1045638737826109054239201810273152980947384140845963043246 : ℤ) else if j = 144 then (-300733441526901737566098529611045359109600766664041525440 : ℤ) else if j = 145 then (-89498741273105686496122444933051900376974086845007684777 : ℤ) else if j = 146 then (68059667182575036878257116008821469324692936476609999186 : ℤ) else if j = 147 then (-11636085466533626927304823081918211146849682222471600400 : ℤ) else if j = 148 then (-377556803161980986247483309912705083022946129038275202 : ℤ) else if j = 149 then (218891568161393324011347354221725180312726660810376386 : ℤ) else 0

def aIdx : Finset ℕ := {26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 73, 74, 76, 77, 79, 80, 82, 83, 85, 86, 88, 89, 91, 92, 94, 95, 97, 98, 100, 101, 103, 104, 106, 107, 109, 110, 112, 113, 115, 116, 118, 119, 121, 122, 124, 125, 127, 128, 130, 131, 133, 134, 136, 137, 139, 140, 142, 143, 145, 146, 148, 149, 151, 152}
def dIdx : Finset ℕ := {26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149}

/-! ## index bounds -/

lemma aIdx_bounds (j : ℕ) (hj : j ∈ aIdx) : 26 ≤ j ∧ j ≤ 152 := by
  simp only [aIdx, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

lemma dIdx_bounds (k : ℕ) (hk : k ∈ dIdx) : 26 ≤ k ∧ k ≤ 149 := by
  simp only [dIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  omega



def Sf (i : ℕ) : Finset ℕ := (Finset.range 26).image (fun j => 3 * j + i)

/-! ## polynomials -/

noncomputable def Dpol : ℤ[X] := ∏ τ ∈ Finset.range 127, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2
noncomputable def Qpol (i : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 127, (if τ ∈ Sf i then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Rpol (j : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 127, (if (26 + τ : ℕ) = j then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Tpol (k : ℕ) : ℤ[X] :=
  (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
    (∏ τ ∈ Finset.range 127, (if (26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3 then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)))
noncomputable def Ppol (i : ℕ) : ℤ[X] := ∏ j ∈ Finset.range 26, (C (3:ℤ) * X + C ((26 + 3 * j + i : ℕ) : ℤ))

noncomputable def P1 : ℤ[X] :=
  C ((123998613655334586790468240788273477463695598800085245713266618550534492015542986080256000000000000 : ℤ)) *
    ((∏ r ∈ Finset.range 50, (Polynomial.X + C (((r : ℤ) + 1)))) *
    (∑ i ∈ Finset.range 52, C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) * Qpol i))

noncomputable def P2 : ℤ[X] :=
  C ((30414093201713378043612608166064768844377641568960512000000000000 : ℤ)) *
    ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k))

/-! ## generic product lemmas -/

lemma prod_ite_one_eq {ι M : Type*} [CommMonoid M] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (f : ι → M) :
    (∏ i ∈ s, (if p i then (1 : M) else f i)) = ∏ i ∈ s.filter (fun i => ¬ p i), f i := by
  rw [Finset.prod_ite]
  simp

lemma Sf_subset (i : ℕ) (hi : i < 52) : Sf i ⊆ Finset.range 127 := by
  intro τ hτ
  simp only [Sf, Finset.mem_image, Finset.mem_range] at hτ ⊢
  obtain ⟨j, hj, rfl⟩ := hτ
  omega

lemma Sf_card (i : ℕ) : (Sf i).card = 26 := by
  rw [Sf, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have h : 3 * x + i = 3 * y + i := hxy
    omega

lemma prod_Sf_eq (i : ℕ) (F : ℕ → ℤ[X]) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 26, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma Ppol_sq_eq (i : ℕ) :
    (Ppol i) ^ 2 = ∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Ppol, prod_Sf_eq i (fun τ => (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  have h : (26 + (3 * j + i) : ℕ) = 26 + 3 * j + i := by omega
  rw [h]

lemma Qpol_eq (i : ℕ) (hi : i < 52) :
    Qpol i = ∏ τ ∈ (Finset.range 127) \ Sf i, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Qpol, prod_ite_one_eq, Finset.sdiff_eq_filter]

lemma prod_range_split (i : ℕ) (hi : i < 52) (F : ℕ → ℤ[X]) :
    (∏ τ ∈ Finset.range 127, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 127) \ Sf i, F τ) := by
  rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset (Sf_subset i hi)]

lemma Dpol_split (i : ℕ) (hi : i < 52) :
    Dpol = (∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2) *
      (∏ τ ∈ (Finset.range 127) \ Sf i, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2) := by
  unfold Dpol
  exact prod_range_split i hi _

lemma Dpol_eq_Ppol_sq_mul_Qpol (i : ℕ) (hi : i < 52) : Dpol = Ppol i ^ 2 * Qpol i := by
  rw [Dpol_split i hi, ← Ppol_sq_eq i, ← Qpol_eq i hi]

lemma Rpol_eq (j : ℕ) :
    Rpol j = ∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = j)),
      (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Rpol, prod_ite_one_eq]

lemma prod_filter_step (j : ℕ) :
    (∏ τ ∈ Finset.range 127, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 127).filter (fun τ => (26 + τ : ℕ) = j),
            (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = j)),
            (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 127) (fun τ => (26 + τ : ℕ) = j) _).symm

lemma filter_eq_singleton (j : ℕ) (h1 : 26 ≤ j) (h2 : j ≤ 152) :
    (Finset.range 127).filter (fun τ => (26 + τ : ℕ) = j) = {j - 26} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hj⟩; omega
  · rintro rfl; constructor <;> omega

lemma Dpol_eq_sq_mul_Rpol (j : ℕ) (h1 : 26 ≤ j) (h2 : j ≤ 152) :
    Dpol = (C (3:ℤ) * X + C (j : ℤ)) ^ 2 * Rpol j := by
  rw [Dpol, prod_filter_step j, Rpol_eq j, filter_eq_singleton j h1 h2, Finset.prod_singleton]
  have e : ((26 + (j - 26) : ℕ) : ℤ) = (j : ℤ) := by omega
  rw [e]

lemma prod_filter_step2 (k : ℕ) :
    (∏ τ ∈ Finset.range 127, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 127).filter (fun τ => ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 127)
    (fun τ => ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)) _).symm

lemma filter_eq_pair (k : ℕ) (h1 : 26 ≤ k) (h2 : k ≤ 149) :
    (Finset.range 127).filter (fun τ => ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)) = {k - 26, k - 23} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hk | hk⟩
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> constructor <;> omega

lemma Dpol_eq_lin_mul_Tpol (k : ℕ) (h1 : 26 ≤ k) (h2 : k ≤ 149) :
    Dpol = (C (3:ℤ) * X + C (k : ℤ)) * (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) * Tpol k := by
  have hne : k - 26 ∉ ({k - 23} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [Tpol, prod_ite_one_eq, Dpol, prod_filter_step2 k, filter_eq_pair k h1 h2,
    Finset.prod_insert hne, Finset.prod_singleton]
  have e1 : ((26 + (k - 26) : ℕ) : ℤ) = (k : ℤ) := by omega
  have e2 : ((26 + (k - 23) : ℕ) : ℤ) = ((k + 3 : ℕ) : ℤ) := by omega
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
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 2 * s.card := by
  have h1 : (∏ τ ∈ s, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤
      ∑ τ ∈ s, ((C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2).natDegree :=
    Polynomial.natDegree_prod_le s (fun τ => (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)
  have h2 : (∑ τ ∈ s, ((C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2).natDegree) ≤ ∑ _τ ∈ s, 2 :=
    Finset.sum_le_sum (fun τ _ => natDegree_sq_lin_le _)
  have h3 : (∑ _τ ∈ s, (2 : ℕ)) = 2 * s.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  linarith

lemma natDegree_prod_sq_le_254 (s : Finset ℕ) (h : s.card ≤ 127) :
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 254 :=
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
    ((Finset.range 127).filter p).card ≤ 127 := by
  have h := Finset.card_le_card (Finset.filter_subset p (Finset.range 127))
  rwa [Finset.card_range] at h

lemma card_sdiff_le (s : Finset ℕ) : ((Finset.range 127) \ s).card ≤ 127 := by
  have h := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range 127) (t := s))
  rwa [Finset.card_range] at h

lemma natDegree_Qpol_le (i : ℕ) (hi : i < 52) : (Qpol i).natDegree ≤ 254 := by
  rw [Qpol_eq i hi]
  exact natDegree_prod_sq_le_254 _ (card_sdiff_le _)

lemma natDegree_Rpol_le (j : ℕ) : (Rpol j).natDegree ≤ 254 := by
  rw [Rpol_eq j]
  exact natDegree_prod_sq_le_254 _ (filter_card_le _)

lemma Tpol_eq' (k : ℕ) :
    Tpol k = (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)) := by
  rw [Tpol, prod_ite_one_eq]

lemma natDegree_Tpol_le (k : ℕ) : (Tpol k).natDegree ≤ 256 := by
  have h1 : (Tpol k).natDegree ≤ (C (3:ℤ) * X + C (k : ℤ)).natDegree +
      ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
        (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
          (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)).natDegree := by
    rw [Tpol_eq' k]
    exact Polynomial.natDegree_mul_le
  have h2 : ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2)).natDegree ≤ 1 + 254 := by
    have hm := Polynomial.natDegree_mul_le (p := (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)))
      (q := (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2))
    have ha : (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
    have hb : (∏ τ ∈ (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((26 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 254 :=
      natDegree_prod_sq_le_254 _ (filter_card_le _)
    linarith
  have h3 : (C (3:ℤ) * X + C (k : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
  linarith

lemma natDegree_P1_le : P1.natDegree ≤ 304 := by
  have h1 : P1.natDegree ≤ (C ((717897987691852588770249 : ℤ) * (13142471588392206890177483046912000000 : ℤ) ^ 2)).natDegree +
      ((∏ r ∈ Finset.range 50, (Polynomial.X + C (((r : ℤ) + 1)))) *
        (∑ i ∈ Finset.range 52,
          C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) * Qpol i)).natDegree := by
    rw [P1]
    exact Polynomial.natDegree_mul_le
  have h2 : ((∏ r ∈ Finset.range 50, (Polynomial.X + C (((r : ℤ) + 1)))) *
      (∑ i ∈ Finset.range 52,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) * Qpol i)).natDegree ≤ 50 + 254 := by
    refine le_trans (Polynomial.natDegree_mul_le) (add_le_add ?_ ?_)
    · have hp : (∏ r ∈ Finset.range 50, (Polynomial.X + C (((r : ℤ) + 1)))).natDegree ≤
          ∑ r ∈ Finset.range 50, (Polynomial.X + C (((r : ℤ) + 1))).natDegree :=
        Polynomial.natDegree_prod_le _ _
      have hq : (∑ r ∈ Finset.range 50, (Polynomial.X + C (((r : ℤ) + 1))).natDegree) = 50 := by
        rw [Finset.sum_congr rfl (fun r _ => Polynomial.natDegree_X_add_C _)]
        simp
      omega
    · exact natDegree_sum_le' _ _ 254 (fun i hi => by
        rw [Finset.mem_range] at hi
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Qpol_le i hi))
  have h3 : (C ((717897987691852588770249 : ℤ) * (13142471588392206890177483046912000000 : ℤ) ^ 2)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma natDegree_P2_le : P2.natDegree ≤ 256 := by
  have h1 : P2.natDegree ≤ (C ((30414093201713378043612608166064768844377641568960512000000000000 : ℤ))).natDegree +
      ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree := by
    rw [P2]
    exact Polynomial.natDegree_mul_le
  have hR : (∑ j ∈ aIdx, C (cA j) * Rpol j).natDegree ≤ 254 :=
    natDegree_sum_le' _ _ 254 (fun j _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Rpol_le j))
  have hT : (∑ k ∈ dIdx, C (cD k) * Tpol k).natDegree ≤ 256 :=
    natDegree_sum_le' _ _ 256 (fun k _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Tpol_le k))
  have h2 : ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree ≤
      256 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (le_trans hR (by norm_num)) hT)
  have h3 : (C ((30414093201713378043612608166064768844377641568960512000000000000 : ℤ))).natDegree = 0 := Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma degree_bound : max P1.natDegree P2.natDegree < 305 := by
  rw [max_lt_iff]
  constructor
  · exact lt_of_le_of_lt natDegree_P1_le (by norm_num)
  · exact lt_of_le_of_lt natDegree_P2_le (by norm_num)

/-! ## evaluation of the polynomials (integer form) -/

def EvP1 (c : ℤ) : ℤ := (717897987691852588770249 * 13142471588392206890177483046912000000 ^ 2) *
  ((∏ r ∈ Finset.range 50, (c + ((r : ℤ) + 1))) *
   (∑ i ∈ Finset.range 52, (Lc * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) *
     (∏ τ ∈ Finset.range 127, (if τ ∈ Sf i then 1 else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2))))

def EvP2 (c : ℤ) : ℤ := 30414093201713378043612608166064768844377641568960512000000000000 *
  ((∑ j ∈ aIdx, cA j * (∏ τ ∈ Finset.range 127, (if (26 + τ : ℕ) = j then 1 else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2)))
   + (∑ k ∈ dIdx, cD k * ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) * (∏ τ ∈ Finset.range 127, (if (26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3 then 1 else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2)))))

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

def Pall (c : ℤ) : ℤ := ∏ τ ∈ Finset.range 127, (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2

lemma prod_Sf_eqZ (i : ℕ) (F : ℕ → ℤ) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 26, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma prod_range_splitZ (i : ℕ) (hi : i < 52) (F : ℕ → ℤ) :
    (∏ τ ∈ Finset.range 127, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 127) \ Sf i, F τ) := by
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

lemma filter_not_eq_erase (j : ℕ) (h1 : 26 ≤ j) (h2 : j ≤ 152) :
    (Finset.range 127).filter (fun τ => ¬ ((26 + τ : ℕ) = j)) =
      (Finset.range 127).erase (j - 26) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨hlt, hne⟩
    exact ⟨fun h => hne (by omega), hlt⟩
  · rintro ⟨hne, hlt⟩
    exact ⟨hlt, fun h => hne (by omega)⟩

lemma filter_not_pair_eq_erase (k : ℕ) (h1 : 26 ≤ k) (h2 : k ≤ 149) :
    (Finset.range 127).filter
        (fun τ => ¬ ((26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3)) =
      ((Finset.range 127).erase (k - 26)).erase (k - 23) := by
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

lemma prod_ite_eq_div {c : ℤ} (hc : 0 ≤ c) (j : ℕ) (h1 : 26 ≤ j) (h2 : j ≤ 152) :
    (∏ τ ∈ Finset.range 127,
        (if (26 + τ : ℕ) = j then (1 : ℤ)
          else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (3 * c + ((26 + (j - 26) : ℕ) : ℤ)) ^ 2 := by
  have hmem : j - 26 ∈ Finset.range 127 := by
    simp only [Finset.mem_range]; omega
  have hne : (3 * c + ((26 + (j - 26) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hj : (26 + (j - 26) : ℕ) = j := by omega
    rw [hj]; exact sqf_ne_zero hc (by omega : 0 < j)
  rw [prod_ite_one_eq, filter_not_eq_erase j h1 h2, Pall]
  exact prod_erase_eq_div _ _ hmem _ hne

lemma prod_ite_pair_eq_div {c : ℤ} (hc : 0 ≤ c) (k : ℕ) (h1 : 26 ≤ k)
    (h2 : k ≤ 149) :
    (∏ τ ∈ Finset.range 127,
        (if (26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3 then (1 : ℤ)
          else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / ((3 * c + ((26 + (k - 26) : ℕ) : ℤ)) ^ 2 *
          (3 * c + ((26 + (k - 23) : ℕ) : ℤ)) ^ 2) := by
  have hmem1 : k - 26 ∈ Finset.range 127 := by
    simp only [Finset.mem_range]; omega
  have hmem2 : k - 23 ∈ (Finset.range 127).erase (k - 26) := by
    simp only [Finset.mem_erase, Finset.mem_range]
    constructor
    · omega
    · omega
  have hne1 : (3 * c + ((26 + (k - 26) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (26 + (k - 26) : ℕ) = k := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k)
  have hne2 : (3 * c + ((26 + (k - 23) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (26 + (k - 23) : ℕ) = k + 3 := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k + 3)
  rw [prod_ite_one_eq, filter_not_pair_eq_erase k h1 h2, Pall]
  exact prod_erase_pair_eq_div _ _ _ hmem1 hmem2 _ hne1 hne2

lemma prod_ite_Sf_eq_div {c : ℤ} (hc : 0 ≤ c) (i : ℕ) (hi : i < 52) :
    (∏ τ ∈ Finset.range 127,
        (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (∏ j ∈ Finset.range 26,
          (3 * c + ((26 + (3 * j + i) : ℕ) : ℤ)) ^ 2) := by
  have hSf : (∏ τ ∈ Sf i, (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ j ∈ Finset.range 26, (3 * c + ((26 + (3 * j + i) : ℕ) : ℤ)) ^ 2) :=
    prod_Sf_eqZ i _
  have hne : (∏ j ∈ Finset.range 26,
      (3 * c + ((26 + (3 * j + i) : ℕ) : ℤ)) ^ 2) ≠ 0 := by
    rw [← hSf]
    exact Finset.prod_ne_zero_iff.mpr (fun τ _ => sqf_ne_zero hc (by omega : 0 < 26 + τ))
  have hsplit : Pall c =
      (∏ j ∈ Finset.range 26, (3 * c + ((26 + (3 * j + i) : ℕ) : ℤ)) ^ 2) *
        (∏ τ ∈ (Finset.range 127) \ Sf i,
          (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2) := by
    rw [Pall, prod_range_splitZ i hi, hSf]
  rw [prod_ite_one_eq, ← Finset.sdiff_eq_filter, hsplit,
    Int.mul_ediv_cancel_left _ hne]

def EvP1cheap (c : ℤ) : ℤ :=
  (717897987691852588770249 * 13142471588392206890177483046912000000 ^ 2) *
    ((∏ r ∈ Finset.range 50, (c + ((r : ℤ) + 1))) *
     (∑ i ∈ Finset.range 52, (Lc * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) *
       (Pall c / (∏ j ∈ Finset.range 26,
         (3 * c + ((26 + (3 * j + i) : ℕ) : ℤ)) ^ 2))))

def EvP2cheap (c : ℤ) : ℤ :=
  (30414093201713378043612608166064768844377641568960512000000000000) *
    ((∑ j ∈ aIdx, cA j * (Pall c / (3 * c + ((26 + (j - 26) : ℕ) : ℤ)) ^ 2))
     + (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((26 + (k - 26) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((26 + (k - 23) : ℕ) : ℤ)) ^ 2)))))

lemma EvP1_sum_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ i ∈ Finset.range 52, (Lc * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) *
        (∏ τ ∈ Finset.range 127,
          (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ i ∈ Finset.range 52, (Lc * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) *
        (Pall c / (∏ j ∈ Finset.range 26,
          (3 * c + ((26 + (3 * j + i) : ℕ) : ℤ)) ^ 2))) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [prod_ite_Sf_eq_div hc i hi]

lemma EvP2_sum1_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ j ∈ aIdx, cA j *
        (∏ τ ∈ Finset.range 127,
          (if (26 + τ : ℕ) = j then (1 : ℤ)
            else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ j ∈ aIdx, cA j *
        (Pall c / (3 * c + ((26 + (j - 26) : ℕ) : ℤ)) ^ 2)) := by
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨h1, h2⟩ := aIdx_bounds j hj
  rw [prod_ite_eq_div hc j h1 h2]

lemma EvP2_sum2_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ k ∈ dIdx, cD k *
        ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
          (∏ τ ∈ Finset.range 127,
            (if (26 + τ : ℕ) = k ∨ (26 + τ : ℕ) = k + 3 then (1 : ℤ)
              else (3 * c + ((26 + τ : ℕ) : ℤ)) ^ 2))))
      = (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((26 + (k - 26) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((26 + (k - 23) : ℕ) : ℤ)) ^ 2)))) := by
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨h1, h2⟩ := dIdx_bounds k hk
  rw [prod_ite_pair_eq_div hc k h1 h2]

lemma EvP1_eq_cheap {c : ℤ} (hc : 0 ≤ c) : EvP1 c = EvP1cheap c := by
  rw [EvP1, EvP1cheap, EvP1_sum_eq hc]

lemma EvP2_eq_cheap {c : ℤ} (hc : 0 ≤ c) : EvP2 c = EvP2cheap c := by
  rw [EvP2, EvP2cheap, EvP2_sum1_eq hc, EvP2_sum2_eq hc]
noncomputable def pts : Finset ℤ := (Finset.range 305).image (fun k : ℕ => (k : ℤ))

lemma pts_card : pts.card = 305 := by
  rw [pts, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Int.ofNat.inj h

theorem poly_eq : P1 = P2 := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' P1 P2 pts ?_ ?_
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_range] at hk
    have h0 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    rw [eval_P1_EvP1 (k : ℤ), eval_P2_EvP2 (k : ℤ),
      EvP1_eq_cheap (c := (k : ℤ)) h0, EvP2_eq_cheap (c := (k : ℤ)) h0]
    by_cases h1 : k ≤ 75
    · exact cintegralTwentyFive_evc_0 (k : ℤ)
        (by rw [Finset.mem_Icc]; exact ⟨h0, by exact_mod_cast h1⟩)
    · have h1' : 75 < k := by omega
      by_cases h2 : k ≤ 151
      · exact cintegralTwentyFive_evc_1 (k : ℤ)
          (by rw [Finset.mem_Icc]
              exact ⟨by exact_mod_cast (by omega : 76 ≤ k), by exact_mod_cast h2⟩)
      · have h2' : 151 < k := by omega
        by_cases h3 : k ≤ 227
        · exact cintegralTwentyFive_evc_2 (k : ℤ)
            (by rw [Finset.mem_Icc]
                exact ⟨by exact_mod_cast (by omega : 152 ≤ k), by exact_mod_cast h3⟩)
        · have h3' : 227 < k := by omega
          exact cintegralTwentyFive_evc_3 (k : ℤ)
            (by rw [Finset.mem_Icc]
                exact ⟨by exact_mod_cast (by omega : 228 ≤ k),
                       by exact_mod_cast (by omega : k ≤ 304)⟩)
  · rw [pts_card]
    exact degree_bound

def Df (m : ℕ) : ℤ := (Dpol).eval (m : ℤ)
def Pf (i : ℕ) (m : ℕ) : ℤ := (Ppol i).eval (m : ℤ)
def Qf (i : ℕ) (m : ℕ) : ℤ := (Qpol i).eval (m : ℤ)
def Rf (j : ℕ) (m : ℕ) : ℤ := (Rpol j).eval (m : ℤ)
def Tf (k : ℕ) (m : ℕ) : ℤ := (Tpol k).eval (m : ℤ)

lemma Pf_pos (i m : ℕ) (hi : i < 52) : 0 < Pf i m := by
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

lemma Df_eq_Pf_sq_mul_Qf (i m : ℕ) (hi : i < 52) : Df m = (Pf i m) ^ 2 * Qf i m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_Ppol_sq_mul_Qpol i hi)
  simpa [Df, Pf, Qf, Polynomial.eval_mul, Polynomial.eval_pow] using h

lemma Df_eq_sq_mul_Rf (j m : ℕ) (h1 : 26 ≤ j) (h2 : j ≤ 152) :
    Df m = (3 * (m : ℤ) + (j : ℤ)) ^ 2 * Rf j m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_sq_mul_Rpol j h1 h2)
  simpa [Df, Rf, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

lemma Df_eq_lin_mul_Tf (k m : ℕ) (h1 : 26 ≤ k) (h2 : k ≤ 149) :
    Df m = (3 * (m : ℤ) + (k : ℤ)) * (3 * (m : ℤ) + ((k + 3 : ℕ) : ℤ)) * Tf k m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_lin_mul_Tpol k h1 h2)
  simpa [Df, Tf, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h


/-! ## real-valued definitions -/

noncomputable def cTwentyFivePf (i : ℕ) (m : ℕ) : ℝ := ∏ j ∈ Finset.range 26, xm m (26 + 3 * j + i)

noncomputable def Vm25 (m : ℕ) : ℝ := (717897987691852588770249 : ℝ) * (Nat.choose (m + 50) 50 : ℝ) *
  (∑ i ∈ Finset.range 52, ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
    (13142471588392206890177483046912000000 / cTwentyFivePf i m) ^ 2)

noncomputable def aj (j : ℕ) : ℝ := (cA j : ℝ) / (Lc : ℝ)
noncomputable def dj (k : ℕ) : ℝ := (cD k : ℝ) / (3 * (Lc : ℝ))

noncomputable def W125 (m : ℕ) : ℝ := ∑ j ∈ aIdx, aj j / (xm m j) ^ 2
noncomputable def W225 (m : ℕ) : ℝ := ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))
noncomputable def Vd25 (m : ℕ) : ℝ := W125 m + W225 m

lemma cTwentyFivePf_eq (i m : ℕ) : cTwentyFivePf i m = ((Pf i m : ℤ) : ℝ) := by
  have h : ((Pf i m : ℤ) : ℝ) = ∏ j ∈ Finset.range 26,
      ((3 : ℝ) * (m : ℝ) + ((26 + 3 * j + i : ℕ) : ℝ)) := by
    rw [Pf, Ppol, Polynomial.eval_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    ring
  rw [h, cTwentyFivePf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [xm_eq]

lemma eval_prodP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∏ r ∈ Finset.range 50, (Polynomial.X + C ((r : ℤ) + 1))) =
      ∏ r ∈ Finset.range 50, ((m : ℤ) + (r + 1)) := by
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

lemma eval_sumP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∑ i ∈ Finset.range 52,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ)) * Qpol i) =
      ∑ i ∈ Finset.range 52, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ) * (Qf i m) := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.eval_mul, Polynomial.eval_C, Qf]

lemma eval_P1_int (m : ℕ) :
    P1.eval (m : ℤ) = (717897987691852588770249 * 13142471588392206890177483046912000000 ^ 2) *
      (∏ r ∈ Finset.range 50, ((m : ℤ) + (r + 1))) *
      (∑ i ∈ Finset.range 52, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 51 i : ℤ) * (Qf i m)) := by
  rw [P1, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_prodP m, eval_sumP m]
  ring

lemma eval_P1 (m : ℕ) :
    ((P1.eval (m : ℤ) : ℤ) : ℝ) = (717897987691852588770249 : ℝ) * (13142471588392206890177483046912000000 : ℝ) ^ 2 *
      (∏ r ∈ Finset.range 50, ((m : ℝ) + (r + 1))) *
      (∑ i ∈ Finset.range 52, (Lc : ℝ) * (-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ) * ((Qf i m : ℤ) : ℝ)) := by
  rw [eval_P1_int m]
  push_cast
  ring

lemma eval_P2_int (m : ℕ) :
    P2.eval (m : ℤ) = 30414093201713378043612608166064768844377641568960512000000000000 *
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
    ((P2.eval (m : ℤ) : ℤ) : ℝ) = (30414093201713378043612608166064768844377641568960512000000000000 : ℝ) *
      ((∑ j ∈ aIdx, (cA j : ℝ) * ((Rf j m : ℤ) : ℝ)) +
        (∑ k ∈ dIdx, (cD k : ℝ) * ((Tf k m : ℤ) : ℝ))) := by
  rw [eval_P2_int m]
  push_cast
  ring


/-! ## the factorial identity -/

lemma choose_fact_nat (m : ℕ) :
    (m + 50).choose 50 * (50 !) = ∏ r ∈ Finset.range 50, (m + r + 1) := by
  have h2 : (m + 1).ascFactorial 50 = 50 ! * (m + 50).choose 50 := by
    simpa using Nat.ascFactorial_eq_factorial_mul_choose m 50
  have h1 : (m + 1).ascFactorial 50 = ∏ i ∈ Finset.range 50, (m + 1 + i) :=
    Nat.ascFactorial_eq_prod_range (m + 1) 50
  rw [h2, Nat.mul_comm] at h1
  rw [h1]
  apply Finset.prod_congr rfl
  intro r hr
  omega

lemma choose_fact (m : ℕ) :
    (Nat.choose (m + 50) 50 : ℝ) * 30414093201713378043612608166064768844377641568960512000000000000 = ∏ r ∈ Finset.range 50, ((m : ℝ) + (r + 1)) := by
  have h : ((m + 50).choose 50 : ℝ) * ((50 ! : ℕ) : ℝ) =
      ((∏ r ∈ Finset.range 50, (m + r + 1) : ℕ) : ℝ) := by
    exact_mod_cast choose_fact_nat m
  have h24 : ((50 ! : ℕ) : ℝ) = 30414093201713378043612608166064768844377641568960512000000000000 := by norm_num
  rw [h24] at h
  rw [h]
  push_cast
  apply Finset.prod_congr rfl
  intro r hr
  ring


/-! ## the two clearing identities -/

lemma clear_left (m : ℕ) :
    Vm25 m * ((Df m : ℤ) : ℝ) * 30414093201713378043612608166064768844377641568960512000000000000 * (Lc : ℝ) =
      ((P1.eval (m : ℤ) : ℤ) : ℝ) := by
  have hgoal : Vm25 m * ((Df m : ℤ) : ℝ) * 30414093201713378043612608166064768844377641568960512000000000000 * (Lc : ℝ) =
      (717897987691852588770249 : ℝ) * ((Nat.choose (m + 50) 50 : ℝ) * 30414093201713378043612608166064768844377641568960512000000000000) *
        ((∑ i ∈ Finset.range 52, ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
            (13142471588392206890177483046912000000 / cTwentyFivePf i m) ^ 2) * ((Df m : ℤ) : ℝ)) * (Lc : ℝ) := by
    rw [Vm25]
    ring
  have hsum : (∑ i ∈ Finset.range 52, ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
        (13142471588392206890177483046912000000 / cTwentyFivePf i m) ^ 2) * ((Df m : ℤ) : ℝ) =
      (13142471588392206890177483046912000000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 52,
        ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cTwentyFivePf_eq i m]
    have hD : ((Df m : ℤ) : ℝ) = ((((Pf i m : ℤ)) : ℝ)) ^ 2 * ((Qf i m : ℤ) : ℝ) := by
      rw [Df_eq_Pf_sq_mul_Qf i m hi]
      simp only [Int.cast_mul, Int.cast_pow]
    rw [hD]
    have hne : (((Pf i m : ℤ)) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Pf_pos i m hi))
    field_simp
    try ring
  have hLc2 : ((13142471588392206890177483046912000000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 52,
        ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ) =
      (13142471588392206890177483046912000000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 52,
        (Lc : ℝ) * ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [show ((13142471588392206890177483046912000000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 52,
          ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
        = (13142471588392206890177483046912000000 : ℝ) ^ 2 * ((Lc : ℝ) * (∑ i ∈ Finset.range 52,
          ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) by ring]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hgoal, choose_fact m, hsum, eval_P1 m]
  rw [show (717897987691852588770249 : ℝ) * (∏ r ∈ Finset.range 50, ((m : ℝ) + (r + 1))) *
        ((13142471588392206890177483046912000000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 52,
          ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
      = (717897987691852588770249 : ℝ) * (∏ r ∈ Finset.range 50, ((m : ℝ) + (r + 1))) *
        (((13142471588392206890177483046912000000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 52,
          ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)) by ring]
  rw [hLc2]
  ring

lemma clear_right (m : ℕ) :
    Vd25 m * ((Df m : ℤ) : ℝ) * 30414093201713378043612608166064768844377641568960512000000000000 * (Lc : ℝ) =
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
  rw [eval_P2 m, Vd25]
  rw [show (W125 m + W225 m) * ((Df m : ℤ) : ℝ) * 30414093201713378043612608166064768844377641568960512000000000000 * (Lc : ℝ) =
      ((∑ j ∈ aIdx, aj j / (xm m j) ^ 2) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) +
        (∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) * ((Df m : ℤ) : ℝ) * (Lc : ℝ)) *
        30414093201713378043612608166064768844377641568960512000000000000 by
    rw [W125, W225]
    ring]
  rw [hW1, hW2]
  ring

theorem vm25_decomp (m : ℕ) : Vm25 m = Vd25 m := by
  have h1 := clear_left m
  have h2 := clear_right m
  have hP : ((P1.eval (m : ℤ) : ℤ) : ℝ) = ((P2.eval (m : ℤ) : ℤ) : ℝ) := by rw [poly_eq]
  have hDf : ((Df m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Df_pos m))
  have hFT : (30414093201713378043612608166064768844377641568960512000000000000 : ℝ) ≠ 0 := by norm_num
  have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
  have h := h1.trans (hP.trans h2.symm)
  have h' : (Vm25 m * ((Df m : ℤ) : ℝ)) * 30414093201713378043612608166064768844377641568960512000000000000 =
      (Vd25 m * ((Df m : ℤ) : ℝ)) * 30414093201713378043612608166064768844377641568960512000000000000 := mul_right_cancel₀ hLc h
  have h'' : Vm25 m * ((Df m : ℤ) : ℝ) = Vd25 m * ((Df m : ℤ) : ℝ) := mul_right_cancel₀ hFT h'
  exact mul_right_cancel₀ hDf h''

lemma denom_statement25 (m : ℕ) (i : ℕ) :
    (((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ) * ((3 * m + 44 + i : ℕ) : ℝ) * ((3 * m + 47 + i : ℕ) : ℝ) * ((3 * m + 50 + i : ℕ) : ℝ) * ((3 * m + 53 + i : ℕ) : ℝ) * ((3 * m + 56 + i : ℕ) : ℝ) * ((3 * m + 59 + i : ℕ) : ℝ) * ((3 * m + 62 + i : ℕ) : ℝ) * ((3 * m + 65 + i : ℕ) : ℝ) * ((3 * m + 68 + i : ℕ) : ℝ) * ((3 * m + 71 + i : ℕ) : ℝ) * ((3 * m + 74 + i : ℕ) : ℝ) * ((3 * m + 77 + i : ℕ) : ℝ) * ((3 * m + 80 + i : ℕ) : ℝ) * ((3 * m + 83 + i : ℕ) : ℝ) * ((3 * m + 86 + i : ℕ) : ℝ) * ((3 * m + 89 + i : ℕ) : ℝ) * ((3 * m + 92 + i : ℕ) : ℝ) * ((3 * m + 95 + i : ℕ) : ℝ) * ((3 * m + 98 + i : ℕ) : ℝ) * ((3 * m + 101 + i : ℕ) : ℝ))
      = cTwentyFivePf i m := by
  rw [cTwentyFivePf]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  simp only [xm_eq]
  push_cast
  ring

lemma inner_sum_statement25 (m : ℕ) :
    (∑ i ∈ Finset.range 52,
      ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
        (13142471588392206890177483046912000000 / (((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ) * ((3 * m + 44 + i : ℕ) : ℝ) * ((3 * m + 47 + i : ℕ) : ℝ) * ((3 * m + 50 + i : ℕ) : ℝ) * ((3 * m + 53 + i : ℕ) : ℝ) * ((3 * m + 56 + i : ℕ) : ℝ) * ((3 * m + 59 + i : ℕ) : ℝ) * ((3 * m + 62 + i : ℕ) : ℝ) * ((3 * m + 65 + i : ℕ) : ℝ) * ((3 * m + 68 + i : ℕ) : ℝ) * ((3 * m + 71 + i : ℕ) : ℝ) * ((3 * m + 74 + i : ℕ) : ℝ) * ((3 * m + 77 + i : ℕ) : ℝ) * ((3 * m + 80 + i : ℕ) : ℝ) * ((3 * m + 83 + i : ℕ) : ℝ) * ((3 * m + 86 + i : ℕ) : ℝ) * ((3 * m + 89 + i : ℕ) : ℝ) * ((3 * m + 92 + i : ℕ) : ℝ) * ((3 * m + 95 + i : ℕ) : ℝ) * ((3 * m + 98 + i : ℕ) : ℝ) * ((3 * m + 101 + i : ℕ) : ℝ))) ^ 2)
    = (∑ i ∈ Finset.range 52,
      ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
        (13142471588392206890177483046912000000 / cTwentyFivePf i m) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [denom_statement25 m i]

lemma vm25_eq_statement (m : ℕ) :
    (717897987691852588770249 : ℝ) * (Nat.choose (m + 50) 50 : ℝ) *
      (∑ i ∈ Finset.range 52,
        ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
          (13142471588392206890177483046912000000 / (((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ) * ((3 * m + 44 + i : ℕ) : ℝ) * ((3 * m + 47 + i : ℕ) : ℝ) * ((3 * m + 50 + i : ℕ) : ℝ) * ((3 * m + 53 + i : ℕ) : ℝ) * ((3 * m + 56 + i : ℕ) : ℝ) * ((3 * m + 59 + i : ℕ) : ℝ) * ((3 * m + 62 + i : ℕ) : ℝ) * ((3 * m + 65 + i : ℕ) : ℝ) * ((3 * m + 68 + i : ℕ) : ℝ) * ((3 * m + 71 + i : ℕ) : ℝ) * ((3 * m + 74 + i : ℕ) : ℝ) * ((3 * m + 77 + i : ℕ) : ℝ) * ((3 * m + 80 + i : ℕ) : ℝ) * ((3 * m + 83 + i : ℕ) : ℝ) * ((3 * m + 86 + i : ℕ) : ℝ) * ((3 * m + 89 + i : ℕ) : ℝ) * ((3 * m + 92 + i : ℕ) : ℝ) * ((3 * m + 95 + i : ℕ) : ℝ) * ((3 * m + 98 + i : ℕ) : ℝ) * ((3 * m + 101 + i : ℕ) : ℝ))) ^ 2) =
      Vm25 m := by
  rw [Vm25, inner_sum_statement25 m]

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
@[simp] lemma asum49 : Asum 49 = 2490994536883545715261963398023246596456020842425971688831304663149955196563207254991693 / 2225179528961438806186033432843632337863881646487724566841120736235661232526529815040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum50 : Asum 50 = 2491096124699878870795481752361853409473636980192885847184429257778161718715897472751693 / 2225179528961438806186033432843632337863881646487724566841120736235661232526529815040000 := by
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
@[simp] lemma bsum49 : Bsum 49 = 204945672635576940095965558380263181991543318179932863531949616604096966757212585177342662841 / 606041909968983011965499480530220623775734762419394033652145703698943045903352807743744000000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum50 : Bsum 50 = 4550604920092412630082496861080753124018028941675108897306465583931255702022779956329928201733041 / 13454736443221391848646053967251428068445087460472966941111286767820234562100335684718860544000000 := by
  norm_num [Bsum, f2, xm]

def cAval (j : ℕ) : ℝ := if j % 3 = 1 then (A - Asum (j / 3)) else (B - Bsum (j / 3))
def cDval (k : ℕ) : ℝ := 1 / xm 0 k

noncomputable def V1val25 : ℝ := ∑ j ∈ aIdx, aj j * cAval j
noncomputable def V2val25 : ℝ := ∑ k ∈ dIdx, dj k * cDval k
noncomputable def Vval25 : ℝ := V1val25 + V2val25

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

lemma hasSum_W125 : HasSum W125 V1val25 := by
  change HasSum (fun m => ∑ j ∈ aIdx, aj j / (xm m j) ^ 2) V1val25
  rw [V1val25]
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

lemma hasSum_W225 : HasSum W225 V2val25 := by
  change HasSum (fun m => ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) V2val25
  rw [V2val25]
  apply hasSum_finset_sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := dIdx_bounds k hk
  have hh := (CdtTwoCore.hasSum_pair k (by omega)).mul_left (dj k)
  simpa [cDval, div_eq_mul_inv, mul_comm] using hh

lemma hasSum_Vm25 : HasSum Vm25 Vval25 := by
  have hsum : HasSum (fun m => W125 m + W225 m) Vval25 := by
    simpa [Vval25] using hasSum_W125.add hasSum_W225
  refine hsum.congr_fun (fun m => ?_)
  exact vm25_decomp m


set_option maxHeartbeats 0 in
lemma tsum_Vm25 : (∑' m : ℕ, Vm25 m) = 11756409817108040588403 * A - 11756409817108040588403 * B - 125808567865009046495730414430613843427 / 13696712389360000 := by
  have hval : Vval25 = 11756409817108040588403 * A - 11756409817108040588403 * B - 125808567865009046495730414430613843427 / 13696712389360000 := by
    unfold Vval25 V1val25 V2val25
    simp (maxSteps := 100000000) only [cAval, cDval, aj, dj, cA, cD, Lc, aIdx, dIdx, xm_eq,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      not_false_eq_true, asum0, asum1, asum2, asum3, asum4, asum5, asum6, asum7, asum8, asum9, asum10, asum11, asum12, asum13, asum14, asum15, asum16, asum17, asum18, asum19, asum20, asum21, asum22, asum23, asum24, asum25, asum26, asum27, asum28, asum29, asum30, asum31, asum32, asum33, asum34, asum35, asum36, asum37, asum38, asum39, asum40, asum41, asum42, asum43, asum44, asum45, asum46, asum47, asum48, asum49, asum50,
      bsum0, bsum1, bsum2, bsum3, bsum4, bsum5, bsum6, bsum7, bsum8, bsum9, bsum10, bsum11, bsum12, bsum13, bsum14, bsum15, bsum16, bsum17, bsum18, bsum19, bsum20, bsum21, bsum22, bsum23, bsum24, bsum25, bsum26, bsum27, bsum28, bsum29, bsum30, bsum31, bsum32, bsum33, bsum34, bsum35, bsum36, bsum37, bsum38, bsum39, bsum40, bsum41, bsum42, bsum43, bsum44, bsum45, bsum46, bsum47, bsum48, bsum49, bsum50]
    norm_num (maxSteps := 100000000)
    ring
  rw [hasSum_Vm25.tsum_eq]
  exact hval

end CdtTwentyFiveCore
open CdtTwentyFiveCore

theorem sum_cintegralTwentyFive_core :
    (∑' m : ℕ,
        (717897987691852588770249 : ℝ) * (Nat.choose (m + 50) 50 : ℝ) *
          (∑ i ∈ Finset.range 52,
            ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
              (13142471588392206890177483046912000000 / (((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ) * ((3 * m + 44 + i : ℕ) : ℝ) * ((3 * m + 47 + i : ℕ) : ℝ) * ((3 * m + 50 + i : ℕ) : ℝ) * ((3 * m + 53 + i : ℕ) : ℝ) * ((3 * m + 56 + i : ℕ) : ℝ) * ((3 * m + 59 + i : ℕ) : ℝ) * ((3 * m + 62 + i : ℕ) : ℝ) * ((3 * m + 65 + i : ℕ) : ℝ) * ((3 * m + 68 + i : ℕ) : ℝ) * ((3 * m + 71 + i : ℕ) : ℝ) * ((3 * m + 74 + i : ℕ) : ℝ) * ((3 * m + 77 + i : ℕ) : ℝ) * ((3 * m + 80 + i : ℕ) : ℝ) * ((3 * m + 83 + i : ℕ) : ℝ) * ((3 * m + 86 + i : ℕ) : ℝ) * ((3 * m + 89 + i : ℕ) : ℝ) * ((3 * m + 92 + i : ℕ) : ℝ) * ((3 * m + 95 + i : ℕ) : ℝ) * ((3 * m + 98 + i : ℕ) : ℝ) * ((3 * m + 101 + i : ℕ) : ℝ))) ^ 2)) =
      11756409817108040588403 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 125808567865009046495730414430613843427 / 13696712389360000 := by
  have hMain := tsum_Vm25
  have hL : (∑' m : ℕ, Vm25 m) = (∑' m : ℕ,
        (717897987691852588770249 : ℝ) * (Nat.choose (m + 50) 50 : ℝ) *
          (∑ i ∈ Finset.range 52,
            ((-1 : ℝ) ^ i * (Nat.choose 51 i : ℝ)) *
              (13142471588392206890177483046912000000 / (((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ) * ((3 * m + 44 + i : ℕ) : ℝ) * ((3 * m + 47 + i : ℕ) : ℝ) * ((3 * m + 50 + i : ℕ) : ℝ) * ((3 * m + 53 + i : ℕ) : ℝ) * ((3 * m + 56 + i : ℕ) : ℝ) * ((3 * m + 59 + i : ℕ) : ℝ) * ((3 * m + 62 + i : ℕ) : ℝ) * ((3 * m + 65 + i : ℕ) : ℝ) * ((3 * m + 68 + i : ℕ) : ℝ) * ((3 * m + 71 + i : ℕ) : ℝ) * ((3 * m + 74 + i : ℕ) : ℝ) * ((3 * m + 77 + i : ℕ) : ℝ) * ((3 * m + 80 + i : ℕ) : ℝ) * ((3 * m + 83 + i : ℕ) : ℝ) * ((3 * m + 86 + i : ℕ) : ℝ) * ((3 * m + 89 + i : ℕ) : ℝ) * ((3 * m + 92 + i : ℕ) : ℝ) * ((3 * m + 95 + i : ℕ) : ℝ) * ((3 * m + 98 + i : ℕ) : ℝ) * ((3 * m + 101 + i : ℕ) : ℝ))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm25_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
