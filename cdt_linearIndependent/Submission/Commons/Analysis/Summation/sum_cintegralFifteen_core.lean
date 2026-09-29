import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralTwelve_core

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section
open scoped BigOperators Nat
open Filter Topology
open Polynomial

namespace Commons.Analysis.Summation
namespace CdtFifteenCore

/-! ## The clearing factor and the decomposition coefficients -/

def Lc : ℤ := 3713321059031984400

def cA : ℕ → ℤ := fun j => if j = 16 then (-168390879930807909877101600 : ℤ) else if j = 17 then (3054180834011543755501382400 : ℤ) else if j = 19 then (-155465742119902654091940288000 : ℤ) else if j = 20 then (561885597270890858032651584000 : ℤ) else if j = 22 then (2572879830000827605979110790400 : ℤ) else if j = 23 then (-26930882017477327653083960640000 : ℤ) else if j = 25 then (303094311234957902374676881920000 : ℤ) else if j = 26 then (-465407303082548088282504067584000 : ℤ) else if j = 28 then (-3387282513865015760750587431600000 : ℤ) else if j = 29 then (11666735902579021047846762229530000 : ℤ) else if j = 31 then (-25597549142513294693842090771776000 : ℤ) else if j = 32 then (-18760079536982719806665182717929600 : ℤ) else if j = 34 then (389484880297520499737324554194720000 : ℤ) else if j = 35 then (-565667908600782281097969336146976000 : ℤ) else if j = 37 then (-888552854089284784790777126515776000 : ℤ) else if j = 38 then (3096653918083200420303642787863360000 : ℤ) else if j = 40 then (-4808942269377999133848172474368600000 : ℤ) else if j = 41 then (-1312592588524426490007986413205251200 : ℤ) else if j = 43 then (27329056272624583789300922801579712000 : ℤ) else if j = 44 then (-30377512844870560776100218180591936000 : ℤ) else if j = 46 then (-35297772268425523180270537712048928000 : ℤ) else if j = 47 then (88056560612023246299339904105124640000 : ℤ) else if j = 49 then (-67492452795746230252732518012962736000 : ℤ) else if j = 50 then (-46477952374340621086717948240625568000 : ℤ) else if j = 52 then (259623312807506309909243951538260476800 : ℤ) else if j = 53 then (-199621080131293974373886970986081400000 : ℤ) else if j = 55 then (-249806716710466545261326800490505120000 : ℤ) else if j = 56 then (406667878048184882453194368835032696000 : ℤ) else if j = 58 then (-114248196972066794777361282159562464000 : ℤ) else if j = 59 then (-208100309982039271189537473134725920000 : ℤ) else if j = 61 then (428816516324452421424184383782794470000 : ℤ) else if j = 62 then (-216551045835550392053309022400760160000 : ℤ) else if j = 64 then (-297638207930141417129245093441130328000 : ℤ) else if j = 65 then (339658024501180737317742391099124640000 : ℤ) else if j = 67 then (-26488710583455343602867936338668377600 : ℤ) else if j = 68 then (-124316891696333890486525951831833360000 : ℤ) else if j = 70 then (133030358523904865069843161790705280000 : ℤ) else if j = 71 then (-49565093751744103995238258620916377600 : ℤ) else if j = 73 then (-54124391963745084548266905477688416000 : ℤ) else if j = 74 then (49292279992912543475232155189650272000 : ℤ) else if j = 76 then (-4252673963062087424262733520501913600 : ℤ) else if j = 77 then (-7872417322345642426112687192515857600 : ℤ) else if j = 79 then (6825437580583219969028380198956480000 : ℤ) else if j = 80 then (-2786601443439168873725061549354660000 : ℤ) else if j = 82 then (-794405251379793255611341738950144000 : ℤ) else if j = 83 then (767216371806428297449836956175360000 : ℤ) else if j = 85 then (-161747057416233652593831713352240000 : ℤ) else if j = 86 then (24983506887227995839628357305043200 : ℤ) else if j = 88 then (16391344886625300542049876704928000 : ℤ) else if j = 89 then (-8685649772529021422647419206304000 : ℤ) else if j = 91 then (912935664571535726392651360780800 : ℤ) else if j = 92 then (-181035791511729017942768222332800 : ℤ) else 0

def cD : ℕ → ℤ := fun j => if j = 16 then (1145391076518546208139334949 : ℤ) else if j = 17 then (-9938862772841191460857074412 : ℤ) else if j = 18 then (-99788371760872732661355024360 : ℤ) else if j = 19 then (1111548697885829883718098745269 : ℤ) else if j = 20 then (-2302063630077107350896994345332 : ℤ) else if j = 21 then (-3602360220567505649074916379396 : ℤ) else if j = 22 then (3179224155166872779228703849213 : ℤ) else if j = 23 then (4723430263775442034901046686868 : ℤ) else if j = 24 then (408106022509141923698031968092854 : ℤ) else if j = 25 then (-1638024648546678867678231793299587 : ℤ) else if j = 26 then (1449817148132064875665533583627988 : ℤ) else if j = 27 then (-106743601551583474998852919882986 : ℤ) else if j = 28 then (8127202121065356669505050183548913 : ℤ) else if j = 29 then (-2018128815725953233455175916985037 : ℤ) else if j = 30 then (-86313513684816751076673190128913986 : ℤ) else if j = 31 then (164533720770776605628855134769504673 : ℤ) else if j = 32 then (-119405657197496362308258281821637829 : ℤ) else if j = 33 then (481986361771983426018448735557985134 : ℤ) else if j = 34 then (-1228240499082313975615186539902997527 : ℤ) else if j = 35 then (278606372741658742237286103878771651 : ℤ) else if j = 36 then (1577596755766960654649348118034564026 : ℤ) else if j = 37 then (-242698608735850801021183264242817767 : ℤ) else if j = 38 then (2911652506199038938422003902204132851 : ℤ) else if j = 39 then (-17508022492002031691862418396442589174 : ℤ) else if j = 40 then (21867058759562315792399355794336559483 : ℤ) else if j = 41 then (-10957941556605410623207532725265503353 : ℤ) else if j = 42 then (32381553700153386872920103848830936738 : ℤ) else if j = 43 then (-55258197538575010696728534877429939157 : ℤ) else if j = 44 then (-12351824672730545099030572788684434473 : ℤ) else if j = 45 then (69631349653269675802884925663744800258 : ℤ) else if j = 46 then (-22361381453018038570983943169959410717 : ℤ) else if j = 47 then (108598229044749276101084817482153893647 : ℤ) else if j = 48 then (-332472101807248504895452351154285596662 : ℤ) else if j = 49 then (275704928623622364559101983529455870103 : ℤ) else if j = 50 then (-123374199712063486627180016431954840713 : ℤ) else if j = 51 then (334819817890429850424023312995348397706 : ℤ) else if j = 52 then (-346974451842001803183143665947389225213 : ℤ) else if j = 53 then (-185016250522143181667771709683293540963 : ℤ) else if j = 54 then (334819817890429850424023312995348397706 : ℤ) else if j = 55 then (-101707564119638159617618560325693923813 : ℤ) else if j = 56 then (516208884977450131966373695343455781847 : ℤ) else if j = 57 then (-974098947670400769625717412836625975862 : ℤ) else if j = 58 then (546001100053739220178827808767311300067 : ℤ) else if j = 59 then (-261004768261028686342237077273523504353 : ℤ) else if j = 60 then (582897034208688609382030124572650566058 : ℤ) else if j = 61 then (-338955086092130087745398622268228247318 : ℤ) else if j = 62 then (-312169174251144149557355427447974844553 : ℤ) else if j = 63 then (294425087926413412793531324663347599018 : ℤ) else if j = 64 then (-114154084982722330257185820111594981858 : ℤ) else if j = 65 then (402625558688107542422419069574441264847 : ℤ) else if j = 66 then (-494388420957946037381107016571361786206 : ℤ) else if j = 67 then (185269693904757760793212619882151250374 : ℤ) else if j = 68 then (-75849913160948379231601475011859287053 : ℤ) else if j = 69 then (140208419030372958140409220035003557694 : ℤ) else if j = 70 then (-31053699770637384157395795334742029226 : ℤ) else if j = 71 then (-91589827771606728586559598672773467597 : ℤ) else if j = 72 then (60411462001072116655125381677959395060 : ℤ) else if j = 73 then (-24298104185124766832902119501836673606 : ℤ) else if j = 74 then (42781130904361839579506843628379429083 : ℤ) else if j = 75 then (-35441783659308179881585183121230923180 : ℤ) else if j = 76 then (6141800970591921387572443633470512346 : ℤ) else if j = 77 then (2003105613021040483915286433229936989 : ℤ) else if j = 78 then (908737725801965790454162401910481820 : ℤ) else if j = 79 then (1333943694188238936235769800890701746 : ℤ) else if j = 80 then (-3119656141406940705943105183910671036 : ℤ) else if j = 81 then (1513502159207582160566324686393531020 : ℤ) else if j = 82 then (-219049305004344171995833049892040974 : ℤ) else if j = 83 then (101830678077388431192886852550135364 : ℤ) else if j = 84 then (-69222494971915088538053350913361480 : ℤ) else if j = 85 then (-36986970259103449741718999720202924 : ℤ) else if j = 86 then (44274236342436330598957817607977532 : ℤ) else if j = 87 then (-11850368088462441367199215917871800 : ℤ) else if j = 88 then (-99282724890895507648437238526984 : ℤ) else if j = 89 then (346039095198065544982774451637572 : ℤ) else 0

def aIdx : Finset ℕ := {16, 17, 19, 20, 22, 23, 25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 73, 74, 76, 77, 79, 80, 82, 83, 85, 86, 88, 89, 91, 92}
def dIdx : Finset ℕ := {16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89}

/-! ## index bounds -/

lemma aIdx_bounds (j : ℕ) (hj : j ∈ aIdx) : 16 ≤ j ∧ j ≤ 92 := by
  simp only [aIdx, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

lemma dIdx_bounds (k : ℕ) (hk : k ∈ dIdx) : 16 ≤ k ∧ k ≤ 89 := by
  simp only [dIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  omega



def Sf (i : ℕ) : Finset ℕ := (Finset.range 16).image (fun j => 3 * j + i)

/-! ## polynomials -/

noncomputable def Dpol : ℤ[X] := ∏ τ ∈ Finset.range 77, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2
noncomputable def Qpol (i : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 77, (if τ ∈ Sf i then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Rpol (j : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 77, (if (16 + τ : ℕ) = j then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Tpol (k : ℕ) : ℤ[X] :=
  (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
    (∏ τ ∈ Finset.range 77, (if (16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3 then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)))
noncomputable def Ppol (i : ℕ) : ℤ[X] := ∏ j ∈ Finset.range 16, (C (3:ℤ) * X + C ((16 + 3 * j + i : ℕ) : ℤ))

noncomputable def P1 : ℤ[X] :=
  C ((72489400057790548363973345969624382942570676224000000 : ℤ)) *
    ((∏ r ∈ Finset.range 30, (Polynomial.X + C (((r : ℤ) + 1)))) *
    (∑ i ∈ Finset.range 32, C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) * Qpol i))

noncomputable def P2 : ℤ[X] :=
  C ((265252859812191058636308480000000 : ℤ)) *
    ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k))

/-! ## generic product lemmas -/

lemma prod_ite_one_eq {ι M : Type*} [CommMonoid M] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (f : ι → M) :
    (∏ i ∈ s, (if p i then (1 : M) else f i)) = ∏ i ∈ s.filter (fun i => ¬ p i), f i := by
  rw [Finset.prod_ite]
  simp

lemma Sf_subset (i : ℕ) (hi : i < 32) : Sf i ⊆ Finset.range 77 := by
  intro τ hτ
  simp only [Sf, Finset.mem_image, Finset.mem_range] at hτ ⊢
  obtain ⟨j, hj, rfl⟩ := hτ
  omega

lemma Sf_card (i : ℕ) : (Sf i).card = 16 := by
  rw [Sf, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have h : 3 * x + i = 3 * y + i := hxy
    omega

lemma prod_Sf_eq (i : ℕ) (F : ℕ → ℤ[X]) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 16, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma Ppol_sq_eq (i : ℕ) :
    (Ppol i) ^ 2 = ∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Ppol, prod_Sf_eq i (fun τ => (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  have h : (16 + (3 * j + i) : ℕ) = 16 + 3 * j + i := by omega
  rw [h]

lemma Qpol_eq (i : ℕ) (hi : i < 32) :
    Qpol i = ∏ τ ∈ (Finset.range 77) \ Sf i, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Qpol, prod_ite_one_eq, Finset.sdiff_eq_filter]

lemma prod_range_split (i : ℕ) (hi : i < 32) (F : ℕ → ℤ[X]) :
    (∏ τ ∈ Finset.range 77, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 77) \ Sf i, F τ) := by
  rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset (Sf_subset i hi)]

lemma Dpol_split (i : ℕ) (hi : i < 32) :
    Dpol = (∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2) *
      (∏ τ ∈ (Finset.range 77) \ Sf i, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2) := by
  unfold Dpol
  exact prod_range_split i hi _

lemma Dpol_eq_Ppol_sq_mul_Qpol (i : ℕ) (hi : i < 32) : Dpol = Ppol i ^ 2 * Qpol i := by
  rw [Dpol_split i hi, ← Ppol_sq_eq i, ← Qpol_eq i hi]

lemma Rpol_eq (j : ℕ) :
    Rpol j = ∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = j)),
      (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Rpol, prod_ite_one_eq]

lemma prod_filter_step (j : ℕ) :
    (∏ τ ∈ Finset.range 77, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 77).filter (fun τ => (16 + τ : ℕ) = j),
            (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = j)),
            (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 77) (fun τ => (16 + τ : ℕ) = j) _).symm

lemma filter_eq_singleton (j : ℕ) (h1 : 16 ≤ j) (h2 : j ≤ 92) :
    (Finset.range 77).filter (fun τ => (16 + τ : ℕ) = j) = {j - 16} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hj⟩; omega
  · rintro rfl; constructor <;> omega

lemma Dpol_eq_sq_mul_Rpol (j : ℕ) (h1 : 16 ≤ j) (h2 : j ≤ 92) :
    Dpol = (C (3:ℤ) * X + C (j : ℤ)) ^ 2 * Rpol j := by
  rw [Dpol, prod_filter_step j, Rpol_eq j, filter_eq_singleton j h1 h2, Finset.prod_singleton]
  have e : ((16 + (j - 16) : ℕ) : ℤ) = (j : ℤ) := by omega
  rw [e]

lemma prod_filter_step2 (k : ℕ) :
    (∏ τ ∈ Finset.range 77, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 77).filter (fun τ => ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 77)
    (fun τ => ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)) _).symm

lemma filter_eq_pair (k : ℕ) (h1 : 16 ≤ k) (h2 : k ≤ 89) :
    (Finset.range 77).filter (fun τ => ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)) = {k - 16, k - 13} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hk | hk⟩
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> constructor <;> omega

lemma Dpol_eq_lin_mul_Tpol (k : ℕ) (h1 : 16 ≤ k) (h2 : k ≤ 89) :
    Dpol = (C (3:ℤ) * X + C (k : ℤ)) * (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) * Tpol k := by
  have hne : k - 16 ∉ ({k - 13} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [Tpol, prod_ite_one_eq, Dpol, prod_filter_step2 k, filter_eq_pair k h1 h2,
    Finset.prod_insert hne, Finset.prod_singleton]
  have e1 : ((16 + (k - 16) : ℕ) : ℤ) = (k : ℤ) := by omega
  have e2 : ((16 + (k - 13) : ℕ) : ℤ) = ((k + 3 : ℕ) : ℤ) := by omega
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
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 2 * s.card := by
  have h1 : (∏ τ ∈ s, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤
      ∑ τ ∈ s, ((C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2).natDegree :=
    Polynomial.natDegree_prod_le s (fun τ => (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)
  have h2 : (∑ τ ∈ s, ((C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2).natDegree) ≤ ∑ _τ ∈ s, 2 :=
    Finset.sum_le_sum (fun τ _ => natDegree_sq_lin_le _)
  have h3 : (∑ _τ ∈ s, (2 : ℕ)) = 2 * s.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  linarith

lemma natDegree_prod_sq_le_154 (s : Finset ℕ) (h : s.card ≤ 77) :
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 154 :=
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
    ((Finset.range 77).filter p).card ≤ 77 := by
  have h := Finset.card_le_card (Finset.filter_subset p (Finset.range 77))
  rwa [Finset.card_range] at h

lemma card_sdiff_le (s : Finset ℕ) : ((Finset.range 77) \ s).card ≤ 77 := by
  have h := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range 77) (t := s))
  rwa [Finset.card_range] at h

lemma natDegree_Qpol_le (i : ℕ) (hi : i < 32) : (Qpol i).natDegree ≤ 154 := by
  rw [Qpol_eq i hi]
  exact natDegree_prod_sq_le_154 _ (card_sdiff_le _)

lemma natDegree_Rpol_le (j : ℕ) : (Rpol j).natDegree ≤ 154 := by
  rw [Rpol_eq j]
  exact natDegree_prod_sq_le_154 _ (filter_card_le _)

lemma Tpol_eq' (k : ℕ) :
    Tpol k = (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)) := by
  rw [Tpol, prod_ite_one_eq]

lemma natDegree_Tpol_le (k : ℕ) : (Tpol k).natDegree ≤ 156 := by
  have h1 : (Tpol k).natDegree ≤ (C (3:ℤ) * X + C (k : ℤ)).natDegree +
      ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
        (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
          (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)).natDegree := by
    rw [Tpol_eq' k]
    exact Polynomial.natDegree_mul_le
  have h2 : ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2)).natDegree ≤ 1 + 154 := by
    have hm := Polynomial.natDegree_mul_le (p := (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)))
      (q := (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2))
    have ha : (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
    have hb : (∏ τ ∈ (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((16 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 154 :=
      natDegree_prod_sq_le_154 _ (filter_card_le _)
    linarith
  have h3 : (C (3:ℤ) * X + C (k : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
  linarith

lemma natDegree_P1_le : P1.natDegree ≤ 184 := by
  have h1 : P1.natDegree ≤ (C ((205891132094649 : ℤ) * (18763697892715776000 : ℤ) ^ 2)).natDegree +
      ((∏ r ∈ Finset.range 30, (Polynomial.X + C (((r : ℤ) + 1)))) *
        (∑ i ∈ Finset.range 32,
          C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) * Qpol i)).natDegree := by
    rw [P1]
    exact Polynomial.natDegree_mul_le
  have h2 : ((∏ r ∈ Finset.range 30, (Polynomial.X + C (((r : ℤ) + 1)))) *
      (∑ i ∈ Finset.range 32,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) * Qpol i)).natDegree ≤ 30 + 154 := by
    refine le_trans (Polynomial.natDegree_mul_le) (add_le_add ?_ ?_)
    · have hp : (∏ r ∈ Finset.range 30, (Polynomial.X + C (((r : ℤ) + 1)))).natDegree ≤
          ∑ r ∈ Finset.range 30, (Polynomial.X + C (((r : ℤ) + 1))).natDegree :=
        Polynomial.natDegree_prod_le _ _
      have hq : (∑ r ∈ Finset.range 30, (Polynomial.X + C (((r : ℤ) + 1))).natDegree) = 30 := by
        rw [Finset.sum_congr rfl (fun r _ => Polynomial.natDegree_X_add_C _)]
        simp
      omega
    · exact natDegree_sum_le' _ _ 154 (fun i hi => by
        rw [Finset.mem_range] at hi
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Qpol_le i hi))
  have h3 : (C ((205891132094649 : ℤ) * (18763697892715776000 : ℤ) ^ 2)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma natDegree_P2_le : P2.natDegree ≤ 156 := by
  have h1 : P2.natDegree ≤ (C ((265252859812191058636308480000000 : ℤ))).natDegree +
      ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree := by
    rw [P2]
    exact Polynomial.natDegree_mul_le
  have hR : (∑ j ∈ aIdx, C (cA j) * Rpol j).natDegree ≤ 154 :=
    natDegree_sum_le' _ _ 154 (fun j _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Rpol_le j))
  have hT : (∑ k ∈ dIdx, C (cD k) * Tpol k).natDegree ≤ 156 :=
    natDegree_sum_le' _ _ 156 (fun k _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Tpol_le k))
  have h2 : ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree ≤
      156 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (le_trans hR (by norm_num)) hT)
  have h3 : (C ((265252859812191058636308480000000 : ℤ))).natDegree = 0 := Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma degree_bound : max P1.natDegree P2.natDegree < 185 := by
  rw [max_lt_iff]
  constructor
  · exact lt_of_le_of_lt natDegree_P1_le (by norm_num)
  · exact lt_of_le_of_lt natDegree_P2_le (by norm_num)

/-! ## evaluation of the polynomials (integer form) -/

def EvP1 (c : ℤ) : ℤ := (205891132094649 * 18763697892715776000 ^ 2) *
  ((∏ r ∈ Finset.range 30, (c + ((r : ℤ) + 1))) *
   (∑ i ∈ Finset.range 32, (Lc * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) *
     (∏ τ ∈ Finset.range 77, (if τ ∈ Sf i then 1 else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2))))

def EvP2 (c : ℤ) : ℤ := 265252859812191058636308480000000 *
  ((∑ j ∈ aIdx, cA j * (∏ τ ∈ Finset.range 77, (if (16 + τ : ℕ) = j then 1 else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2)))
   + (∑ k ∈ dIdx, cD k * ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) * (∏ τ ∈ Finset.range 77, (if (16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3 then 1 else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2)))))

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

def Pall (c : ℤ) : ℤ := ∏ τ ∈ Finset.range 77, (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2

lemma prod_Sf_eqZ (i : ℕ) (F : ℕ → ℤ) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 16, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma prod_range_splitZ (i : ℕ) (hi : i < 32) (F : ℕ → ℤ) :
    (∏ τ ∈ Finset.range 77, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 77) \ Sf i, F τ) := by
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

lemma filter_not_eq_erase (j : ℕ) (h1 : 16 ≤ j) (h2 : j ≤ 92) :
    (Finset.range 77).filter (fun τ => ¬ ((16 + τ : ℕ) = j)) =
      (Finset.range 77).erase (j - 16) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨hlt, hne⟩
    exact ⟨fun h => hne (by omega), hlt⟩
  · rintro ⟨hne, hlt⟩
    exact ⟨hlt, fun h => hne (by omega)⟩

lemma filter_not_pair_eq_erase (k : ℕ) (h1 : 16 ≤ k) (h2 : k ≤ 89) :
    (Finset.range 77).filter
        (fun τ => ¬ ((16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3)) =
      ((Finset.range 77).erase (k - 16)).erase (k - 13) := by
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

lemma prod_ite_eq_div {c : ℤ} (hc : 0 ≤ c) (j : ℕ) (h1 : 16 ≤ j) (h2 : j ≤ 92) :
    (∏ τ ∈ Finset.range 77,
        (if (16 + τ : ℕ) = j then (1 : ℤ)
          else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (3 * c + ((16 + (j - 16) : ℕ) : ℤ)) ^ 2 := by
  have hmem : j - 16 ∈ Finset.range 77 := by
    simp only [Finset.mem_range]; omega
  have hne : (3 * c + ((16 + (j - 16) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hj : (16 + (j - 16) : ℕ) = j := by omega
    rw [hj]; exact sqf_ne_zero hc (by omega : 0 < j)
  rw [prod_ite_one_eq, filter_not_eq_erase j h1 h2, Pall]
  exact prod_erase_eq_div _ _ hmem _ hne

lemma prod_ite_pair_eq_div {c : ℤ} (hc : 0 ≤ c) (k : ℕ) (h1 : 16 ≤ k)
    (h2 : k ≤ 89) :
    (∏ τ ∈ Finset.range 77,
        (if (16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3 then (1 : ℤ)
          else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / ((3 * c + ((16 + (k - 16) : ℕ) : ℤ)) ^ 2 *
          (3 * c + ((16 + (k - 13) : ℕ) : ℤ)) ^ 2) := by
  have hmem1 : k - 16 ∈ Finset.range 77 := by
    simp only [Finset.mem_range]; omega
  have hmem2 : k - 13 ∈ (Finset.range 77).erase (k - 16) := by
    simp only [Finset.mem_erase, Finset.mem_range]
    constructor
    · omega
    · omega
  have hne1 : (3 * c + ((16 + (k - 16) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (16 + (k - 16) : ℕ) = k := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k)
  have hne2 : (3 * c + ((16 + (k - 13) : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have hk : (16 + (k - 13) : ℕ) = k + 3 := by omega
    rw [hk]; exact sqf_ne_zero hc (by omega : 0 < k + 3)
  rw [prod_ite_one_eq, filter_not_pair_eq_erase k h1 h2, Pall]
  exact prod_erase_pair_eq_div _ _ _ hmem1 hmem2 _ hne1 hne2

lemma prod_ite_Sf_eq_div {c : ℤ} (hc : 0 ≤ c) (i : ℕ) (hi : i < 32) :
    (∏ τ ∈ Finset.range 77,
        (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2))
      = Pall c / (∏ j ∈ Finset.range 16,
          (3 * c + ((16 + (3 * j + i) : ℕ) : ℤ)) ^ 2) := by
  have hSf : (∏ τ ∈ Sf i, (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ j ∈ Finset.range 16, (3 * c + ((16 + (3 * j + i) : ℕ) : ℤ)) ^ 2) :=
    prod_Sf_eqZ i _
  have hne : (∏ j ∈ Finset.range 16,
      (3 * c + ((16 + (3 * j + i) : ℕ) : ℤ)) ^ 2) ≠ 0 := by
    rw [← hSf]
    exact Finset.prod_ne_zero_iff.mpr (fun τ _ => sqf_ne_zero hc (by omega : 0 < 16 + τ))
  have hsplit : Pall c =
      (∏ j ∈ Finset.range 16, (3 * c + ((16 + (3 * j + i) : ℕ) : ℤ)) ^ 2) *
        (∏ τ ∈ (Finset.range 77) \ Sf i,
          (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2) := by
    rw [Pall, prod_range_splitZ i hi, hSf]
  rw [prod_ite_one_eq, ← Finset.sdiff_eq_filter, hsplit,
    Int.mul_ediv_cancel_left _ hne]

def EvP1cheap (c : ℤ) : ℤ :=
  (205891132094649 * 18763697892715776000 ^ 2) *
    ((∏ r ∈ Finset.range 30, (c + ((r : ℤ) + 1))) *
     (∑ i ∈ Finset.range 32, (Lc * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) *
       (Pall c / (∏ j ∈ Finset.range 16,
         (3 * c + ((16 + (3 * j + i) : ℕ) : ℤ)) ^ 2))))

def EvP2cheap (c : ℤ) : ℤ :=
  (265252859812191058636308480000000) *
    ((∑ j ∈ aIdx, cA j * (Pall c / (3 * c + ((16 + (j - 16) : ℕ) : ℤ)) ^ 2))
     + (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((16 + (k - 16) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((16 + (k - 13) : ℕ) : ℤ)) ^ 2)))))

lemma EvP1_sum_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ i ∈ Finset.range 32, (Lc * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) *
        (∏ τ ∈ Finset.range 77,
          (if τ ∈ Sf i then (1 : ℤ) else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ i ∈ Finset.range 32, (Lc * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) *
        (Pall c / (∏ j ∈ Finset.range 16,
          (3 * c + ((16 + (3 * j + i) : ℕ) : ℤ)) ^ 2))) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [prod_ite_Sf_eq_div hc i hi]

lemma EvP2_sum1_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ j ∈ aIdx, cA j *
        (∏ τ ∈ Finset.range 77,
          (if (16 + τ : ℕ) = j then (1 : ℤ)
            else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2)))
      = (∑ j ∈ aIdx, cA j *
        (Pall c / (3 * c + ((16 + (j - 16) : ℕ) : ℤ)) ^ 2)) := by
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨h1, h2⟩ := aIdx_bounds j hj
  rw [prod_ite_eq_div hc j h1 h2]

lemma EvP2_sum2_eq {c : ℤ} (hc : 0 ≤ c) :
    (∑ k ∈ dIdx, cD k *
        ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
          (∏ τ ∈ Finset.range 77,
            (if (16 + τ : ℕ) = k ∨ (16 + τ : ℕ) = k + 3 then (1 : ℤ)
              else (3 * c + ((16 + τ : ℕ) : ℤ)) ^ 2))))
      = (∑ k ∈ dIdx, cD k *
          ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) *
            (Pall c / ((3 * c + ((16 + (k - 16) : ℕ) : ℤ)) ^ 2 *
              (3 * c + ((16 + (k - 13) : ℕ) : ℤ)) ^ 2)))) := by
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

noncomputable def pts : Finset ℤ := (Finset.range 185).image (fun k : ℕ => (k : ℤ))

lemma pts_card : pts.card = 185 := by
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
  · rw [pts_card]
    exact degree_bound

def Df (m : ℕ) : ℤ := (Dpol).eval (m : ℤ)
def Pf (i : ℕ) (m : ℕ) : ℤ := (Ppol i).eval (m : ℤ)
def Qf (i : ℕ) (m : ℕ) : ℤ := (Qpol i).eval (m : ℤ)
def Rf (j : ℕ) (m : ℕ) : ℤ := (Rpol j).eval (m : ℤ)
def Tf (k : ℕ) (m : ℕ) : ℤ := (Tpol k).eval (m : ℤ)

lemma Pf_pos (i m : ℕ) (hi : i < 32) : 0 < Pf i m := by
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

lemma Df_eq_Pf_sq_mul_Qf (i m : ℕ) (hi : i < 32) : Df m = (Pf i m) ^ 2 * Qf i m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_Ppol_sq_mul_Qpol i hi)
  simpa [Df, Pf, Qf, Polynomial.eval_mul, Polynomial.eval_pow] using h

lemma Df_eq_sq_mul_Rf (j m : ℕ) (h1 : 16 ≤ j) (h2 : j ≤ 92) :
    Df m = (3 * (m : ℤ) + (j : ℤ)) ^ 2 * Rf j m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_sq_mul_Rpol j h1 h2)
  simpa [Df, Rf, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

lemma Df_eq_lin_mul_Tf (k m : ℕ) (h1 : 16 ≤ k) (h2 : k ≤ 89) :
    Df m = (3 * (m : ℤ) + (k : ℤ)) * (3 * (m : ℤ) + ((k + 3 : ℕ) : ℤ)) * Tf k m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_lin_mul_Tpol k h1 h2)
  simpa [Df, Tf, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h


/-! ## real-valued definitions -/

noncomputable def cFifteenPf (i : ℕ) (m : ℕ) : ℝ := ∏ j ∈ Finset.range 16, xm m (16 + 3 * j + i)

noncomputable def Vm15 (m : ℕ) : ℝ := (205891132094649 : ℝ) * (Nat.choose (m + 30) 30 : ℝ) *
  (∑ i ∈ Finset.range 32, ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
    (18763697892715776000 / cFifteenPf i m) ^ 2)

noncomputable def aj (j : ℕ) : ℝ := (cA j : ℝ) / (Lc : ℝ)
noncomputable def dj (k : ℕ) : ℝ := (cD k : ℝ) / (3 * (Lc : ℝ))

noncomputable def W115 (m : ℕ) : ℝ := ∑ j ∈ aIdx, aj j / (xm m j) ^ 2
noncomputable def W215 (m : ℕ) : ℝ := ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))
noncomputable def Vd15 (m : ℕ) : ℝ := W115 m + W215 m

lemma cFifteenPf_eq (i m : ℕ) : cFifteenPf i m = ((Pf i m : ℤ) : ℝ) := by
  have h : ((Pf i m : ℤ) : ℝ) = ∏ j ∈ Finset.range 16,
      ((3 : ℝ) * (m : ℝ) + ((16 + 3 * j + i : ℕ) : ℝ)) := by
    rw [Pf, Ppol, Polynomial.eval_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    ring
  rw [h, cFifteenPf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [xm_eq]

lemma eval_prodP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∏ r ∈ Finset.range 30, (Polynomial.X + C ((r : ℤ) + 1))) =
      ∏ r ∈ Finset.range 30, ((m : ℤ) + (r + 1)) := by
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

lemma eval_sumP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∑ i ∈ Finset.range 32,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ)) * Qpol i) =
      ∑ i ∈ Finset.range 32, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ) * (Qf i m) := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.eval_mul, Polynomial.eval_C, Qf]

lemma eval_P1_int (m : ℕ) :
    P1.eval (m : ℤ) = (205891132094649 * 18763697892715776000 ^ 2) *
      (∏ r ∈ Finset.range 30, ((m : ℤ) + (r + 1))) *
      (∑ i ∈ Finset.range 32, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 31 i : ℤ) * (Qf i m)) := by
  rw [P1, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_prodP m, eval_sumP m]
  ring

lemma eval_P1 (m : ℕ) :
    ((P1.eval (m : ℤ) : ℤ) : ℝ) = (205891132094649 : ℝ) * (18763697892715776000 : ℝ) ^ 2 *
      (∏ r ∈ Finset.range 30, ((m : ℝ) + (r + 1))) *
      (∑ i ∈ Finset.range 32, (Lc : ℝ) * (-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ) * ((Qf i m : ℤ) : ℝ)) := by
  rw [eval_P1_int m]
  push_cast
  ring

lemma eval_P2_int (m : ℕ) :
    P2.eval (m : ℤ) = 265252859812191058636308480000000 *
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
    ((P2.eval (m : ℤ) : ℤ) : ℝ) = (265252859812191058636308480000000 : ℝ) *
      ((∑ j ∈ aIdx, (cA j : ℝ) * ((Rf j m : ℤ) : ℝ)) +
        (∑ k ∈ dIdx, (cD k : ℝ) * ((Tf k m : ℤ) : ℝ))) := by
  rw [eval_P2_int m]
  push_cast
  ring


/-! ## the factorial identity -/

lemma choose_fact_nat (m : ℕ) :
    (m + 30).choose 30 * (30 !) = ∏ r ∈ Finset.range 30, (m + r + 1) := by
  have h2 : (m + 1).ascFactorial 30 = 30 ! * (m + 30).choose 30 := by
    simpa using Nat.ascFactorial_eq_factorial_mul_choose m 30
  have h1 : (m + 1).ascFactorial 30 = ∏ i ∈ Finset.range 30, (m + 1 + i) :=
    Nat.ascFactorial_eq_prod_range (m + 1) 30
  rw [h2, Nat.mul_comm] at h1
  rw [h1]
  apply Finset.prod_congr rfl
  intro r hr
  omega

lemma choose_fact (m : ℕ) :
    (Nat.choose (m + 30) 30 : ℝ) * 265252859812191058636308480000000 = ∏ r ∈ Finset.range 30, ((m : ℝ) + (r + 1)) := by
  have h : ((m + 30).choose 30 : ℝ) * ((30 ! : ℕ) : ℝ) =
      ((∏ r ∈ Finset.range 30, (m + r + 1) : ℕ) : ℝ) := by
    exact_mod_cast choose_fact_nat m
  have h24 : ((30 ! : ℕ) : ℝ) = 265252859812191058636308480000000 := by norm_num
  rw [h24] at h
  rw [h]
  push_cast
  apply Finset.prod_congr rfl
  intro r hr
  ring


/-! ## the two clearing identities -/

lemma clear_left (m : ℕ) :
    Vm15 m * ((Df m : ℤ) : ℝ) * 265252859812191058636308480000000 * (Lc : ℝ) =
      ((P1.eval (m : ℤ) : ℤ) : ℝ) := by
  have hgoal : Vm15 m * ((Df m : ℤ) : ℝ) * 265252859812191058636308480000000 * (Lc : ℝ) =
      (205891132094649 : ℝ) * ((Nat.choose (m + 30) 30 : ℝ) * 265252859812191058636308480000000) *
        ((∑ i ∈ Finset.range 32, ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
            (18763697892715776000 / cFifteenPf i m) ^ 2) * ((Df m : ℤ) : ℝ)) * (Lc : ℝ) := by
    rw [Vm15]
    ring
  have hsum : (∑ i ∈ Finset.range 32, ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
        (18763697892715776000 / cFifteenPf i m) ^ 2) * ((Df m : ℤ) : ℝ) =
      (18763697892715776000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 32,
        ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cFifteenPf_eq i m]
    have hD : ((Df m : ℤ) : ℝ) = ((((Pf i m : ℤ)) : ℝ)) ^ 2 * ((Qf i m : ℤ) : ℝ) := by
      rw [Df_eq_Pf_sq_mul_Qf i m hi]
      simp only [Int.cast_mul, Int.cast_pow]
    rw [hD]
    have hne : (((Pf i m : ℤ)) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Pf_pos i m hi))
    field_simp
    try ring
  have hLc2 : ((18763697892715776000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 32,
        ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ) =
      (18763697892715776000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 32,
        (Lc : ℝ) * ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [show ((18763697892715776000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 32,
          ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
        = (18763697892715776000 : ℝ) ^ 2 * ((Lc : ℝ) * (∑ i ∈ Finset.range 32,
          ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) by ring]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hgoal, choose_fact m, hsum, eval_P1 m]
  rw [show (205891132094649 : ℝ) * (∏ r ∈ Finset.range 30, ((m : ℝ) + (r + 1))) *
        ((18763697892715776000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 32,
          ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
      = (205891132094649 : ℝ) * (∏ r ∈ Finset.range 30, ((m : ℝ) + (r + 1))) *
        (((18763697892715776000 : ℝ) ^ 2 * (∑ i ∈ Finset.range 32,
          ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)) by ring]
  rw [hLc2]
  ring

lemma clear_right (m : ℕ) :
    Vd15 m * ((Df m : ℤ) : ℝ) * 265252859812191058636308480000000 * (Lc : ℝ) =
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
  rw [eval_P2 m, Vd15]
  rw [show (W115 m + W215 m) * ((Df m : ℤ) : ℝ) * 265252859812191058636308480000000 * (Lc : ℝ) =
      ((∑ j ∈ aIdx, aj j / (xm m j) ^ 2) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) +
        (∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) * ((Df m : ℤ) : ℝ) * (Lc : ℝ)) *
        265252859812191058636308480000000 by
    rw [W115, W215]
    ring]
  rw [hW1, hW2]
  ring

theorem vm15_decomp (m : ℕ) : Vm15 m = Vd15 m := by
  have h1 := clear_left m
  have h2 := clear_right m
  have hP : ((P1.eval (m : ℤ) : ℤ) : ℝ) = ((P2.eval (m : ℤ) : ℤ) : ℝ) := by rw [poly_eq]
  have hDf : ((Df m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Df_pos m))
  have hFT : (265252859812191058636308480000000 : ℝ) ≠ 0 := by norm_num
  have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
  have h := h1.trans (hP.trans h2.symm)
  have h' : (Vm15 m * ((Df m : ℤ) : ℝ)) * 265252859812191058636308480000000 =
      (Vd15 m * ((Df m : ℤ) : ℝ)) * 265252859812191058636308480000000 := mul_right_cancel₀ hLc h
  have h'' : Vm15 m * ((Df m : ℤ) : ℝ) = Vd15 m * ((Df m : ℤ) : ℝ) := mul_right_cancel₀ hFT h'
  exact mul_right_cancel₀ hDf h''

lemma denom_statement15 (m : ℕ) (i : ℕ) :
    (((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ))
      = cFifteenPf i m := by
  rw [cFifteenPf]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  simp only [xm_eq]
  push_cast
  ring

lemma inner_sum_statement15 (m : ℕ) :
    (∑ i ∈ Finset.range 32,
      ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
        (18763697892715776000 / (((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ))) ^ 2)
    = (∑ i ∈ Finset.range 32,
      ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
        (18763697892715776000 / cFifteenPf i m) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [denom_statement15 m i]

lemma vm15_eq_statement (m : ℕ) :
    (205891132094649 : ℝ) * (Nat.choose (m + 30) 30 : ℝ) *
      (∑ i ∈ Finset.range 32,
        ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
          (18763697892715776000 / (((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ))) ^ 2) =
      Vm15 m := by
  rw [Vm15, inner_sum_statement15 m]

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

def cAval (j : ℕ) : ℝ := if j % 3 = 1 then (A - Asum (j / 3)) else (B - Bsum (j / 3))
def cDval (k : ℕ) : ℝ := 1 / xm 0 k

noncomputable def V1val15 : ℝ := ∑ j ∈ aIdx, aj j * cAval j
noncomputable def V2val15 : ℝ := ∑ k ∈ dIdx, dj k * cDval k
noncomputable def Vval15 : ℝ := V1val15 + V2val15

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

lemma hasSum_W115 : HasSum W115 V1val15 := by
  change HasSum (fun m => ∑ j ∈ aIdx, aj j / (xm m j) ^ 2) V1val15
  rw [V1val15]
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

lemma hasSum_W215 : HasSum W215 V2val15 := by
  change HasSum (fun m => ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) V2val15
  rw [V2val15]
  apply hasSum_finset_sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := dIdx_bounds k hk
  have hh := (CdtTwoCore.hasSum_pair k (by omega)).mul_left (dj k)
  simpa [cDval, div_eq_mul_inv, mul_comm] using hh

lemma hasSum_Vm15 : HasSum Vm15 Vval15 := by
  have hsum : HasSum (fun m => W115 m + W215 m) Vval15 := by
    simpa [Vval15] using hasSum_W115.add hasSum_W215
  refine hsum.congr_fun (fun m => ?_)
  exact vm15_decomp m


set_option maxHeartbeats 0 in
lemma tsum_Vm15 : (∑' m : ℕ, Vm15 m) = 5582724468093 * A - 5582724468093 * B - 699283848231726007461 / 160320160 := by
  have hval : Vval15 = 5582724468093 * A - 5582724468093 * B - 699283848231726007461 / 160320160 := by
    unfold Vval15 V1val15 V2val15
    simp only [cAval, cDval, aj, dj, cA, cD, Lc, aIdx, dIdx, xm_eq,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      not_false_eq_true, asum0, asum1, asum2, asum3, asum4, asum5, asum6, asum7, asum8, asum9, asum10, asum11, asum12, asum13, asum14, asum15, asum16, asum17, asum18, asum19, asum20, asum21, asum22, asum23, asum24, asum25, asum26, asum27, asum28, asum29, asum30,
      bsum0, bsum1, bsum2, bsum3, bsum4, bsum5, bsum6, bsum7, bsum8, bsum9, bsum10, bsum11, bsum12, bsum13, bsum14, bsum15, bsum16, bsum17, bsum18, bsum19, bsum20, bsum21, bsum22, bsum23, bsum24, bsum25, bsum26, bsum27, bsum28, bsum29, bsum30]
    norm_num
    ring
  rw [hasSum_Vm15.tsum_eq]
  exact hval

end CdtFifteenCore
open CdtFifteenCore

theorem sum_cintegralFifteen_core :
    (∑' m : ℕ,
        (205891132094649 : ℝ) * (Nat.choose (m + 30) 30 : ℝ) *
          (∑ i ∈ Finset.range 32,
            ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
              (18763697892715776000 / ((((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ)))) ^ 2)) =
      5582724468093 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 699283848231726007461 / 160320160 := by
  have hMain := tsum_Vm15
  have hL : (∑' m : ℕ, Vm15 m) = (∑' m : ℕ,
        (205891132094649 : ℝ) * (Nat.choose (m + 30) 30 : ℝ) *
          (∑ i ∈ Finset.range 32,
            ((-1 : ℝ) ^ i * (Nat.choose 31 i : ℝ)) *
              (18763697892715776000 / ((((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ) * ((3 * m + 52 + i : ℕ) : ℝ) * ((3 * m + 55 + i : ℕ) : ℝ) * ((3 * m + 58 + i : ℕ) : ℝ) * ((3 * m + 61 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm15_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
