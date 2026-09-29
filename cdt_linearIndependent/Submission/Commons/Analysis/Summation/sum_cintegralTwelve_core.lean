import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralTen_core

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section
open scoped BigOperators Nat
open Filter Topology
open Polynomial

namespace Commons.Analysis.Summation
namespace CdtTwelveCore

def Lc : ℤ := 189697116681072

def cA : ℕ → ℤ := fun j => if j = 13 then (196482475310257936800 : ℤ) else if j = 14 then (-2874697483829641470000 : ℤ) else if j = 16 then (93339166406710329705600 : ℤ) else if j = 17 then (-251189083587045223620000 : ℤ) else if j = 19 then (-1852236964538355633638400 : ℤ) else if j = 20 then (10569370500546610072320000 : ℤ) else if j = 22 then (-59814352808800964894520000 : ℤ) else if j = 23 then (39789034057414889511264000 : ℤ) else if j = 25 then (724605003154397249129044800 : ℤ) else if j = 26 then (-1583333863165431737121762000 : ℤ) else if j = 28 then (150394760062491617927654400 : ℤ) else if j = 29 then (5856571581692777711784018000 : ℤ) else if j = 31 then (-22946963215201940356156915200 : ℤ) else if j = 32 then (15338148565041062475034320000 : ℤ) else if j = 34 then (76864330264271659923978964800 : ℤ) else if j = 35 then (-126280952313858524422880640000 : ℤ) else if j = 37 then (-6092252771508745246445040000 : ℤ) else if j = 38 then (210792738268464793635571977600 : ℤ) else if j = 40 then (-401716195084019958135241248000 : ℤ) else if j = 41 then (138609505293860544040676779200 : ℤ) else if j = 43 then (748905938424691736083332537600 : ℤ) else if j = 44 then (-837742260060483929814331468800 : ℤ) else if j = 46 then (-242997879808338484227909310800 : ℤ) else if j = 47 then (882687849549968465372809440000 : ℤ) else if j = 49 then (-730725527800107255921417712800 : ℤ) else if j = 50 then (26604631693746235693022659200 : ℤ) else if j = 52 then (882208111821286176919792800000 : ℤ) else if j = 53 then (-682569421286873219693582788800 : ℤ) else if j = 55 then (-222879165700286335413084912000 : ℤ) else if j = 56 then (429781093000511529527720870400 : ℤ) else if j = 58 then (-185687769560729834508916806000 : ℤ) else if j = 59 then (-6273764189496809430154329600 : ℤ) else if j = 61 then (117551403360177283623804678000 : ℤ) else if j = 62 then (-72970550763924371485948020000 : ℤ) else if j = 64 then (-7689314422003111042777632000 : ℤ) else if j = 65 then (16432213533436102808850444000 : ℤ) else if j = 67 then (-6284778627047715367372800000 : ℤ) else if j = 68 then (1693870704070326226962316800 : ℤ) else if j = 70 then (618632389693243865747808000 : ℤ) else if j = 71 then (-414599243011977754505174400 : ℤ) else if j = 73 then (59812523865368882047440000 : ℤ) else if j = 74 then (-13653314588984425125170400 : ℤ) else 0
def cD : ℕ → ℤ := fun j => if j = 13 then (-1250144286845413847097 : ℤ) else if j = 14 then (8148746698366473459975 : ℤ) else if j = 15 then (75629684833451917089480 : ℤ) else if j = 16 then (-634925451762922444735821 : ℤ) else if j = 17 then (1003493843161974882828825 : ℤ) else if j = 18 then (734404044830098879105740 : ℤ) else if j = 19 then (3422474801787379042920915 : ℤ) else if j = 20 then (-3478781253802765654232775 : ℤ) else if j = 21 then (-115636792982915962125642690 : ℤ) else if j = 22 then (330931375274838260402173965 : ℤ) else if j = 23 then (-241428441885239338237101495 : ℤ) else if j = 24 then (481926381104316826202006430 : ℤ) else if j = 25 then (-2072685967820684736614527305 : ℤ) else if j = 26 then (336411834299008780702810890 : ℤ) else if j = 27 then (7657013703751050338700482430 : ℤ) else if j = 28 then (-8568777519435559632282237033 : ℤ) else if j = 29 then (9640639862415000614756840625 : ℤ) else if j = 30 then (-49005957506971978140748994835 : ℤ) else if j = 31 then (77434197808610701408131044391 : ℤ) else if j = 32 then (-20944268473243587513240825975 : ℤ) else if j = 33 then (20194602326956239384334463370 : ℤ) else if j = 34 then (-99785502383562019230773629935 : ℤ) else if j = 35 then (-100394880878454052450297514775 : ℤ) else if j = 36 then (429454385200350191104841280330 : ℤ) else if j = 37 then (-319248721574900552704751608635 : ℤ) else if j = 38 then (346660741538673522210329954877 : ℤ) else if j = 39 then (-999916534239638037223125545010 : ℤ) else if j = 40 then (928581421789484178362133047325 : ℤ) else if j = 41 then (-37336550317694228730833704089 : ℤ) else if j = 42 then (183832259417741035213529893515 : ℤ) else if j = 43 then (-434414394344361184070067055827 : ℤ) else if j = 44 then (-998486369462806213988614391865 : ℤ) else if j = 45 then (1841080570538071736624847507450 : ℤ) else if j = 46 then (-943351460178118249812939549036 : ℤ) else if j = 47 then (1143797402819642599411068709935 : ℤ) else if j = 48 then (-2100518025493410953612879192730 : ℤ) else if j = 49 then (1110128575233958019079290832570 : ℤ) else if j = 50 then (166885704355126147041742192155 : ℤ) else if j = 51 then (156611686111367810421431131110 : ℤ) else if j = 52 then (-75016154143011267860017553430 : ℤ) else if j = 53 then (-911679023998967243066694953967 : ℤ) else if j = 54 then (940884697562554275705710324100 : ℤ) else if j = 55 then (-351580765600576451027625506190 : ℤ) else if j = 56 then (368159926398519475061584097409 : ℤ) else if j = 57 then (-435216031840719273080919838050 : ℤ) else if j = 58 then (94005135339526548304958066055 : ℤ) else if j = 59 then (102416829262499603686007613585 : ℤ) else if j = 60 then (-37921196661023000303147081250 : ℤ) else if j = 61 then (31535281614391555691572472370 : ℤ) else if j = 62 then (-71515137655835197383323336340 : ℤ) else if j = 63 then (44798619866195367109637489790 : ℤ) else if j = 64 then (-6554941601671553186001960990 : ℤ) else if j = 65 then (619807797107084966698496295 : ℤ) else if j = 66 then (-1633487747875311231257133780 : ℤ) else if j = 67 then (-1421993593021701256647144990 : ℤ) else if j = 68 then (2050688308040632305923964567 : ℤ) else if j = 69 then (-669700859200216725827345400 : ℤ) else if j = 70 then (5788112679271324852727550 : ℤ) else if j = 71 then (23253524575004291921163291 : ℤ) else 0

def aIdx : Finset ℕ := {13, 14, 16, 17, 19, 20, 22, 23, 25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 73, 74}
def dIdx : Finset ℕ := {13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71}

def Sf (i : ℕ) : Finset ℕ := (Finset.range 13).image (fun j => 3 * j + i)

/-! ## polynomials -/

noncomputable def Dpol : ℤ[X] := ∏ τ ∈ Finset.range 62, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2
noncomputable def Qpol (i : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 62, (if τ ∈ Sf i then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Rpol (j : ℕ) : ℤ[X] := ∏ τ ∈ Finset.range 62, (if (13 + τ : ℕ) = j then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
noncomputable def Tpol (k : ℕ) : ℤ[X] :=
  (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
    (∏ τ ∈ Finset.range 62, (if (13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3 then (1 : ℤ[X]) else (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)))
noncomputable def Ppol (i : ℕ) : ℤ[X] := ∏ j ∈ Finset.range 13, (C (3:ℤ) * X + C ((13 + 3 * j + i : ℕ) : ℤ))

noncomputable def P1 : ℤ[X] :=
  C ((18301814732208855860019323385991004160000 : ℤ)) *
    ((∏ r ∈ Finset.range 24, (Polynomial.X + C (((r : ℤ) + 1)))) *
    (∑ i ∈ Finset.range 26, C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ)) * Qpol i))

noncomputable def P2 : ℤ[X] :=
  C ((620448401733239439360000 : ℤ)) *
    ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k))

/-! ## generic product lemmas -/

lemma prod_ite_one_eq {ι M : Type*} [CommMonoid M] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (f : ι → M) :
    (∏ i ∈ s, (if p i then (1 : M) else f i)) = ∏ i ∈ s.filter (fun i => ¬ p i), f i := by
  rw [Finset.prod_ite]
  simp

lemma Sf_subset (i : ℕ) (hi : i < 26) : Sf i ⊆ Finset.range 62 := by
  intro τ hτ
  simp only [Sf, Finset.mem_image, Finset.mem_range] at hτ ⊢
  obtain ⟨j, hj, rfl⟩ := hτ
  omega

lemma Sf_card (i : ℕ) : (Sf i).card = 13 := by
  rw [Sf, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have h : 3 * x + i = 3 * y + i := hxy
    omega

lemma prod_Sf_eq (i : ℕ) (F : ℕ → ℤ[X]) :
    ∏ τ ∈ Sf i, F τ = ∏ j ∈ Finset.range 13, F (3 * j + i) := by
  rw [Sf, Finset.prod_image]
  intro x _ y _ hxy
  have h : 3 * x + i = 3 * y + i := hxy
  omega

lemma Ppol_sq_eq (i : ℕ) :
    (Ppol i) ^ 2 = ∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Ppol, prod_Sf_eq i (fun τ => (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  have h : (13 + (3 * j + i) : ℕ) = 13 + 3 * j + i := by omega
  rw [h]

lemma Qpol_eq (i : ℕ) (hi : i < 26) :
    Qpol i = ∏ τ ∈ (Finset.range 62) \ Sf i, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Qpol, prod_ite_one_eq, Finset.sdiff_eq_filter]

lemma prod_range_split (i : ℕ) (hi : i < 26) (F : ℕ → ℤ[X]) :
    (∏ τ ∈ Finset.range 62, F τ) =
      (∏ τ ∈ Sf i, F τ) * (∏ τ ∈ (Finset.range 62) \ Sf i, F τ) := by
  rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset (Sf_subset i hi)]

lemma Dpol_split (i : ℕ) (hi : i < 26) :
    Dpol = (∏ τ ∈ Sf i, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2) *
      (∏ τ ∈ (Finset.range 62) \ Sf i, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2) := by
  unfold Dpol
  exact prod_range_split i hi _

lemma Dpol_eq_Ppol_sq_mul_Qpol (i : ℕ) (hi : i < 26) : Dpol = Ppol i ^ 2 * Qpol i := by
  rw [Dpol_split i hi, ← Ppol_sq_eq i, ← Qpol_eq i hi]

lemma Rpol_eq (j : ℕ) :
    Rpol j = ∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = j)),
      (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2 := by
  rw [Rpol, prod_ite_one_eq]

lemma prod_filter_step (j : ℕ) :
    (∏ τ ∈ Finset.range 62, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 62).filter (fun τ => (13 + τ : ℕ) = j),
            (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = j)),
            (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 62) (fun τ => (13 + τ : ℕ) = j) _).symm

lemma filter_eq_singleton (j : ℕ) (h1 : 13 ≤ j) (h2 : j ≤ 74) :
    (Finset.range 62).filter (fun τ => (13 + τ : ℕ) = j) = {j - 13} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hj⟩; omega
  · rintro rfl; constructor <;> omega

lemma Dpol_eq_sq_mul_Rpol (j : ℕ) (h1 : 13 ≤ j) (h2 : j ≤ 74) :
    Dpol = (C (3:ℤ) * X + C (j : ℤ)) ^ 2 * Rpol j := by
  rw [Dpol, prod_filter_step j, Rpol_eq j, filter_eq_singleton j h1 h2, Finset.prod_singleton]
  have e : ((13 + (j - 13) : ℕ) : ℤ) = (j : ℤ) := by omega
  rw [e]

lemma prod_filter_step2 (k : ℕ) :
    (∏ τ ∈ Finset.range 62, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
      = (∏ τ ∈ (Finset.range 62).filter (fun τ => ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
        * (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
            (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2) :=
  (Finset.prod_filter_mul_prod_filter_not (Finset.range 62)
    (fun τ => ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)) _).symm

lemma filter_eq_pair (k : ℕ) (h1 : 13 ≤ k) (h2 : k ≤ 71) :
    (Finset.range 62).filter (fun τ => ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)) = {k - 13, k - 10} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hlt, hk | hk⟩
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> constructor <;> omega

lemma Dpol_eq_lin_mul_Tpol (k : ℕ) (h1 : 13 ≤ k) (h2 : k ≤ 71) :
    Dpol = (C (3:ℤ) * X + C (k : ℤ)) * (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) * Tpol k := by
  have hne : k - 13 ∉ ({k - 10} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [Tpol, prod_ite_one_eq, Dpol, prod_filter_step2 k, filter_eq_pair k h1 h2,
    Finset.prod_insert hne, Finset.prod_singleton]
  have e1 : ((13 + (k - 13) : ℕ) : ℤ) = (k : ℤ) := by omega
  have e2 : ((13 + (k - 10) : ℕ) : ℤ) = ((k + 3 : ℕ) : ℤ) := by omega
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
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 2 * s.card := by
  have h1 : (∏ τ ∈ s, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤
      ∑ τ ∈ s, ((C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2).natDegree :=
    Polynomial.natDegree_prod_le s (fun τ => (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)
  have h2 : (∑ τ ∈ s, ((C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2).natDegree) ≤ ∑ _τ ∈ s, 2 :=
    Finset.sum_le_sum (fun τ _ => natDegree_sq_lin_le _)
  have h3 : (∑ _τ ∈ s, (2 : ℕ)) = 2 * s.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  linarith

lemma natDegree_prod_sq_le_124 (s : Finset ℕ) (h : s.card ≤ 62) :
    (∏ τ ∈ s, (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 124 :=
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
    ((Finset.range 62).filter p).card ≤ 62 := by
  have h := Finset.card_le_card (Finset.filter_subset p (Finset.range 62))
  rwa [Finset.card_range] at h

lemma card_sdiff_le (s : Finset ℕ) : ((Finset.range 62) \ s).card ≤ 62 := by
  have h := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range 62) (t := s))
  rwa [Finset.card_range] at h

lemma natDegree_Qpol_le (i : ℕ) (hi : i < 26) : (Qpol i).natDegree ≤ 124 := by
  rw [Qpol_eq i hi]
  exact natDegree_prod_sq_le_124 _ (card_sdiff_le _)

lemma natDegree_Rpol_le (j : ℕ) : (Rpol j).natDegree ≤ 124 := by
  rw [Rpol_eq j]
  exact natDegree_prod_sq_le_124 _ (filter_card_le _)

lemma Tpol_eq' (k : ℕ) :
    Tpol k = (C (3:ℤ) * X + C (k : ℤ)) * ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)) := by
  rw [Tpol, prod_ite_one_eq]

lemma natDegree_Tpol_le (k : ℕ) : (Tpol k).natDegree ≤ 126 := by
  have h1 : (Tpol k).natDegree ≤ (C (3:ℤ) * X + C (k : ℤ)).natDegree +
      ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
        (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
          (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)).natDegree := by
    rw [Tpol_eq' k]
    exact Polynomial.natDegree_mul_le
  have h2 : ((C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)) *
      (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2)).natDegree ≤ 1 + 124 := by
    have hm := Polynomial.natDegree_mul_le (p := (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)))
      (q := (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2))
    have ha : (C (3:ℤ) * X + C ((k + 3 : ℕ) : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
    have hb : (∏ τ ∈ (Finset.range 62).filter (fun τ => ¬ ((13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3)),
        (C (3:ℤ) * X + C ((13 + τ : ℕ) : ℤ)) ^ 2).natDegree ≤ 124 :=
      natDegree_prod_sq_le_124 _ (filter_card_le _)
    linarith
  have h3 : (C (3:ℤ) * X + C (k : ℤ)).natDegree ≤ 1 := natDegree_lin_le _
  linarith

lemma natDegree_P1_le : P1.natDegree ≤ 148 := by
  have h1 : P1.natDegree ≤ (C ((282429536481 : ℤ) * (254561089305600 : ℤ) ^ 2)).natDegree +
      ((∏ r ∈ Finset.range 24, (Polynomial.X + C ((r : ℤ) + 1))) *
        (∑ i ∈ Finset.range 26,
          C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ)) * Qpol i)).natDegree := by
    rw [P1]
    exact Polynomial.natDegree_mul_le
  have h2 : ((∏ r ∈ Finset.range 24, (Polynomial.X + C ((r : ℤ) + 1))) *
      (∑ i ∈ Finset.range 26,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ)) * Qpol i)).natDegree ≤ 24 + 124 := by
    refine le_trans (Polynomial.natDegree_mul_le) (add_le_add ?_ ?_)
    · have hp : (∏ r ∈ Finset.range 24, (Polynomial.X + C ((r : ℤ) + 1))).natDegree ≤
          ∑ r ∈ Finset.range 24, (Polynomial.X + C ((r : ℤ) + 1)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      have hq : (∑ r ∈ Finset.range 24, (Polynomial.X + C ((r : ℤ) + 1)).natDegree) = 24 := by
        rw [Finset.sum_congr rfl (fun r _ => Polynomial.natDegree_X_add_C _)]
        simp
      omega
    · exact natDegree_sum_le' _ _ 124 (fun i hi => by
        rw [Finset.mem_range] at hi
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Qpol_le i hi))
  have h3 : (C ((282429536481 : ℤ) * (254561089305600 : ℤ) ^ 2)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma natDegree_P2_le : P2.natDegree ≤ 126 := by
  have h1 : P2.natDegree ≤ (C ((620448401733239439360000 : ℤ))).natDegree +
      ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree := by
    rw [P2]
    exact Polynomial.natDegree_mul_le
  have hR : (∑ j ∈ aIdx, C (cA j) * Rpol j).natDegree ≤ 124 :=
    natDegree_sum_le' _ _ 124 (fun j _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Rpol_le j))
  have hT : (∑ k ∈ dIdx, C (cD k) * Tpol k).natDegree ≤ 126 :=
    natDegree_sum_le' _ _ 126 (fun k _ =>
      le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Tpol_le k))
  have h2 : ((∑ j ∈ aIdx, C (cA j) * Rpol j) + (∑ k ∈ dIdx, C (cD k) * Tpol k)).natDegree ≤
      126 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (le_trans hR (by norm_num)) hT)
  have h3 : (C ((620448401733239439360000 : ℤ))).natDegree = 0 := Polynomial.natDegree_C _
  rw [h3] at h1
  linarith

lemma degree_bound : max P1.natDegree P2.natDegree < 149 := by
  rw [max_lt_iff]
  constructor
  · exact lt_of_le_of_lt natDegree_P1_le (by norm_num)
  · exact lt_of_le_of_lt natDegree_P2_le (by norm_num)


/-! ## evaluation of the polynomials (integer form) -/

def EvP1 (c : ℤ) : ℤ := (282429536481 * 254561089305600 ^ 2) *
  ((∏ r ∈ Finset.range 24, (c + ((r : ℤ) + 1))) *
   (∑ i ∈ Finset.range 26, (Lc * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ)) *
     (∏ τ ∈ Finset.range 62, (if τ ∈ Sf i then 1 else (3 * c + ((13 + τ : ℕ) : ℤ)) ^ 2))))

def EvP2 (c : ℤ) : ℤ := 620448401733239439360000 *
  ((∑ j ∈ aIdx, cA j * (∏ τ ∈ Finset.range 62, (if (13 + τ : ℕ) = j then 1 else (3 * c + ((13 + τ : ℕ) : ℤ)) ^ 2)))
   + (∑ k ∈ dIdx, cD k * ((3 * c + (k : ℤ)) * (3 * c + ((k + 3 : ℕ) : ℤ)) * (∏ τ ∈ Finset.range 62, (if (13 + τ : ℕ) = k ∨ (13 + τ : ℕ) = k + 3 then 1 else (3 * c + ((13 + τ : ℕ) : ℤ)) ^ 2)))))

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

set_option maxHeartbeats 0 in
lemma evc_0 : EvP1 (0:ℤ) = EvP2 (0:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_1 : EvP1 (1:ℤ) = EvP2 (1:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_2 : EvP1 (2:ℤ) = EvP2 (2:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_3 : EvP1 (3:ℤ) = EvP2 (3:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_4 : EvP1 (4:ℤ) = EvP2 (4:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_5 : EvP1 (5:ℤ) = EvP2 (5:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_6 : EvP1 (6:ℤ) = EvP2 (6:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_7 : EvP1 (7:ℤ) = EvP2 (7:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_8 : EvP1 (8:ℤ) = EvP2 (8:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_9 : EvP1 (9:ℤ) = EvP2 (9:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_10 : EvP1 (10:ℤ) = EvP2 (10:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_11 : EvP1 (11:ℤ) = EvP2 (11:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_12 : EvP1 (12:ℤ) = EvP2 (12:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_13 : EvP1 (13:ℤ) = EvP2 (13:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_14 : EvP1 (14:ℤ) = EvP2 (14:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_15 : EvP1 (15:ℤ) = EvP2 (15:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_16 : EvP1 (16:ℤ) = EvP2 (16:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_17 : EvP1 (17:ℤ) = EvP2 (17:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_18 : EvP1 (18:ℤ) = EvP2 (18:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_19 : EvP1 (19:ℤ) = EvP2 (19:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_20 : EvP1 (20:ℤ) = EvP2 (20:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_21 : EvP1 (21:ℤ) = EvP2 (21:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_22 : EvP1 (22:ℤ) = EvP2 (22:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_23 : EvP1 (23:ℤ) = EvP2 (23:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_24 : EvP1 (24:ℤ) = EvP2 (24:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_25 : EvP1 (25:ℤ) = EvP2 (25:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_26 : EvP1 (26:ℤ) = EvP2 (26:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_27 : EvP1 (27:ℤ) = EvP2 (27:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_28 : EvP1 (28:ℤ) = EvP2 (28:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_29 : EvP1 (29:ℤ) = EvP2 (29:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_30 : EvP1 (30:ℤ) = EvP2 (30:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_31 : EvP1 (31:ℤ) = EvP2 (31:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_32 : EvP1 (32:ℤ) = EvP2 (32:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_33 : EvP1 (33:ℤ) = EvP2 (33:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_34 : EvP1 (34:ℤ) = EvP2 (34:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_35 : EvP1 (35:ℤ) = EvP2 (35:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_36 : EvP1 (36:ℤ) = EvP2 (36:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_37 : EvP1 (37:ℤ) = EvP2 (37:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_38 : EvP1 (38:ℤ) = EvP2 (38:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_39 : EvP1 (39:ℤ) = EvP2 (39:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_40 : EvP1 (40:ℤ) = EvP2 (40:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_41 : EvP1 (41:ℤ) = EvP2 (41:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_42 : EvP1 (42:ℤ) = EvP2 (42:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_43 : EvP1 (43:ℤ) = EvP2 (43:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_44 : EvP1 (44:ℤ) = EvP2 (44:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_45 : EvP1 (45:ℤ) = EvP2 (45:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_46 : EvP1 (46:ℤ) = EvP2 (46:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_47 : EvP1 (47:ℤ) = EvP2 (47:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_48 : EvP1 (48:ℤ) = EvP2 (48:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_49 : EvP1 (49:ℤ) = EvP2 (49:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_50 : EvP1 (50:ℤ) = EvP2 (50:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_51 : EvP1 (51:ℤ) = EvP2 (51:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_52 : EvP1 (52:ℤ) = EvP2 (52:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_53 : EvP1 (53:ℤ) = EvP2 (53:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_54 : EvP1 (54:ℤ) = EvP2 (54:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_55 : EvP1 (55:ℤ) = EvP2 (55:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_56 : EvP1 (56:ℤ) = EvP2 (56:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_57 : EvP1 (57:ℤ) = EvP2 (57:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_58 : EvP1 (58:ℤ) = EvP2 (58:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_59 : EvP1 (59:ℤ) = EvP2 (59:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_60 : EvP1 (60:ℤ) = EvP2 (60:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_61 : EvP1 (61:ℤ) = EvP2 (61:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_62 : EvP1 (62:ℤ) = EvP2 (62:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_63 : EvP1 (63:ℤ) = EvP2 (63:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_64 : EvP1 (64:ℤ) = EvP2 (64:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_65 : EvP1 (65:ℤ) = EvP2 (65:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_66 : EvP1 (66:ℤ) = EvP2 (66:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_67 : EvP1 (67:ℤ) = EvP2 (67:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_68 : EvP1 (68:ℤ) = EvP2 (68:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_69 : EvP1 (69:ℤ) = EvP2 (69:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_70 : EvP1 (70:ℤ) = EvP2 (70:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_71 : EvP1 (71:ℤ) = EvP2 (71:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_72 : EvP1 (72:ℤ) = EvP2 (72:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_73 : EvP1 (73:ℤ) = EvP2 (73:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_74 : EvP1 (74:ℤ) = EvP2 (74:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_75 : EvP1 (75:ℤ) = EvP2 (75:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_76 : EvP1 (76:ℤ) = EvP2 (76:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_77 : EvP1 (77:ℤ) = EvP2 (77:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_78 : EvP1 (78:ℤ) = EvP2 (78:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_79 : EvP1 (79:ℤ) = EvP2 (79:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_80 : EvP1 (80:ℤ) = EvP2 (80:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_81 : EvP1 (81:ℤ) = EvP2 (81:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_82 : EvP1 (82:ℤ) = EvP2 (82:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_83 : EvP1 (83:ℤ) = EvP2 (83:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_84 : EvP1 (84:ℤ) = EvP2 (84:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_85 : EvP1 (85:ℤ) = EvP2 (85:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_86 : EvP1 (86:ℤ) = EvP2 (86:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_87 : EvP1 (87:ℤ) = EvP2 (87:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_88 : EvP1 (88:ℤ) = EvP2 (88:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_89 : EvP1 (89:ℤ) = EvP2 (89:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_90 : EvP1 (90:ℤ) = EvP2 (90:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_91 : EvP1 (91:ℤ) = EvP2 (91:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_92 : EvP1 (92:ℤ) = EvP2 (92:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_93 : EvP1 (93:ℤ) = EvP2 (93:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_94 : EvP1 (94:ℤ) = EvP2 (94:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_95 : EvP1 (95:ℤ) = EvP2 (95:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_96 : EvP1 (96:ℤ) = EvP2 (96:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_97 : EvP1 (97:ℤ) = EvP2 (97:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_98 : EvP1 (98:ℤ) = EvP2 (98:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_99 : EvP1 (99:ℤ) = EvP2 (99:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_100 : EvP1 (100:ℤ) = EvP2 (100:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_101 : EvP1 (101:ℤ) = EvP2 (101:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_102 : EvP1 (102:ℤ) = EvP2 (102:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_103 : EvP1 (103:ℤ) = EvP2 (103:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_104 : EvP1 (104:ℤ) = EvP2 (104:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_105 : EvP1 (105:ℤ) = EvP2 (105:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_106 : EvP1 (106:ℤ) = EvP2 (106:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_107 : EvP1 (107:ℤ) = EvP2 (107:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_108 : EvP1 (108:ℤ) = EvP2 (108:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_109 : EvP1 (109:ℤ) = EvP2 (109:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_110 : EvP1 (110:ℤ) = EvP2 (110:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_111 : EvP1 (111:ℤ) = EvP2 (111:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_112 : EvP1 (112:ℤ) = EvP2 (112:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_113 : EvP1 (113:ℤ) = EvP2 (113:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_114 : EvP1 (114:ℤ) = EvP2 (114:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_115 : EvP1 (115:ℤ) = EvP2 (115:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_116 : EvP1 (116:ℤ) = EvP2 (116:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_117 : EvP1 (117:ℤ) = EvP2 (117:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_118 : EvP1 (118:ℤ) = EvP2 (118:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_119 : EvP1 (119:ℤ) = EvP2 (119:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_120 : EvP1 (120:ℤ) = EvP2 (120:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_121 : EvP1 (121:ℤ) = EvP2 (121:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_122 : EvP1 (122:ℤ) = EvP2 (122:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_123 : EvP1 (123:ℤ) = EvP2 (123:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_124 : EvP1 (124:ℤ) = EvP2 (124:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_125 : EvP1 (125:ℤ) = EvP2 (125:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_126 : EvP1 (126:ℤ) = EvP2 (126:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_127 : EvP1 (127:ℤ) = EvP2 (127:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_128 : EvP1 (128:ℤ) = EvP2 (128:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_129 : EvP1 (129:ℤ) = EvP2 (129:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_130 : EvP1 (130:ℤ) = EvP2 (130:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_131 : EvP1 (131:ℤ) = EvP2 (131:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_132 : EvP1 (132:ℤ) = EvP2 (132:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_133 : EvP1 (133:ℤ) = EvP2 (133:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_134 : EvP1 (134:ℤ) = EvP2 (134:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_135 : EvP1 (135:ℤ) = EvP2 (135:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_136 : EvP1 (136:ℤ) = EvP2 (136:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_137 : EvP1 (137:ℤ) = EvP2 (137:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_138 : EvP1 (138:ℤ) = EvP2 (138:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_139 : EvP1 (139:ℤ) = EvP2 (139:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_140 : EvP1 (140:ℤ) = EvP2 (140:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_141 : EvP1 (141:ℤ) = EvP2 (141:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_142 : EvP1 (142:ℤ) = EvP2 (142:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_143 : EvP1 (143:ℤ) = EvP2 (143:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_144 : EvP1 (144:ℤ) = EvP2 (144:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_145 : EvP1 (145:ℤ) = EvP2 (145:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_146 : EvP1 (146:ℤ) = EvP2 (146:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_147 : EvP1 (147:ℤ) = EvP2 (147:ℤ) := by decide

set_option maxHeartbeats 0 in
lemma evc_148 : EvP1 (148:ℤ) = EvP2 (148:ℤ) := by decide

noncomputable def pts : Finset ℤ := (Finset.range 149).image (fun k : ℕ => (k : ℤ))

lemma pts_card : pts.card = 149 := by
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
  · rw [pts_card]
    exact degree_bound

def Df (m : ℕ) : ℤ := (Dpol).eval (m : ℤ)
def Pf (i : ℕ) (m : ℕ) : ℤ := (Ppol i).eval (m : ℤ)
def Qf (i : ℕ) (m : ℕ) : ℤ := (Qpol i).eval (m : ℤ)
def Rf (j : ℕ) (m : ℕ) : ℤ := (Rpol j).eval (m : ℤ)
def Tf (k : ℕ) (m : ℕ) : ℤ := (Tpol k).eval (m : ℤ)

lemma Pf_pos (i m : ℕ) (hi : i < 26) : 0 < Pf i m := by
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

lemma Df_eq_Pf_sq_mul_Qf (i m : ℕ) (hi : i < 26) : Df m = (Pf i m) ^ 2 * Qf i m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_Ppol_sq_mul_Qpol i hi)
  simpa [Df, Pf, Qf, Polynomial.eval_mul, Polynomial.eval_pow] using h

lemma Df_eq_sq_mul_Rf (j m : ℕ) (h1 : 13 ≤ j) (h2 : j ≤ 74) :
    Df m = (3 * (m : ℤ) + (j : ℤ)) ^ 2 * Rf j m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_sq_mul_Rpol j h1 h2)
  simpa [Df, Rf, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

lemma Df_eq_lin_mul_Tf (k m : ℕ) (h1 : 13 ≤ k) (h2 : k ≤ 71) :
    Df m = (3 * (m : ℤ) + (k : ℤ)) * (3 * (m : ℤ) + ((k + 3 : ℕ) : ℤ)) * Tf k m := by
  have h := congrArg (Polynomial.eval (m : ℤ)) (Dpol_eq_lin_mul_Tpol k h1 h2)
  simpa [Df, Tf, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h


/-! ## real-valued definitions -/

noncomputable def cTwelvePf (i : ℕ) (m : ℕ) : ℝ := ∏ j ∈ Finset.range 13, xm m (13 + 3 * j + i)

noncomputable def Vm12 (m : ℕ) : ℝ := (282429536481 : ℝ) * (Nat.choose (m + 24) 24 : ℝ) *
  (∑ i ∈ Finset.range 26, ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
    (254561089305600 / cTwelvePf i m) ^ 2)

noncomputable def aj (j : ℕ) : ℝ := (cA j : ℝ) / (Lc : ℝ)
noncomputable def dj (k : ℕ) : ℝ := (cD k : ℝ) / (3 * (Lc : ℝ))

noncomputable def W112 (m : ℕ) : ℝ := ∑ j ∈ aIdx, aj j / (xm m j) ^ 2
noncomputable def W212 (m : ℕ) : ℝ := ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))
noncomputable def Vd12 (m : ℕ) : ℝ := W112 m + W212 m

lemma cTwelvePf_eq (i m : ℕ) : cTwelvePf i m = ((Pf i m : ℤ) : ℝ) := by
  have h : ((Pf i m : ℤ) : ℝ) = ∏ j ∈ Finset.range 13,
      ((3 : ℝ) * (m : ℝ) + ((13 + 3 * j + i : ℕ) : ℝ)) := by
    rw [Pf, Ppol, Polynomial.eval_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    ring
  rw [h, cTwelvePf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [xm_eq]

lemma eval_prodP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∏ r ∈ Finset.range 24, (Polynomial.X + C ((r : ℤ) + 1))) =
      ∏ r ∈ Finset.range 24, ((m : ℤ) + (r + 1)) := by
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

lemma eval_sumP (m : ℕ) :
    Polynomial.eval (m : ℤ) (∑ i ∈ Finset.range 26,
        C ((Lc) * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ)) * Qpol i) =
      ∑ i ∈ Finset.range 26, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ) * (Qf i m) := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.eval_mul, Polynomial.eval_C, Qf]

lemma eval_P1_int (m : ℕ) :
    P1.eval (m : ℤ) = (282429536481 * 254561089305600 ^ 2) *
      (∏ r ∈ Finset.range 24, ((m : ℤ) + (r + 1))) *
      (∑ i ∈ Finset.range 26, (Lc) * (-1 : ℤ) ^ i * (Nat.choose 25 i : ℤ) * (Qf i m)) := by
  rw [P1, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, eval_prodP m, eval_sumP m]
  ring

lemma eval_P1 (m : ℕ) :
    ((P1.eval (m : ℤ) : ℤ) : ℝ) = (282429536481 : ℝ) * (254561089305600 : ℝ) ^ 2 *
      (∏ r ∈ Finset.range 24, ((m : ℝ) + (r + 1))) *
      (∑ i ∈ Finset.range 26, (Lc : ℝ) * (-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ) * ((Qf i m : ℤ) : ℝ)) := by
  rw [eval_P1_int m]
  push_cast
  ring

lemma eval_P2_int (m : ℕ) :
    P2.eval (m : ℤ) = 620448401733239439360000 *
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
    ((P2.eval (m : ℤ) : ℤ) : ℝ) = (620448401733239439360000 : ℝ) *
      ((∑ j ∈ aIdx, (cA j : ℝ) * ((Rf j m : ℤ) : ℝ)) +
        (∑ k ∈ dIdx, (cD k : ℝ) * ((Tf k m : ℤ) : ℝ))) := by
  rw [eval_P2_int m]
  push_cast
  ring


/-! ## index bounds -/

lemma aIdx_bounds (j : ℕ) (hj : j ∈ aIdx) : 13 ≤ j ∧ j ≤ 74 := by
  simp only [aIdx, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

lemma dIdx_bounds (k : ℕ) (hk : k ∈ dIdx) : 13 ≤ k ∧ k ≤ 71 := by
  simp only [dIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  omega


/-! ## the factorial identity -/

lemma choose_fact_nat (m : ℕ) :
    (m + 24).choose 24 * (24 !) = ∏ r ∈ Finset.range 24, (m + r + 1) := by
  have h2 : (m + 1).ascFactorial 24 = 24 ! * (m + 24).choose 24 := by
    simpa using Nat.ascFactorial_eq_factorial_mul_choose m 24
  have h1 : (m + 1).ascFactorial 24 = ∏ i ∈ Finset.range 24, (m + 1 + i) :=
    Nat.ascFactorial_eq_prod_range (m + 1) 24
  rw [h2, Nat.mul_comm] at h1
  rw [h1]
  apply Finset.prod_congr rfl
  intro r hr
  omega

lemma choose_fact (m : ℕ) :
    (Nat.choose (m + 24) 24 : ℝ) * 620448401733239439360000 =
      ∏ r ∈ Finset.range 24, ((m : ℝ) + (r + 1)) := by
  have h : ((m + 24).choose 24 : ℝ) * ((24 ! : ℕ) : ℝ) =
      ((∏ r ∈ Finset.range 24, (m + r + 1) : ℕ) : ℝ) := by
    exact_mod_cast choose_fact_nat m
  have h24 : ((24 ! : ℕ) : ℝ) = 620448401733239439360000 := by norm_num
  rw [h24] at h
  rw [h]
  push_cast
  apply Finset.prod_congr rfl
  intro r hr
  ring

/-! ## the two clearing identities -/

lemma clear_left (m : ℕ) :
    Vm12 m * ((Df m : ℤ) : ℝ) * 620448401733239439360000 * (Lc : ℝ) =
      ((P1.eval (m : ℤ) : ℤ) : ℝ) := by
  have hgoal : Vm12 m * ((Df m : ℤ) : ℝ) * 620448401733239439360000 * (Lc : ℝ) =
      (282429536481 : ℝ) * ((Nat.choose (m + 24) 24 : ℝ) * 620448401733239439360000) *
        ((∑ i ∈ Finset.range 26, ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
            (254561089305600 / cTwelvePf i m) ^ 2) * ((Df m : ℤ) : ℝ)) * (Lc : ℝ) := by
    rw [Vm12]
    ring
  have hsum : (∑ i ∈ Finset.range 26, ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
        (254561089305600 / cTwelvePf i m) ^ 2) * ((Df m : ℤ) : ℝ) =
      (254561089305600 : ℝ) ^ 2 * (∑ i ∈ Finset.range 26,
        ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cTwelvePf_eq i m]
    have hD : ((Df m : ℤ) : ℝ) = ((((Pf i m : ℤ)) : ℝ)) ^ 2 * ((Qf i m : ℤ) : ℝ) := by
      rw [Df_eq_Pf_sq_mul_Qf i m hi]
      simp only [Int.cast_mul, Int.cast_pow]
    rw [hD]
    have hne : (((Pf i m : ℤ)) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Pf_pos i m hi))
    field_simp
    try ring
  have hLc2 : ((254561089305600 : ℝ) ^ 2 * (∑ i ∈ Finset.range 26,
        ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ) =
      (254561089305600 : ℝ) ^ 2 * (∑ i ∈ Finset.range 26,
        (Lc : ℝ) * ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ)) := by
    rw [show ((254561089305600 : ℝ) ^ 2 * (∑ i ∈ Finset.range 26,
          ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
        = (254561089305600 : ℝ) ^ 2 * ((Lc : ℝ) * (∑ i ∈ Finset.range 26,
          ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) by ring]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hgoal, choose_fact m, hsum, eval_P1 m]
  rw [show (282429536481 : ℝ) * (∏ r ∈ Finset.range 24, ((m : ℝ) + (r + 1))) *
        ((254561089305600 : ℝ) ^ 2 * (∑ i ∈ Finset.range 26,
          ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)
      = (282429536481 : ℝ) * (∏ r ∈ Finset.range 24, ((m : ℝ) + (r + 1))) *
        (((254561089305600 : ℝ) ^ 2 * (∑ i ∈ Finset.range 26,
          ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) * ((Qf i m : ℤ) : ℝ))) * (Lc : ℝ)) by ring]
  rw [hLc2]
  ring


lemma clear_right (m : ℕ) :
    Vd12 m * ((Df m : ℤ) : ℝ) * 620448401733239439360000 * (Lc : ℝ) =
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
  rw [eval_P2 m, Vd12]
  rw [show (W112 m + W212 m) * ((Df m : ℤ) : ℝ) * 620448401733239439360000 * (Lc : ℝ) =
      ((∑ j ∈ aIdx, aj j / (xm m j) ^ 2) * ((Df m : ℤ) : ℝ) * (Lc : ℝ) +
        (∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) * ((Df m : ℤ) : ℝ) * (Lc : ℝ)) *
        620448401733239439360000 by
    rw [W112, W212]
    ring]
  rw [hW1, hW2]
  ring


theorem vm12_decomp (m : ℕ) : Vm12 m = Vd12 m := by
  have h1 := clear_left m
  have h2 := clear_right m
  have hP : ((P1.eval (m : ℤ) : ℤ) : ℝ) = ((P2.eval (m : ℤ) : ℤ) : ℝ) := by rw [poly_eq]
  have hDf : ((Df m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Df_pos m))
  have hFT : (620448401733239439360000 : ℝ) ≠ 0 := by norm_num
  have hLc : (Lc : ℝ) ≠ 0 := by norm_num [Lc]
  have h := h1.trans (hP.trans h2.symm)
  have h' : (Vm12 m * ((Df m : ℤ) : ℝ)) * 620448401733239439360000 =
      (Vd12 m * ((Df m : ℤ) : ℝ)) * 620448401733239439360000 := mul_right_cancel₀ hLc h
  have h'' : Vm12 m * ((Df m : ℤ) : ℝ) = Vd12 m * ((Df m : ℤ) : ℝ) := mul_right_cancel₀ hFT h'
  exact mul_right_cancel₀ hDf h''


lemma denom_statement12 (m : ℕ) (i : ℕ) :
    (((((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ))))
      = cTwelvePf i m := by
  rw [cTwelvePf]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  simp only [xm_eq]
  push_cast
  ring

lemma inner_sum_statement12 (m : ℕ) :
    (∑ i ∈ Finset.range 26,
      ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
        (254561089305600 / (((((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ))))) ^ 2)
    = (∑ i ∈ Finset.range 26,
      ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
        (254561089305600 / cTwelvePf i m) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [denom_statement12 m i]

lemma vm12_eq_statement (m : ℕ) :
    (282429536481 : ℝ) * (Nat.choose (m + 24) 24 : ℝ) *
      (∑ i ∈ Finset.range 26,
        ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
          (254561089305600 / (((((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ))))) ^ 2) =
      Vm12 m := by
  rw [Vm12, inner_sum_statement12 m]

@[simp] lemma asum0 : Asum 0 = 0 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum0 : Bsum 0 = 0 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum1 : Asum 1 = 1 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum1 : Bsum 1 = 1/4 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum2 : Asum 2 = 17/16 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum2 : Bsum 2 = 29/100 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum3 : Asum 3 = 849/784 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum3 : Bsum 3 = 489/1600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum4 : Asum 4 = 21421/19600 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum4 : Bsum 4 = 60769/193600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum5 : Asum 5 = 3639749/3312400 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum5 : Bsum 5 = 3026081/9486400 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum6 : Asum 6 = 58443009/52998400 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum6 : Bsum 6 = 884023809/2741569600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum7 : Asum 7 = 21150924649/19132422400 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum7 : Bsum 7 = 890877733/2741569600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum8 : Asum 8 = 2564044988129/2315023110400 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum8 : Bsum 8 = 474015890357/1450290318400 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum9 : Asum 9 = 64193725627641/57875577760000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum9 : Bsum 9 = 80471258049933/245099063809600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum10 : Asum 10 = 64267546517641/57875577760000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum10 : Bsum 10 = 67921427083803253/206128312663873600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum11 : Asum 11 = 61818987781213001/55618430227360000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum11 : Bsum 11 = 1089963588226225073/3298053002621977600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum12 : Asum 12 = 17879592076327397289/16073726335707040000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum12 : Bsum 12 = 1092655876391630769/3298053002621977600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum13 : Asum 13 = 24493235278827913928641/22004931353582937760000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum13 : Bsum 13 = 395273284628034202009/1190597133946533913600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum14 : Asum 14 = 24506988360923903264741/22004931353582937760000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum14 : Bsum 14 = 665644988593672027490729/2001393782164123508761600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum15 : Asum 15 = 45335426410701880074266109/40687118072774851918240000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum15 : Bsum 15 = 666678766373715479716329/2001393782164123508761600 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum16 : Asum 16 = 23992612350779488272266331661/21523485460497896664748960000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum16 : Bsum 16 = 1474694788701701618202132361/4421078864800548830854374400 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum17 : Asum 17 = 1176077259993511208946453291389/1054650787564396936572699040000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum17 : Bsum 17 = 36911580506190545943361852769/110526971620013720771359360000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum18 : Asum 18 = 1176467293568793900121221301389/1054650787564396936572699040000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum18 : Bsum 18 = 103795156613509257275674803788121/310470263280618541646748442240000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum19 : Asum 19 = 1176815938457244940430832110989/1054650787564396936572699040000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum19 : Bsum 19 = 103894158610728842269822363878121/310470263280618541646748442240000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum20 : Asum 20 = 989965866939434094136472980101749/886961312341657823657639892640000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum20 : Bsum 20 = 361966036387227718482898397101979201/1080746986479833143472331327437440000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum21 : Asum 21 = 3684549952193975922105473598851248029/3300383043223308761830078040513440000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum21 : Bsum 21 = 348119547714745795747933442446861372161/1038597854007119650876910405667379840000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum22 : Asum 22 = 58965691356366205803538476323965724089/52806128691572940189281248648215040000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum22 : Bsum 22 = 348365369692025587381277089880155426561/1038597854007119650876910405667379840000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum23 : Asum 23 = 264749794627419470792273501466930350475521/237046711696470928509683525181837314560000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum23 : Bsum 23 = 20505292938504139981959879070978858033/61093991412183508875112376803963520000 := by norm_num [Bsum, f2, xm]
@[simp] lemma asum24 : Asum 24 = 264798171507357526083806089941457256049921/237046711696470928509683525181837314560000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum24 : Bsum 24 = 103428275694411553157934862773608386864353/307974810708817068239441491468780104320000 := by norm_num [Bsum, f2, xm]


def cAval (j : ℕ) : ℝ := if j % 3 = 1 then (A - Asum (j / 3)) else (B - Bsum (j / 3))
def cDval (k : ℕ) : ℝ := 1 / xm 0 k

noncomputable def V1val12 : ℝ := ∑ j ∈ aIdx, aj j * cAval j
noncomputable def V2val12 : ℝ := ∑ k ∈ dIdx, dj k * cDval k
noncomputable def Vval12 : ℝ := V1val12 + V2val12

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

lemma hasSum_W112 : HasSum W112 V1val12 := by
  change HasSum (fun m => ∑ j ∈ aIdx, aj j / (xm m j) ^ 2) V1val12
  rw [V1val12]
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

lemma hasSum_W212 : HasSum W212 V2val12 := by
  change HasSum (fun m => ∑ k ∈ dIdx, dj k * (1 / xm m k - 1 / xm m (k + 3))) V2val12
  rw [V2val12]
  apply hasSum_finset_sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := dIdx_bounds k hk
  have hh := (CdtTwoCore.hasSum_pair k (by omega)).mul_left (dj k)
  simpa [cDval, div_eq_mul_inv, mul_comm] using hh

lemma hasSum_Vm12 : HasSum Vm12 Vval12 := by
  have hsum : HasSum (fun m => W112 m + W212 m) Vval12 := by
    simpa [Vval12] using hasSum_W112.add hasSum_W212
  refine hsum.congr_fun (fun m => ?_)
  exact vm12_decomp m



set_option maxHeartbeats 0 in
lemma tsum_Vm12 : (∑' m : ℕ, Vm12 m) = 9533639025 * A - 9533639025 * B - 1413218448827853 / 189728 := by
  have hval : Vval12 = 9533639025 * A - 9533639025 * B - 1413218448827853 / 189728 := by
    unfold Vval12 V1val12 V2val12
    simp only [cAval, cDval, aj, dj, cA, cD, Lc, aIdx, dIdx, xm_eq,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      not_false_eq_true, asum0, asum1, asum2, asum3, asum4, asum5, asum6, asum7, asum8, asum9, asum10, asum11, asum12, asum13, asum14, asum15, asum16, asum17, asum18, asum19, asum20, asum21, asum22, asum23, asum24, bsum0, bsum1, bsum2, bsum3, bsum4, bsum5, bsum6, bsum7, bsum8, bsum9, bsum10, bsum11, bsum12, bsum13, bsum14, bsum15, bsum16, bsum17, bsum18, bsum19, bsum20, bsum21, bsum22, bsum23, bsum24]
    norm_num
    ring
  rw [hasSum_Vm12.tsum_eq]
  exact hval

end CdtTwelveCore
open CdtTwelveCore

/-! ## Final assembly -/

/-- Creative-telescoping evaluation of the degree-12 `(Cintegral)` inner sum. -/
theorem sum_cintegralTwelve_core :
    (∑' m : ℕ,
        (282429536481 : ℝ) * (Nat.choose (m + 24) 24 : ℝ) *
          (∑ i ∈ Finset.range 26,
            ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
              (254561089305600 / ((((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ)))) ^ 2)) =
      9533639025 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 1413218448827853 / 189728 := by
  have hMain := tsum_Vm12
  have hL : (∑' m : ℕ, Vm12 m) =
      (∑' m : ℕ,
        (282429536481 : ℝ) * (Nat.choose (m + 24) 24 : ℝ) *
          (∑ i ∈ Finset.range 26,
            ((-1 : ℝ) ^ i * (Nat.choose 25 i : ℝ)) *
              (254561089305600 / ((((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ) * ((3 * m + 40 + i : ℕ) : ℝ) * ((3 * m + 43 + i : ℕ) : ℝ) * ((3 * m + 46 + i : ℕ) : ℝ) * ((3 * m + 49 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm12_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
