import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.Data.ArithCheck
import Submission.Work.SG.Data.SepCheck
import Submission.Work.SG.sgTauDefs
import Submission.Work.SG.SGdata
import Submission.Work.SG.imatOfList_inj
import Submission.Work.SG.sgMulPair_toPair
import Submission.Work.SG.Tau.zClose_map_toPair
import Submission.Work.SG.Tau.wfold_mem
import Submission.Work.SG.Tau.m9mul_foldl_start

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# `sgTau_eq_data`: the representative cocycles are the `repZ` tables

`sgTau k A` is, by definition, the translation read off the `find?`-lookup of the matrix `A`
in the (`ℚ`-side) closure table `sgTable k = sgClose (gensQ k) 48 [sgOne]`, and `0` if `A`
does not occur.  The goal of this file is that on the `i`-th element of the arithmetic class of
`k` this value is `repZ[k][i] / n`, where `n` is the order of the class.

The route has four steps.

1. **Existence.**  `kChk` (kernel-checked by `decide`) unpacks the BFS structure of the class
   table `Data.repArith k`: `elems` is generated from the identity by left multiplication with
   the generators.  Reading that BFS presentation as a *sequence* of generators produces, for
   every `i < n`, a word `wOf k i` of at most `i+1` generators whose flat product is
   `elems[i]` (`wgo_spec`).  `Tau.wfold_mem` then puts the corresponding affine product into
   `sgTable k` (with the `48`-step fuel bound), and `Tau.wfst` identifies its matrix part.
2. **Uniqueness.**  `Tau.zClose_map_toPair` shows that every element of `sgTable k` is
   `toPair d` of an element of the integer mirror closure `zClose (gensZ k) d 48 [zOne]`, and
   `zClose_subset_TZ` places those in the certified table `TZ k`.  Since `TZnodup` says that a
   matrix occurs at most once in `TZ k` (`tzred`, `tzlen_le` give the range facts), the
   translation of a table entry is determined by its matrix: the kernel check `alignB` exhibits,
   for each `i < n`, an entry of `TZ k` with matrix `elems[i]` and numerators `n · num = d · z`.
3. **Assembly.**  `List.find?` on `sgTable k` therefore returns an entry whose translation is
   `repZ[k][i]/n`, and `sgTau` reads off exactly that translation.
-/

namespace Work.SG


namespace Tau



/-! ## Facts about the certified integer table `TZ` -/

/-- Elements of `arithGens` have nine entries. -/
theorem codeToList_length (c : ℕ) : (codeToList c).length = 9 := by
  simp [codeToList]

theorem tzone (k : Fin 230) : zOne ∈ TZ k := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : oneCheck k = true := by tauto
  rw [oneCheck] at h1
  exact of_decide_eq_true h1

theorem tzclo (k : Fin 230) : ∀ t ∈ TZ k, ∀ g ∈ gensZ k, zMul (sgDen k) t g ∈ TZ k := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : cloCheck k = true := by tauto
  simp only [cloCheck, List.all_eq_true] at h1
  intro t ht g hg
  exact of_decide_eq_true (h1 t ht g hg)

theorem tznodup (k : Fin 230) : ((TZ k).map (·.1)).Nodup := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : nodupCheck k = true := by tauto
  rw [nodupCheck] at h1
  exact of_decide_eq_true h1

theorem tzred (k : Fin 230) : ∀ t ∈ TZ k, ∀ x ∈ t.2, 0 ≤ x ∧ x < (sgDen k : ℤ) := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : redCheck k = true := by tauto
  simp only [redCheck, List.all_eq_true] at h1
  intro t ht x hx
  exact of_decide_eq_true (h1 t ht x hx)

theorem tzlen : (List.finRange 230).all (fun k => decide ((TZ k).length ≤ 48)) = true := by
  decide

theorem tzlen_le (k : Fin 230) : (TZ k).length ≤ 48 :=
  of_decide_eq_true (List.all_eq_true.mp tzlen k (List.mem_finRange k))

/-- `zClose` built from the certified data is contained in the certified table. -/
theorem zClose_subset_TZ (k : Fin 230) (m : ℕ) :
    ∀ p ∈ zClose (gensZ k) (sgDen k) m [zOne], p ∈ TZ k := by
  refine zClose_subset_of_closed (gensZ k) (sgDen k) (S := {p | p ∈ TZ k}) ?_ m [zOne] ?_
  · intro a ha g hg
    exact tzclo k a ha g hg
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact tzone k

/-! ## Kernel checks of the class tables -/

/-- Structural check for the class table of representative `k`. -/
def kChk (k : Fin 230) : Bool :=
  let D := Data.repArith k
  let gs := arithGens (sgArith k)
  decide (D.gens.map Data.M3.toList = gs) &&
  decide (Data.M3.toList (D.elems.getD 0 Data.M3.one) = one9) &&
  decide (D.elems.length = D.n) &&
  decide (D.n ≤ 48) &&
  decide (0 < D.n) &&
  (List.range (D.n - 1)).all (fun i => decide ((D.par.getD i (0,0)).1 < gs.length)) &&
  (List.range (D.n - 1)).all (fun i => decide ((D.par.getD i (0,0)).2 ≤ i)) &&
  (List.range (D.n - 1)).all (fun i => decide (
    Data.M3.toList (D.elems.getD (i+1) Data.M3.one) =
      m9mul (gs.getD ((D.par.getD i (0,0)).1) one9)
            (Data.M3.toList (D.elems.getD ((D.par.getD i (0,0)).2) Data.M3.one))))

theorem kChk_true : (List.finRange 230).all kChk = true := by decide

theorem kChk_eq (k : Fin 230) : kChk k = true :=
  List.all_eq_true.mp kChk_true k (List.mem_finRange k)

theorem kChk_gens (k : Fin 230) :
    (Data.repArith k).gens.map Data.M3.toList = arithGens (sgArith k) := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true (by tauto)

theorem kChk_one (k : Fin 230) :
    Data.M3.toList ((Data.repArith k).elems.getD 0 Data.M3.one) = one9 := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true (by tauto)

theorem kChk_elen (k : Fin 230) : (Data.repArith k).elems.length = (Data.repArith k).n := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true (by tauto)

theorem kChk_n48 (k : Fin 230) : (Data.repArith k).n ≤ 48 := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true (by tauto)

theorem kChk_npos (k : Fin 230) : 0 < (Data.repArith k).n := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true (by tauto)

theorem kChk_par1 (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n - 1) :
    ((Data.repArith k).par.getD i (0,0)).1 < (arithGens (sgArith k)).length := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : ((List.range ((Data.repArith k).n - 1)).all (fun i => decide
      (((Data.repArith k).par.getD i (0,0)).1 < (arithGens (sgArith k)).length))) = true := by
    tauto
  exact of_decide_eq_true (List.all_eq_true.mp h1 i (List.mem_range.mpr hi))

theorem kChk_par2 (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n - 1) :
    ((Data.repArith k).par.getD i (0,0)).2 ≤ i := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : ((List.range ((Data.repArith k).n - 1)).all (fun i => decide
      (((Data.repArith k).par.getD i (0,0)).2 ≤ i))) = true := by
    tauto
  exact of_decide_eq_true (List.all_eq_true.mp h1 i (List.mem_range.mpr hi))

theorem kChk_par3 (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n - 1) :
    Data.M3.toList ((Data.repArith k).elems.getD (i+1) Data.M3.one) =
      m9mul ((arithGens (sgArith k)).getD (((Data.repArith k).par.getD i (0,0)).1) one9)
            (Data.M3.toList ((Data.repArith k).elems.getD (((Data.repArith k).par.getD i (0,0)).2) Data.M3.one)) := by
  have h := kChk_eq k
  simp only [kChk, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : ((List.range ((Data.repArith k).n - 1)).all (fun i => decide (
      Data.M3.toList ((Data.repArith k).elems.getD (i+1) Data.M3.one) =
        m9mul ((arithGens (sgArith k)).getD (((Data.repArith k).par.getD i (0,0)).1) one9)
              (Data.M3.toList ((Data.repArith k).elems.getD
                (((Data.repArith k).par.getD i (0,0)).2) Data.M3.one))))) = true := by
    tauto
  exact of_decide_eq_true (List.all_eq_true.mp h1 i (List.mem_range.mpr hi))

theorem arithGens_len (j : Fin 73) (a : ℕ) (ha : a < (arithGens j).length) :
    ((arithGens j).getD a one9).length = 9 := by
  rw [List.getD_eq_getElem (l := arithGens j) (d := one9) ha]
  simp only [arithGens, List.getElem_map]
  exact codeToList_length _

/-! ## The word attached to each class element -/

/-- `WProp D gs j w` says that `w` is a valid generator word whose flat product is the `j`-th
element of the class table of `D`. -/
def WProp (D : Data.ArithData) (gs : List (List ℤ)) (j : ℕ) (w : List ℕ) : Prop :=
  (∀ a ∈ w, a < gs.length) ∧ w.length ≤ j + 1 ∧
    wflatM gs w = Data.M3.toList (D.elems.getD j Data.M3.one)

/-- Append the word of the next class element. -/
def wstep (D : Data.ArithData) (idx : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc ++ [(D.par.getD idx (0,0)).1 :: acc.getD (D.par.getD idx (0,0)).2 []]

/-- The BFS word table of a class table. -/
def wgo (D : Data.ArithData) : ℕ → ℕ → List (List ℕ) → List (List ℕ)
  | 0, _, acc => acc
  | (m+1), idx, acc => wgo D m (idx+1) (wstep D idx acc)

theorem getD_wstep_lt (D : Data.ArithData) (idx : ℕ) (acc : List (List ℕ)) {j : ℕ}
    (h : j < acc.length) :
    (wstep D idx acc).getD j [] = acc.getD j [] := by
  have h1 : wstep D idx acc
      = acc ++ [(D.par.getD idx (0,0)).1 :: acc.getD (D.par.getD idx (0,0)).2 []] := rfl
  rw [h1]
  exact List.getD_append (l := acc)
    (l' := [(D.par.getD idx (0,0)).1 :: acc.getD (D.par.getD idx (0,0)).2 []]) (d := [])
    (n := j) h

theorem getD_wstep_ge (D : Data.ArithData) (idx : ℕ) (acc : List (List ℕ)) :
    (wstep D idx acc).getD acc.length [] =
      (D.par.getD idx (0,0)).1 :: acc.getD (D.par.getD idx (0,0)).2 [] := by
  have h1 : wstep D idx acc
      = acc ++ [(D.par.getD idx (0,0)).1 :: acc.getD (D.par.getD idx (0,0)).2 []] := rfl
  rw [h1, List.getD_append_right (l := acc)
    (l' := [(D.par.getD idx (0,0)).1 :: acc.getD (D.par.getD idx (0,0)).2 []]) (d := [])
    (n := acc.length) (Nat.le_refl _), Nat.sub_self]
  rfl

theorem wstep_length (D : Data.ArithData) (idx : ℕ) {acc : List (List ℕ)}
    (hlen : acc.length = idx + 1) : (wstep D idx acc).length = (idx + 1) + 1 := by
  simp only [wstep, List.length_append, List.length_cons, List.length_nil, hlen]

theorem wstep_spec (D : Data.ArithData) (gs : List (List ℤ))
    (hpar1 : ∀ i, i < D.n - 1 → (D.par.getD i (0,0)).1 < gs.length)
    (hpar2 : ∀ i, i < D.n - 1 → (D.par.getD i (0,0)).2 ≤ i)
    (hpar3 : ∀ i, i < D.n - 1 → Data.M3.toList (D.elems.getD (i+1) Data.M3.one) =
      m9mul (gs.getD ((D.par.getD i (0,0)).1) one9)
            (Data.M3.toList (D.elems.getD ((D.par.getD i (0,0)).2) Data.M3.one)))
    (h9 : ∀ a, a < gs.length → (gs.getD a one9).length = 9)
    {idx : ℕ} {acc : List (List ℕ)} (hlen : acc.length = idx + 1)
    (hidx : idx < D.n - 1)
    (hacc : ∀ j < acc.length, WProp D gs j (acc.getD j [])) :
    (wstep D idx acc).length = (idx + 1) + 1 ∧
      ∀ j < (wstep D idx acc).length, WProp D gs j ((wstep D idx acc).getD j []) := by
  have hp1 : (D.par.getD idx (0,0)).1 < gs.length := hpar1 idx hidx
  have hp2 : (D.par.getD idx (0,0)).2 ≤ idx := hpar2 idx hidx
  have hl : (D.par.getD idx (0,0)).2 < acc.length := by omega
  have hwp : WProp D gs ((D.par.getD idx (0,0)).2) (acc.getD (D.par.getD idx (0,0)).2 []) :=
    hacc _ hl
  constructor
  · exact wstep_length D idx hlen
  · intro j hj
    rw [wstep_length D idx hlen] at hj
    rcases Nat.lt_or_ge j acc.length with hlt | hge
    · rw [getD_wstep_lt D idx acc hlt]
      exact hacc j hlt
    · have hj' : j = acc.length := by omega
      subst hj'
      rw [getD_wstep_ge]
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hp1
        · exact hwp.1 a ha'
      · have h2 : (acc.getD (D.par.getD idx (0,0)).2 []).length ≤
            (D.par.getD idx (0,0)).2 + 1 := hwp.2.1
        simp only [List.length_cons]
        omega
      · have h4 : wflatM gs (acc.getD (D.par.getD idx (0,0)).2 []) =
            Data.M3.toList (D.elems.getD ((D.par.getD idx (0,0)).2) Data.M3.one) := hwp.2.2
        have h6 : (gs.getD ((D.par.getD idx (0,0)).1) one9).length = 9 := h9 _ hp1
        rw [wflatM, List.foldl_cons, m9mul_one9_left h6]
        rw [m9mul_foldl_start gs (acc.getD (D.par.getD idx (0,0)).2 []) h6, h4]
        rw [hlen]
        exact (hpar3 idx hidx).symm

theorem wgo_spec (D : Data.ArithData) (gs : List (List ℤ))
    (hpar1 : ∀ i, i < D.n - 1 → (D.par.getD i (0,0)).1 < gs.length)
    (hpar2 : ∀ i, i < D.n - 1 → (D.par.getD i (0,0)).2 ≤ i)
    (hpar3 : ∀ i, i < D.n - 1 → Data.M3.toList (D.elems.getD (i+1) Data.M3.one) =
      m9mul (gs.getD ((D.par.getD i (0,0)).1) one9)
            (Data.M3.toList (D.elems.getD ((D.par.getD i (0,0)).2) Data.M3.one)))
    (h9 : ∀ a, a < gs.length → (gs.getD a one9).length = 9) :
    ∀ (m idx : ℕ) (acc : List (List ℕ)), acc.length = idx + 1 → idx + m = D.n - 1 →
      (∀ j < acc.length, WProp D gs j (acc.getD j [])) →
      (wgo D m idx acc).length = idx + m + 1 ∧
      (∀ j < (wgo D m idx acc).length, WProp D gs j ((wgo D m idx acc).getD j [])) := by
  intro m
  induction m with
  | zero =>
      intro idx acc hlen hidx hacc
      have hw : wgo D 0 idx acc = acc := rfl
      rw [hw]
      exact ⟨by omega, hacc⟩
  | succ m ih =>
      intro idx acc hlen hidx hacc
      have hidxlt : idx < D.n - 1 := by omega
      obtain ⟨hlen', hprop'⟩ := wstep_spec D gs hpar1 hpar2 hpar3 h9 hlen hidxlt hacc
      have hidx' : (idx + 1) + m = D.n - 1 := by omega
      obtain ⟨hlen2, hprop2⟩ := ih (idx+1) (wstep D idx acc) hlen' hidx' hprop'
      have hw : wgo D (m+1) idx acc = wgo D m (idx+1) (wstep D idx acc) := rfl
      rw [hw]
      exact ⟨by omega, hprop2⟩








/-! ## The `ℚ`-side generators and the certified table -/

theorem idxCheck (k : Fin 230) :
    (sgArith k).val = (sgDataList.getD k.val (0, 1, [], 0)).1 := by
  have h : (List.finRange 230).all (fun k => decide
      ((sgArith k).val = (sgDataList.getD k.val (0, 1, [], 0)).1)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h k (List.mem_finRange k))

theorem denPos (k : Fin 230) : 0 < sgDen k := by
  have h : (List.finRange 230).all (fun k => decide (0 < sgDen k)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h k (List.mem_finRange k))

theorem sgGenTrans_eq_map (k : Fin 230) :
    sgGenTrans k = (sgGenTransZ k).map (toPairL (sgDen k)) := by
  simp only [sgGenTrans, sgGenTransZ, sgDen]
  rw [List.map_map]
  apply List.map_congr_left
  intro g _
  simp only [Function.comp_apply, toPairL, List.map_map]
  apply List.map_congr_left
  intro i _
  rfl

theorem sgGenTrans_length (k : Fin 230) :
    (sgGenTrans k).length = (arithGens (sgArith k)).length := by
  have hidx := idxCheck k
  simp only [sgGenTrans, arithGens, List.length_map, List.length_range, hidx]

theorem zip_map_snd (l m : List (List ℤ)) (f : List ℤ → List ℚ) :
    (l.zip m).map (fun p => (p.1, f p.2)) = l.zip (m.map f) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => cases m with
    | nil => simp
    | cons b m => simp [ih m]

theorem gensQ_eq_gensZ_map (k : Fin 230) :
    gensQ k = (gensZ k).map (toPair (sgDen k)) := by
  have h := sgGenTrans_eq_map k
  simp only [gensQ, gensZ]
  rw [h, ← zip_map_snd (arithGens (sgArith k)) (sgGenTransZ k) (toPairL (sgDen k))]
  apply List.map_congr_left
  intro p _
  rfl

theorem sgTable_sub (k : Fin 230) :
    ∀ p ∈ sgTable k, ∃ y ∈ zClose (gensZ k) (sgDen k) 48 [zOne], toPair (sgDen k) y = p := by
  have hg : sgClose (gensQ k) 48 [sgOne]
      = sgClose ((gensZ k).map (toPair (sgDen k))) 48 ([zOne].map (toPair (sgDen k))) := by
    rw [gensQ_eq_gensZ_map k]
    congr 1
    simp only [List.map_cons, List.map_nil, toPair_zOne]
  intro p hp
  rw [sgTable_eq k, hg] at hp
  exact zClose_map_toPair (sgDen k) (gensZ k) [zOne] 48 p hp

/-! ## The alignment certificate -/

/-- For every `i`, every entry of the certified table whose matrix is the `i`-th element of the
class has numerators `num` with `n · num = d · repZ[k][i]` (coordinatewise). -/
def alignB (k : Fin 230) (i : ℕ) : Bool :=
  let D := Data.repArith k
  let z := (Data.repZ.getD k []).getD i Data.V3.zero
  let n : ℤ := (D.n : ℤ)
  let d : ℤ := (sgDen k : ℤ)
  (TZ k).all fun y => decide (y.1 = Data.M3.toList (D.elems.getD i Data.M3.one) →
    (n * y.2.getD 0 0 = d * z.x ∧ n * y.2.getD 1 0 = d * z.y ∧ n * y.2.getD 2 0 = d * z.z))

theorem alignB_true : (List.finRange 230).all (fun k =>
    (List.range (Data.repArith k).n).all (alignB k)) = true := by decide

theorem align_spec (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    ∀ y ∈ TZ k, y.1 = Data.M3.toList ((Data.repArith k).elems.getD i Data.M3.one) →
      (Data.repArith k).n * y.2.getD 0 0
          = (sgDen k : ℤ) * ((Data.repZ.getD k []).getD i Data.V3.zero).x ∧
      (Data.repArith k).n * y.2.getD 1 0
          = (sgDen k : ℤ) * ((Data.repZ.getD k []).getD i Data.V3.zero).y ∧
      (Data.repArith k).n * y.2.getD 2 0
          = (sgDen k : ℤ) * ((Data.repZ.getD k []).getD i Data.V3.zero).z := by
  have h : alignB k i = true :=
    List.all_eq_true.mp (List.all_eq_true.mp alignB_true k (List.mem_finRange k))
      i (List.mem_range.mpr hi)
  simp only [alignB] at h
  rw [List.all_eq_true] at h
  intro y hy hmat
  exact of_decide_eq_true (h y hy) hmat

theorem imatOfList_toList (A : Data.M3) : imatOfList (Data.M3.toList A) = A.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toList_length (A : Data.M3) : (Data.M3.toList A).length = 9 := rfl


/-! ## The word certificate -/

theorem tzshape (k : Fin 230) : ∀ t ∈ TZ k, t.1.length = 9 := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  have h1 : lenCheck k = true := by tauto
  simp only [lenCheck, List.all_eq_true] at h1
  intro t ht
  exact (of_decide_eq_true (h1 t ht)).1

theorem map_fst_zip_take (l : List (List ℤ)) (m : List (List ℚ)) :
    (l.zip m).map Prod.fst = l.take m.length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => cases m with
    | nil => simp
    | cons b m => simp [ih m]

theorem gensQ_map_fst (k : Fin 230) :
    (gensQ k).map (·.1) = arithGens (sgArith k) := by
  rw [show gensQ k = List.zip (arithGens (sgArith k)) (sgGenTrans k) from rfl]
  rw [map_fst_zip_take]
  exact List.take_of_length_le (le_of_eq (sgGenTrans_length k).symm)

theorem gensQ_getD_fst (k : Fin 230) (j : ℕ) :
    ((gensQ k).getD j sgOne).1 = (arithGens (sgArith k)).getD j one9 := by
  rw [← gensQ_map_fst k]
  exact (List.getD_map (gensQ k) sgOne (n := j) Prod.fst).symm

theorem foldl_m9mul_congr {f g : ℕ → List ℤ} (w : List ℕ) (A : List ℤ)
    (h : ∀ j ∈ w, f j = g j) :
    w.foldl (fun a j => m9mul a (f j)) A = w.foldl (fun a j => m9mul a (g j)) A := by
  induction w generalizing A with
  | nil => rfl
  | cons a w ih =>
      simp only [List.foldl_cons]
      rw [ih (m9mul A (f a)) (fun j hj => h j (by simp [hj])), h a (by simp)]

theorem gensQ_length (k : Fin 230) : (gensQ k).length = (arithGens (sgArith k)).length := by
  rw [← gensQ_map_fst k, List.length_map]

/-- The word table of representative `k`. -/
def wTab (k : Fin 230) : List (List ℕ) :=
  wgo (Data.repArith k) ((Data.repArith k).n - 1) 0 [[]]

/-- The word attached to the `i`-th element of the class of `k`. -/
def wOf (k : Fin 230) (i : ℕ) : List ℕ := (wTab k).getD i []

theorem wOf_spec (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    (∀ a ∈ wOf k i, a < (arithGens (sgArith k)).length) ∧ (wOf k i).length ≤ i + 1 ∧
    (wfold (gensQ k) (wOf k i)).1 =
      Data.M3.toList ((Data.repArith k).elems.getD i Data.M3.one) := by
  have hpar1 := kChk_par1 k
  have hpar2 := kChk_par2 k
  have hpar3 := kChk_par3 k
  have h9 : ∀ a, a < (arithGens (sgArith k)).length →
      ((arithGens (sgArith k)).getD a one9).length = 9 :=
    fun a ha => arithGens_len (sgArith k) a ha
  have hinit : ∀ j < ([[]] : List (List ℕ)).length,
      WProp (Data.repArith k) (arithGens (sgArith k)) j (([[]] : List (List ℕ)).getD j []) := by
    intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    refine ⟨?_, by simp, ?_⟩
    · intro a ha
      simp at ha
    · simp only [wflatM, List.foldl_nil]
      exact (kChk_one k).symm
  obtain ⟨hlen, hprop⟩ := wgo_spec (Data.repArith k) (arithGens (sgArith k)) hpar1 hpar2 hpar3 h9
    ((Data.repArith k).n - 1) 0 [[]] (by simp) (by omega) hinit
  have hi' : i < (wTab k).length := by
    have hn := kChk_npos k
    rw [wTab, hlen]
    omega
  have hw := hprop i hi'
  refine ⟨hw.1, hw.2.1, ?_⟩
  rw [wfold_fst]
  rw [foldl_m9mul_congr (wOf k i) one9
    (f := fun j => ((gensQ k).getD j sgOne).1)
    (g := fun j => (arithGens (sgArith k)).getD j one9) (fun j _ => gensQ_getD_fst k j)]
  exact hw.2.2

theorem wOf_mem (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    wfold (gensQ k) (wOf k i) ∈ sgTable k := by
  obtain ⟨hvalid, hlen, -⟩ := wOf_spec k i hi
  have h1 : wfold (gensQ k) (wOf k i) ∈ sgClose (gensQ k) (wOf k i).length [sgOne] :=
    wfold_mem (gensQ k) (wOf k i) (fun a ha => by
      rw [gensQ_length]; exact hvalid a ha)
  have h2 : (wOf k i).length ≤ 48 := by
    have hn := kChk_n48 k
    omega
  rw [sgTable_eq k]
  exact sgClose_mono_fuel h2 h1

/-! ## The value of a table entry with a prescribed matrix -/

theorem sgTau_trans (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    ∀ p ∈ sgTable k, imatOfList p.1 = ((Data.repArith k).elems.getD i Data.M3.one).toIMat →
      ∀ c : Fin 3, p.2.getD c.val 0 =
        (((Data.repZ.getD k []).getD i Data.V3.zero).toFun c : ℚ) /
          ((Data.repArith k).n : ℚ) := by
  intro p hp hmat c
  obtain ⟨y, hy, hyeq⟩ := sgTable_sub k p hp
  have hyTZ : y ∈ TZ k := zClose_subset_TZ k 48 y hy
  have hy1 : y.1 = Data.M3.toList ((Data.repArith k).elems.getD i Data.M3.one) := by
    refine imatOfList_inj (tzshape k y hyTZ) (toList_length _) ?_
    have hyx : y.1 = p.1 := by
      rw [← hyeq]
      rfl
    rw [hyx, hmat, imatOfList_toList]
  obtain ⟨hal0, hal1, hal2⟩ := align_spec k i hi y hyTZ hy1
  have hn : ((Data.repArith k).n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (kChk_npos k))
  have hd : (sgDen k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (denPos k))
  have hq0 : (y.2.getD 0 0 : ℚ) / (sgDen k : ℚ) =
      (((Data.repZ.getD k []).getD i Data.V3.zero).x : ℚ) / ((Data.repArith k).n : ℚ) := by
    have hc : ((Data.repArith k).n : ℚ) * (y.2.getD 0 0 : ℚ) =
        (sgDen k : ℚ) * (((Data.repZ.getD k []).getD i Data.V3.zero).x : ℚ) := by
      exact_mod_cast hal0
    field_simp
    linarith [hc]
  have hq1 : (y.2.getD 1 0 : ℚ) / (sgDen k : ℚ) =
      (((Data.repZ.getD k []).getD i Data.V3.zero).y : ℚ) / ((Data.repArith k).n : ℚ) := by
    have hc : ((Data.repArith k).n : ℚ) * (y.2.getD 1 0 : ℚ) =
        (sgDen k : ℚ) * (((Data.repZ.getD k []).getD i Data.V3.zero).y : ℚ) := by
      exact_mod_cast hal1
    field_simp
    linarith [hc]
  have hq2 : (y.2.getD 2 0 : ℚ) / (sgDen k : ℚ) =
      (((Data.repZ.getD k []).getD i Data.V3.zero).z : ℚ) / ((Data.repArith k).n : ℚ) := by
    have hc : ((Data.repArith k).n : ℚ) * (y.2.getD 2 0 : ℚ) =
        (sgDen k : ℚ) * (((Data.repZ.getD k []).getD i Data.V3.zero).z : ℚ) := by
      exact_mod_cast hal2
    field_simp
    linarith [hc]
  have hp2 : p.2.getD c.val 0 = (y.2.getD c.val 0 : ℚ) / (sgDen k : ℚ) := by
    have h1 : p.2 = (y.2.map (divQ (sgDen k))) := by
      rw [← hyeq]
      rfl
    have hd0 : divQ (sgDen k) (0 : ℤ) = 0 := by simp [divQ]
    rw [h1, ← hd0, List.getD_map, divQ]
  rw [hp2]
  fin_cases c
  · simpa [Data.V3.toFun] using hq0
  · simpa [Data.V3.toFun] using hq1
  · simpa [Data.V3.toFun] using hq2

end Tau

/-- The representative cocycles are the `repZ` tables: on the `i`-th element of its class,
`sgTau k` equals `repZ[k][i] / n` (`n` = order of the class). -/
theorem sgTau_eq_data (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    sgTau k ((Data.repArith k).elems.getD i Data.M3.one).toIMat =
      fun c => (((Data.repZ.getD k []).getD i Data.V3.zero).toFun c : ℝ) / (Data.repArith k).n := by
  have hpstar : Tau.wfold (gensQ k) (Tau.wOf k i) ∈ sgTable k := Tau.wOf_mem k i hi
  have hfst : (Tau.wfold (gensQ k) (Tau.wOf k i)).1 =
      Data.M3.toList ((Data.repArith k).elems.getD i Data.M3.one) := (Tau.wOf_spec k i hi).2.2
  have hne : (sgTable k).find? (fun p : List ℤ × List ℚ => decide (imatOfList p.1 =
        ((Data.repArith k).elems.getD i Data.M3.one).toIMat)) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    refine (hnone _ hpstar) ?_
    rw [hfst, Tau.imatOfList_toList]
    simp
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
  have hqmem : q ∈ sgTable k := List.mem_of_find?_eq_some hq
  have hqmat : imatOfList q.1 = ((Data.repArith k).elems.getD i Data.M3.one).toIMat :=
    of_decide_eq_true (List.find?_some
      (p := fun p : List ℤ × List ℚ => decide (imatOfList p.1 =
        ((Data.repArith k).elems.getD i Data.M3.one).toIMat)) (a := q) (l := sgTable k) hq)
  have htrans := Tau.sgTau_trans k i hi q hqmem hqmat
  funext c
  have hval : sgTau k ((Data.repArith k).elems.getD i Data.M3.one).toIMat c =
      ((q.2.getD c.val 0 : ℚ) : ℝ) := by
    unfold sgTau
    rw [hq]
    rfl
  rw [hval, htrans c]
  push_cast
  ring

end Work.SG
