import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.SGgens
import Submission.Work.SG.SGfacts
import Submission.Work.SG.imatOfList_inj
import Submission.Work.SG.sgTau_eq_data

/-!
# `RepCoh_sgTau`

The representative cocycle `sgTau k` of the `k`-th space-group representative, evaluated on the
`i`-th element `e j i` of its arithmetic class `j = sgArith k`, is the vector

  `repZ[k][i] / n`   (`n` = order of the arithmetic class),

where `repZ` is the certified table of numerators of the class.

The proof has three ingredients, all of them available in the workspace:

* **Existence.**  `Tau.wOf_spec` / `Tau.wOf_mem`: the word table of the arithmetic class
  presents the `i`-th class element as a product of the class generators, so the `ℚ`-side
  closure table `sgTable k` contains an entry whose matrix is `elems[i]`.
* **Value.**  `Tau.align_spec`: the kernel-checked alignment certificate for the certified
  integer table `TZ k` says that an entry of `TZ k` whose matrix is `elems[i]` has numerators
  `y` with `n · y = d · repZ[k][i]` (`d` = denominator of the representative).  Since the table
  is the `toPair`-image of `TZ k` (`Tau.sgTable_sub`), *every* entry of `sgTable k` with matrix
  `elems[i]` stores the translation `repZ[k][i] / n`; this is `sgTau_entry_val` below.
* **Assembly.**  `sgTau` reads off the *first* entry of `sgTable k` whose matrix is `elems[i]`;
  by the value lemma any such entry gives the same translation, so the value is
  `repZ[k][i] / n` provided only that such an entry exists.

Everything is phrased in the `Data` vocabulary of the certified tables and then transported to
the `RC` vocabulary of the statement.

The same identity stated in the `Data` vocabulary (`Data.repArith` / `Data.repZ` in place of
`RC.Ad` / `RC.repZvec`) is the sibling deliverable `Work.SG.sgTau_eq_data`.  The argument below
is written out in the `RC` vocabulary of the cohomology route and — apart from the certified
alignment data `Tau.align_spec` and the class-word construction `Tau.wOf_spec` / `Tau.wOf_mem`,
which are part of the shared library — carries its own value lemma and assembly, so that
`RepCoh_sgTau` does not depend on `sgTau_eq_data`.
-/

namespace Work.SG

/-- The class table `Data.repArith k` of the representative `k` is the table of its arithmetic
class `sgArith k`. -/
theorem repArith_eq_arithData (k : Fin 230) :
    Data.repArith k = Data.arithData.getD (sgArith k).val default := by
  simp only [Data.repArith, Data.repClass]
  exact congrArg (fun x => Data.arithData.getD x default) (Tau.idxCheck k).symm

/-- `sgTau` reads its value off the entry returned by `find?`. -/
theorem sgTau_of_find? {k : Fin 230} {A : IMat} {q : List ℤ × List ℚ}
    (hq : (sgTable k).find? (fun p => decide (imatOfList p.1 = A)) = some q) (c : Fin 3) :
    sgTau k A c = ((q.2.getD c.val 0 : ℚ) : ℝ) := by
  unfold sgTau
  rw [hq]
  rfl

/-- A list that has a witness for `p` has `find?` different from `none`. -/
theorem find?_ne_none_of {α : Type*} {l : List α} {p : α → Bool} (h : ∃ a ∈ l, p a = true) :
    l.find? p ≠ none := by
  intro hnone
  obtain ⟨a, ha, hpa⟩ := h
  exact List.find?_eq_none.mp hnone a ha hpa

/-- **Value of a table entry with prescribed matrix.**  Every entry of the `ℚ`-side table
`sgTable k` whose matrix is the `i`-th element of the class of `k` stores the translation
`repZ[k][i] / n`. -/
theorem sgTau_entry_val (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n)
    {p : List ℤ × List ℚ} (hp : p ∈ sgTable k)
    (hmat : imatOfList p.1 = (Data.M3.toIMat ((Data.repArith k).elems.getD i Data.M3.one))) :
    ∀ c : Fin 3, p.2.getD c.val 0 =
      (((Data.repZ.getD k []).getD i Data.V3.zero).toFun c : ℚ) /
        ((Data.repArith k).n : ℚ) := by
  intro c
  -- every table entry is the `toPair`-image of a certified integer table entry
  obtain ⟨y, hy, hyeq⟩ := Tau.sgTable_sub k p hp
  have hyTZ : y ∈ TZ k := Tau.zClose_subset_TZ k 48 y hy
  -- its matrix is prescribed, hence it is fixed by the alignment certificate
  have hy1 : y.1 = Data.M3.toList ((Data.repArith k).elems.getD i Data.M3.one) := by
    refine imatOfList_inj (Tau.tzshape k y hyTZ) (Tau.toList_length _) ?_
    have hyx : y.1 = p.1 := by rw [← hyeq]; rfl
    rw [hyx, hmat, Tau.imatOfList_toList]
  obtain ⟨hal0, hal1, hal2⟩ := Tau.align_spec k i hi y hyTZ hy1
  have hn : ((Data.repArith k).n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (Tau.kChk_npos k))
  have hd : (sgDen k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (Tau.denPos k))
  -- the stored translation is `y.2 / d`
  have hp2 : p.2.getD c.val 0 = (y.2.getD c.val 0 : ℚ) / (sgDen k : ℚ) := by
    have h1 : p.2 = y.2.map (divQ (sgDen k)) := by rw [← hyeq]; rfl
    have hd0 : divQ (sgDen k) (0 : ℤ) = 0 := by simp [divQ]
    rw [h1, ← hd0, List.getD_map, divQ]
  rw [hp2]
  -- and `y.2 / d = repZ[k][i] / n` by the three integer alignment equations
  fin_cases c
  · have hc : ((Data.repArith k).n : ℚ) * (y.2.getD 0 0 : ℚ) =
        (sgDen k : ℚ) * (((Data.repZ.getD k []).getD i Data.V3.zero).x : ℚ) := by
      exact_mod_cast hal0
    have hq : (y.2.getD 0 0 : ℚ) / (sgDen k : ℚ) =
        (((Data.repZ.getD k []).getD i Data.V3.zero).x : ℚ) /
          ((Data.repArith k).n : ℚ) := by
      rw [div_eq_div_iff hd hn]; linarith
    simpa [Data.V3.toFun] using hq
  · have hc : ((Data.repArith k).n : ℚ) * (y.2.getD 1 0 : ℚ) =
        (sgDen k : ℚ) * (((Data.repZ.getD k []).getD i Data.V3.zero).y : ℚ) := by
      exact_mod_cast hal1
    have hq : (y.2.getD 1 0 : ℚ) / (sgDen k : ℚ) =
        (((Data.repZ.getD k []).getD i Data.V3.zero).y : ℚ) /
          ((Data.repArith k).n : ℚ) := by
      rw [div_eq_div_iff hd hn]; linarith
    simpa [Data.V3.toFun] using hq
  · have hc : ((Data.repArith k).n : ℚ) * (y.2.getD 2 0 : ℚ) =
        (sgDen k : ℚ) * (((Data.repZ.getD k []).getD i Data.V3.zero).z : ℚ) := by
      exact_mod_cast hal2
    have hq : (y.2.getD 2 0 : ℚ) / (sgDen k : ℚ) =
        (((Data.repZ.getD k []).getD i Data.V3.zero).z : ℚ) /
          ((Data.repArith k).n : ℚ) := by
      rw [div_eq_div_iff hd hn]; linarith
    simpa [Data.V3.toFun] using hq

/-- The cocycle values of the `k`-th representative on its class, in the vocabulary of the
certified tables. -/
theorem sgTau_repArith (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    sgTau k ((Data.repArith k).elems.getD i Data.M3.one).toIMat =
      fun c => (((Data.repZ.getD k []).getD i Data.V3.zero).toFun c : ℝ) /
        ((Data.repArith k).n : ℝ) := by
  -- an entry of the table with matrix `elems[i]` exists: the word of `i`
  have hmem : Tau.wfold (gensQ k) (Tau.wOf k i) ∈ sgTable k := Tau.wOf_mem k i hi
  have hfst : (Tau.wfold (gensQ k) (Tau.wOf k i)).1 =
      Data.M3.toList ((Data.repArith k).elems.getD i Data.M3.one) := (Tau.wOf_spec k i hi).2.2
  have hwit : (fun p : List ℤ × List ℚ => decide (imatOfList p.1 =
      (Data.M3.toIMat ((Data.repArith k).elems.getD i Data.M3.one))))
      (Tau.wfold (gensQ k) (Tau.wOf k i)) = true := by
    rw [decide_eq_true_eq, hfst, Tau.imatOfList_toList]
  have hne : (sgTable k).find? (fun p : List ℤ × List ℚ => decide (imatOfList p.1 =
      (Data.M3.toIMat ((Data.repArith k).elems.getD i Data.M3.one)))) ≠ none :=
    find?_ne_none_of ⟨Tau.wfold (gensQ k) (Tau.wOf k i), hmem, hwit⟩
  -- the entry returned by `find?` is one of them, hence has the prescribed translation
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
  have hqmem : q ∈ sgTable k := List.mem_of_find?_eq_some hq
  have hqmat : imatOfList q.1 =
      (Data.M3.toIMat ((Data.repArith k).elems.getD i Data.M3.one)) :=
    of_decide_eq_true (List.find?_some
      (p := fun p : List ℤ × List ℚ => decide (imatOfList p.1 =
        (Data.M3.toIMat ((Data.repArith k).elems.getD i Data.M3.one))))
      (a := q) (l := sgTable k) hq)
  funext c
  rw [sgTau_of_find? hq c, sgTau_entry_val k i hi hqmem hqmat c]
  push_cast
  ring

/-- **The cocycle values of the space-group representatives are the `repZ` numerators.**
For the `i`-th element `e j i` of the arithmetic class `j` of the representative `k`
(`sgArith k = j`), the representative cocycle `sgTau k` takes the value `repZ[k][i] / n`, where
`n` is the order of the class. -/
theorem RepCoh_sgTau (j : Fin 73) (k : Fin 230) (hk : sgArith k = j) (i : ℕ)
    (hi : i < Work.SG.RC.N j) :
    sgTau k (Work.SG.RC.e j i) =
      fun c => ((Work.SG.RC.repZvec k i).toFun c : ℝ) / ((Work.SG.RC.Ad j).n : ℝ) := by
  subst hk
  have hAd : Data.repArith k = RC.Ad (sgArith k) := repArith_eq_arithData k
  simp only [RC.N, RC.e, RC.eM, RC.repZvec] at hi ⊢
  rw [← hAd] at hi ⊢
  exact sgTau_repArith k i hi

end Work.SG
