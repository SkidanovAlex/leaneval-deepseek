import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SellStabDefs
import Submission.Work.SG.Data.CohomCheck
import Submission.Work.SG.arithRep_eq_data
import Submission.Work.SG.SGprelude
import Submission.Work.SG.det9_spec

/-!
# Interface for `exists_sgRep_of_cocycle` (the cohomology certificate soundness)

This file holds the vocabulary shared between the main assembly
(`Submission/Work/SG/exists_sgRep_of_cocycle.lean`) and the delegated certificate lemmas:
the arithmetic-class table accessors `RC.e`/`RC.G`, the flat vector operations, the
"echelon lattice" vocabulary (`EchAt`, `InSpan`, `Data.reduceBl`), and the verified data facts
extracted from the kernel-checked certificates (`Data.arithData_chk`, `Data.cohomData_chk_*`).
Nothing here is `sorry`ed.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix

namespace RC

/-! ## The arithmetic-class and cohomology certificates -/

/-- The certified arithmetic-class table of class `j`. -/
abbrev Ad (j : Fin 73) : Data.ArithData := Data.arithData.getD j.val default

/-- The certified cohomology data of class `j`. -/
abbrev Cd (j : Fin 73) : Data.CohomData := Data.cohomData.getD j.val default

/-- Order of the class-`j` point group. -/
def N (j : Fin 73) : ℕ := (Ad j).n

/-- Number of generators of the class-`j` point group. -/
def KK (j : Fin 73) : ℕ := (Ad j).gens.length

/-- Dimension `3 · #generators` of the cocycle-coordinate space. -/
def N3 (j : Fin 73) : ℕ := 3 * KK j

/-- The `i`-th element of the class-`j` table (identity out of range). -/
def eM (j : Fin 73) (i : ℕ) : Data.M3 := (Ad j).elems.getD i Data.M3.one

/-- The `i`-th element of the class-`j` point group. -/
def e (j : Fin 73) (i : ℕ) : IMat := (eM j i).toIMat

/-- The `g`-th generator matrix of the class-`j` table (identity out of range). -/
def gMt (j : Fin 73) (g : ℕ) : Data.M3 := (Ad j).gens.getD g Data.M3.one

/-- The `g`-th generator of the class-`j` point group. -/
def G (j : Fin 73) (g : ℕ) : IMat := (gMt j g).toIMat

/-- The BFS parent of element `i+1`. -/
def par (j : Fin 73) (i : ℕ) : ℕ × ℕ := (Ad j).par.getD i (0, 0)

/-- The generator index of the BFS parent of element `i+1`. -/
def par1 (j : Fin 73) (i : ℕ) : ℕ := (par j i).1

/-- The element index of the BFS parent of element `i+1`. -/
def par2 (j : Fin 73) (i : ℕ) : ℕ := (par j i).2

/-- The index of `generator g · element i` in the table. -/
def mulg (j : Fin 73) (g i : ℕ) : ℕ := ((Ad j).mulGen.getD g []).getD i 0

/-- The index of `generator g` in the table. -/
def geni (j : Fin 73) (g : ℕ) : ℕ := (Ad j).genIdx.getD g 0

/-! ## Flat vector operations on `List ℤ` -/

/-- Scalar multiple of a flat vector. -/
def vz (k : ℤ) (x : List ℤ) : List ℤ := x.map (fun a => k * a)

/-- Pointwise sum of flat vectors. -/
def vadd (x y : List ℤ) : List ℤ := List.zipWith (· + ·) x y

/-- Pointwise difference of flat vectors. -/
def vsub (x y : List ℤ) : List ℤ := List.zipWith (· - ·) x y

/-- Zero vector of length `N`. -/
def vzero (N : ℕ) : List ℤ := List.replicate N 0

/-- `q`-th coordinate of the linear combination `∑ cᵢ · rowsᵢ`. -/
def linC (rows : List (List ℤ)) (cs : List ℤ) (q : ℕ) : ℤ :=
  ((List.range rows.length).map (fun c => cs.getD c 0 * (rows.getD c []).getD q 0)).sum

/-- The row part of an echelon basis with `σ`-vectors. -/
def BlR (Bl : List (List ℤ × Data.V3)) : List (List ℤ) := Bl.map (fun p => p.1)

theorem BlR_length (Bl : List (List ℤ × Data.V3)) : (BlR Bl).length = Bl.length := by
  simp [BlR]

theorem BlR_getD (Bl : List (List ℤ × Data.V3)) (c : ℕ) :
    (BlR Bl).getD c [] = (Bl.getD c ([], Data.V3.zero)).1 := by
  rcases lt_or_ge c Bl.length with hc | hc
  · rw [List.getD_eq_getElem _ _ (by rw [BlR_length]; exact hc),
      List.getD_eq_getElem _ _ hc]
    simp only [BlR, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by rw [BlR_length]; exact hc), List.getD_eq_default _ _ hc]

/-- `v` lies in the `ℤ`-span of the rows (coordinates below `N`). -/
def InSpan (rows : List (List ℤ)) (N : ℕ) (v : List ℤ) : Prop :=
  ∃ cs : List ℤ, ∀ q < N, v.getD q 0 = linC rows cs q

/-- Row `c` of an upper-echelon basis: zeros before `c`, strictly positive pivot at `c`. -/
def EchAt (c : ℕ) (row : List ℤ) : Prop := (∀ q < c, row.getD q 0 = 0) ∧ 0 < row.getD c 0

/-- The `q`-th standard basis vector of length `N`. -/
def unitv (N q : ℕ) : List ℤ := (List.range N).map (fun q' => if q' = q then (1 : ℤ) else 0)

/-- `k` times the `q`-th standard basis vector of length `N`. -/
def vunit (k : ℤ) (N q : ℕ) : List ℤ := (List.range N).map (fun q' => if q' = q then k else 0)

/-- Extract a component of an `ofFn`-`all` check. -/
theorem ofFn_all {f : Fin 73 → Bool} (h : (List.ofFn f).all id = true) (j : Fin 73) : f j = true :=
  List.all_eq_true.mp h (f j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- Blocks of three consecutive integers (mirror of `Data.blocks`). -/
def blks (l : List ℤ) : List Data.V3 := Data.blocks l

/-! ## Certified facts about the arithmetic tables -/

theorem Ad_chk (j : Fin 73) : (Ad j).chk j.val = true := by
  have h := Data.arithData_chk
  rw [List.all_eq_true] at h
  exact h j.val (List.mem_range.mpr j.isLt)

/-- Bundled contents of the arithmetic-table check, in a fixed order. -/
theorem Ad_all_facts (j : Fin 73) :
    ((Ad j).gens.map Data.M3.toList = (arithGensList.getD j.val []).map codeToList) ∧
    ((Ad j).elems.length = (Ad j).n) ∧
    ((Ad j).elems.head? = some Data.M3.one) ∧
    ((Ad j).par.length + 1 = (Ad j).n) ∧
    (∀ x, x < (Ad j).n - 1 →
      (((Ad j).par.getD x (0, 0)).1 < (Ad j).gens.length ∧ ((Ad j).par.getD x (0, 0)).2 ≤ x) ∧
      ((Ad j).elems.getD (x + 1) Data.M3.one =
        Data.M3.mul ((Ad j).gens.getD ((Ad j).par.getD x (0, 0)).1 Data.M3.one)
          ((Ad j).elems.getD ((Ad j).par.getD x (0, 0)).2 Data.M3.one))) ∧
    ((Ad j).mulGen.length = (Ad j).gens.length) ∧
    (∀ x, x < (Ad j).gens.length →
      ((Ad j).mulGen.getD x []).length = (Ad j).n ∧
      ∀ x_1, x_1 < (Ad j).n →
        (((Ad j).mulGen.getD x []).getD x_1 0 < (Ad j).n) ∧
        ((Ad j).elems.getD (((Ad j).mulGen.getD x []).getD x_1 0) Data.M3.one =
          Data.M3.mul ((Ad j).gens.getD x Data.M3.one) ((Ad j).elems.getD x_1 Data.M3.one))) ∧
    ((Ad j).genIdx.length = (Ad j).gens.length) ∧
    (∀ x, x < (Ad j).gens.length →
      ((Ad j).genIdx.getD x 0 < (Ad j).n) ∧
      ((Ad j).elems.getD ((Ad j).genIdx.getD x 0) Data.M3.one =
        (Ad j).gens.getD x Data.M3.one)) ∧
    (Ad j).elems.Nodup := by
  have h := Ad_chk j
  simp only [Data.ArithData.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩, hh⟩, hi⟩, hj⟩
  exact ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj⟩

theorem Ad_gens_eq (j : Fin 73) :
    (Ad j).gens.map Data.M3.toList = (arithGensList.getD j.val []).map codeToList :=
  (Ad_all_facts j).1

theorem Ad_elems_len (j : Fin 73) : (Ad j).elems.length = (Ad j).n := (Ad_all_facts j).2.1

theorem Ad_head (j : Fin 73) : (Ad j).elems.head? = some Data.M3.one :=
  (Ad_all_facts j).2.2.1

theorem Ad_par_len (j : Fin 73) : (Ad j).par.length + 1 = (Ad j).n :=
  (Ad_all_facts j).2.2.2.1

theorem Ad_par_rel1 (j : Fin 73) (i : ℕ) (hi : i < (Ad j).n - 1) :
    ((Ad j).par.getD i (0, 0)).1 < (Ad j).gens.length :=
  ((Ad_all_facts j).2.2.2.2.1 i hi).1.1

theorem Ad_par_rel2 (j : Fin 73) (i : ℕ) (hi : i < (Ad j).n - 1) :
    ((Ad j).par.getD i (0, 0)).2 ≤ i :=
  ((Ad_all_facts j).2.2.2.2.1 i hi).1.2

theorem Ad_par_rel3 (j : Fin 73) (i : ℕ) (hi : i < (Ad j).n - 1) :
    (Ad j).elems.getD (i + 1) Data.M3.one =
      Data.M3.mul ((Ad j).gens.getD ((Ad j).par.getD i (0, 0)).1 Data.M3.one)
        ((Ad j).elems.getD ((Ad j).par.getD i (0, 0)).2 Data.M3.one) :=
  ((Ad_all_facts j).2.2.2.2.1 i hi).2

theorem Ad_mulGen_len (j : Fin 73) : (Ad j).mulGen.length = (Ad j).gens.length :=
  (Ad_all_facts j).2.2.2.2.2.1

theorem Ad_mulGen_rowlen (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) :
    ((Ad j).mulGen.getD g []).length = (Ad j).n :=
  (((Ad_all_facts j).2.2.2.2.2.2.1 g hg).1)

theorem Ad_mulGen_bound (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length)
    (i : ℕ) (hi : i < (Ad j).n) : ((Ad j).mulGen.getD g []).getD i 0 < (Ad j).n :=
  ((((Ad_all_facts j).2.2.2.2.2.2.1 g hg).2 i hi).1)

theorem Ad_mulGen_rel (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length)
    (i : ℕ) (hi : i < (Ad j).n) :
    (Ad j).elems.getD (((Ad j).mulGen.getD g []).getD i 0) Data.M3.one =
      Data.M3.mul ((Ad j).gens.getD g Data.M3.one) ((Ad j).elems.getD i Data.M3.one) :=
  ((((Ad_all_facts j).2.2.2.2.2.2.1 g hg).2 i hi).2)

theorem Ad_genIdx_len (j : Fin 73) : (Ad j).genIdx.length = (Ad j).gens.length :=
  (Ad_all_facts j).2.2.2.2.2.2.2.1

theorem Ad_genIdx_bound (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) :
    (Ad j).genIdx.getD g 0 < (Ad j).n :=
  (((Ad_all_facts j).2.2.2.2.2.2.2.2.1 g hg).1)

theorem Ad_genIdx_rel (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) :
    (Ad j).elems.getD ((Ad j).genIdx.getD g 0) Data.M3.one =
      (Ad j).gens.getD g Data.M3.one :=
  (((Ad_all_facts j).2.2.2.2.2.2.2.2.1 g hg).2)

theorem Ad_nodup (j : Fin 73) : (Ad j).elems.Nodup := (Ad_all_facts j).2.2.2.2.2.2.2.2.2

/-! ## The point group as a finite indexed family -/

theorem par_len_eq (j : Fin 73) : (Ad j).par.length = (Ad j).n - 1 := by
  have h := Ad_par_len j; omega

theorem N_pos (j : Fin 73) : 0 < (Ad j).n := by
  rcases List.head?_eq_some_iff.mp (Ad_head j) with ⟨t, ht⟩
  rw [← Ad_elems_len j, ht]
  simp

theorem N_ne_zero (j : Fin 73) : ((Ad j).n : ℤ) ≠ 0 := by
  have h := N_pos j; omega

theorem par1_lt (j : Fin 73) (i : ℕ) (hi : i < (Ad j).par.length) :
    par1 j i < (Ad j).gens.length := by
  have h : i < (Ad j).n - 1 := by rw [← par_len_eq j]; exact hi
  exact Ad_par_rel1 j i h

theorem par2_le (j : Fin 73) (i : ℕ) (hi : i < (Ad j).par.length) : par2 j i ≤ i := by
  have h : i < (Ad j).n - 1 := by rw [← par_len_eq j]; exact hi
  exact Ad_par_rel2 j i h

theorem e_par (j : Fin 73) (i : ℕ) (hi : i < (Ad j).par.length) :
    e j (i + 1) = G j (par1 j i) * e j (par2 j i) := by
  have h : i < (Ad j).n - 1 := by rw [← par_len_eq j]; exact hi
  have h3 := Ad_par_rel3 j i h
  simp only [par1, par2, par, e, G, gMt, eM] at h3 ⊢
  rw [h3, CZ.toIMat_mul]

theorem mulg_lt (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) (i : ℕ)
    (hi : i < (Ad j).n) : mulg j g i < (Ad j).n := by
  simp only [mulg]
  exact Ad_mulGen_bound j g hg i hi

theorem e_mulGen (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) (i : ℕ)
    (hi : i < (Ad j).n) : e j (mulg j g i) = G j g * e j i := by
  have h3 := Ad_mulGen_rel j g hg i hi
  simp only [mulg, e, G, gMt, eM] at h3 ⊢
  rw [h3, CZ.toIMat_mul]

theorem geni_lt (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) : geni j g < (Ad j).n :=
  Ad_genIdx_bound j g hg

theorem e_genIdx (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) :
    e j (geni j g) = G j g := by
  have h3 := Ad_genIdx_rel j g hg
  simp only [geni, e, G, gMt, eM] at h3 ⊢
  rw [h3]

theorem e_mem (j : Fin 73) (i : ℕ) (hi : i < (Ad j).n) : e j i ∈ arithRep j := by
  rw [arithRep_eq_data]
  have hlen := Ad_elems_len j
  refine ⟨(Ad j).elems[i], List.getElem_mem _, ?_⟩
  simp only [e, eM, List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]

theorem G_mem (j : Fin 73) (g : ℕ) (hg : g < (Ad j).gens.length) : G j g ∈ arithRep j := by
  rw [← e_genIdx j g hg]
  exact e_mem j (geni j g) (geni_lt j g hg)

theorem e_inj (j : Fin 73) {i i' : ℕ} (hi : i < (Ad j).n) (hi' : i' < (Ad j).n)
    (h : e j i = e j i') : i = i' := by
  have hlen := Ad_elems_len j
  have h1 : (Ad j).elems[i] = (Ad j).elems[i'] := by
    have := h
    simp only [e, eM, List.getD_eq_getElem _ _ (by rw [hlen]; exact hi),
      List.getD_eq_getElem _ _ (by rw [hlen]; exact hi')] at this
    exact CZ.toIMat_inj this
  exact (Ad_nodup j).getElem_inj_iff.mp h1

theorem e_one (j : Fin 73) : e j 0 = 1 := by
  rcases List.head?_eq_some_iff.mp (Ad_head j) with ⟨t, ht⟩
  simp only [e, eM]
  rw [ht, List.getD_cons_zero, CZ.toIMat_one]

/-! ## Vector bridges between `Data.V3` and `Fin 3 → ℤ` -/

theorem dvd_iff_toFun (n : ℤ) (v : Data.V3) : v.dvd n = true ↔ ∀ c, (n : ℤ) ∣ v.toFun c := by
  simp only [Data.V3.dvd, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ c
    fin_cases c
    · simpa [Data.V3.toFun] using Int.dvd_iff_emod_eq_zero.mpr h1
    · simpa [Data.V3.toFun] using Int.dvd_iff_emod_eq_zero.mpr h2
    · simpa [Data.V3.toFun] using Int.dvd_iff_emod_eq_zero.mpr h3
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Int.dvd_iff_emod_eq_zero.mp (by simpa [Data.V3.toFun] using h 0)
    · exact Int.dvd_iff_emod_eq_zero.mp (by simpa [Data.V3.toFun] using h 1)
    · exact Int.dvd_iff_emod_eq_zero.mp (by simpa [Data.V3.toFun] using h 2)

theorem dvd_ofFun_iff (n : ℤ) (f : Fin 3 → ℤ) :
    (CZ.ofFun f).dvd n = true ↔ ∀ c, (n : ℤ) ∣ f c := by
  rw [dvd_iff_toFun, CZ.ofFun_toFun]

theorem toFun_inj' {v w : Data.V3} (h : v.toFun = w.toFun) : v = w := CZ.toFun_inj h

/-! ## Certified facts about the cohomology certificates -/

theorem chk_of_range' {f : ℕ → Bool} {a b j : ℕ} (h : (List.range' a b).all f = true)
    (h1 : a ≤ j) (h2 : j < a + b) : f j = true :=
  List.all_eq_true.mp h j (List.mem_range'.mpr ⟨j - a, by omega, by omega⟩)

/-- The class-`j` cohomology certificate passes its kernel check. -/
theorem Cd_chk (j : Fin 73) : (Cd j).chk j.val (Ad j) = true := by
  have key : ∀ j < 73, (Data.cohomData.getD j default).chk j
      (Data.arithData.getD j default) = true := by
    intro j hj
    by_cases h8 : j < 8
    · exact chk_of_range' Data.cohomData_chk_0 (by omega) (by omega)
    by_cases h16 : j < 16
    · exact chk_of_range' Data.cohomData_chk_8 (by omega) (by omega)
    by_cases h24 : j < 24
    · exact chk_of_range' Data.cohomData_chk_16 (by omega) (by omega)
    by_cases h32 : j < 32
    · exact chk_of_range' Data.cohomData_chk_24 (by omega) (by omega)
    by_cases h40 : j < 40
    · exact chk_of_range' Data.cohomData_chk_32 (by omega) (by omega)
    by_cases h48 : j < 48
    · exact chk_of_range' Data.cohomData_chk_40 (by omega) (by omega)
    by_cases h56 : j < 56
    · exact chk_of_range' Data.cohomData_chk_48 (by omega) (by omega)
    by_cases h64 : j < 64
    · exact chk_of_range' Data.cohomData_chk_56 (by omega) (by omega)
    by_cases h72 : j < 72
    · exact chk_of_range' Data.cohomData_chk_64 (by omega) (by omega)
    · exact chk_of_range' Data.cohomData_chk_72 (by omega) (by omega)
  exact key j.val j.isLt

/-- The `wc` combination of rows of `relRows` attached to column `c`. -/
def wcC (j : Fin 73) (c : ℕ) : List ℤ :=
  List.foldl
    (fun acc p => List.zipWith (fun a b => a + p.2 * b) acc ((Data.relRows (Ad j)).getD p.1 []))
    (List.replicate (N3 j) 0) ((Cd j).wc.getD c [])

/-- Row `c` of `Bl` (with its `σ`). -/
def BlRow (j : Fin 73) (c : ℕ) : List ℤ × Data.V3 :=
  (Cd j).Bl.getD c ([], Data.V3.zero)

/-- Bundled contents of the cohomology check. -/
theorem Cd_all_facts (j : Fin 73) :
    ((Cd j).n = (Ad j).n ∧ (Cd j).H.length = N3 j) ∧
    (∀ x, x < N3 j →
      ((((Cd j).H.getD x []).length = N3 j ∧ Data.echelonAt x ((Cd j).H.getD x []) = true) ∧
        ((Ad j).n : ℤ) % ((Cd j).H.getD x []).getD x 1 = 0) ∧
      (∀ x_1 ∈ Data.relRows (Ad j), Data.ldot x_1 ((Cd j).H.getD x []) % ((Ad j).n : ℤ) = 0)) ∧
    ((Cd j).wc.length = N3 j) ∧
    (∀ x, x < N3 j →
      (∀ x_1 < N3 j,
          (decide (x_1 ≤ x) || (wcC j x).getD x_1 0 % ((Ad j).n : ℤ) == 0) = true) ∧
      (((wcC j x).getD x 0 - (Ad j).n / ((Cd j).H.getD x []).getD x 1) %
        ((Ad j).n : ℤ) = 0)) ∧
    ((Cd j).Bl.length = N3 j) ∧
    (∀ x, x < N3 j →
      ((((BlRow j x).1.length = N3 j ∧ Data.echelonAt x (BlRow j x).1 = true) ∧
        (∀ x_1 ∈ (Ad j).gens,
          Data.V3.dvd ((Ad j).n) ((BlRow j x).2.sub (x_1.mulV (BlRow j x).2)) = true)) ∧
        (∀ x_1 ∈ List.zipWith (fun a b => (a - b) % ((Ad j).n : ℤ) == 0) (BlRow j x).1
            (Data.cobVec (Ad j) ((Ad j).n) (BlRow j x).2), id x_1 = true))) ∧
    ((Cd j).reps.head? = some (List.replicate (N3 j) 0)) ∧
    (∀ x ∈ (Cd j).reps,
      x.length = N3 j ∧ Data.reduceBl (Cd j).Bl x = x) ∧
    ((Cd j).add.length = (Cd j).reps.length) ∧
    (∀ x, x < (Cd j).reps.length →
      ∀ x_1 < N3 j,
        ((Cd j).add.getD x []).getD x_1 0 < (Cd j).reps.length ∧
        Data.reduceBl (Cd j).Bl (List.zipWith (fun x1 x2 => x1 + x2) ((Cd j).reps.getD x [])
            ((Cd j).H.getD x_1 [])) = (Cd j).reps.getD (((Cd j).add.getD x []).getD x_1 0) []) ∧
    ((Cd j).targets.length = (Cd j).reps.length) ∧
    (∀ x, x < (Cd j).reps.length →
      ((Data.repClass ((Cd j).targets.getD x default).k = j.val ∧
          ((Cd j).targets.getD x default).k < 230) ∧
        ((Cd j).targets.getD x default).U.det = 1) ∧
      Data.ConjCert.chk (Ad j) ((Cd j).reps.getD x []) ((Cd j).targets.getD x default) = true) := by
  have h := Cd_chk j
  simp only [Data.CohomData.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, N3, KK, wcC, BlRow, and_assoc] at h ⊢
  exact h

/-! ## Atomic consequences of the cohomology check -/

theorem Cd_n (j : Fin 73) : (Cd j).n = (Ad j).n := (Cd_all_facts j).1.1

theorem Cd_H_len (j : Fin 73) : (Cd j).H.length = N3 j := (Cd_all_facts j).1.2

theorem Cd_H_rowlen (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    ((Cd j).H.getD c []).length = N3 j :=
  ((Cd_all_facts j).2.1 c hc).1.1.1

theorem Cd_H_ech (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    Data.echelonAt c ((Cd j).H.getD c []) = true :=
  ((Cd_all_facts j).2.1 c hc).1.1.2

theorem Cd_H_dvd (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    ((Ad j).n : ℤ) % ((Cd j).H.getD c []).getD c 1 = 0 :=
  ((Cd_all_facts j).2.1 c hc).1.2

theorem Cd_H_ann (j : Fin 73) (c : ℕ) (hc : c < N3 j) (row : List ℤ)
    (hr : row ∈ Data.relRows (Ad j)) :
    Data.ldot row ((Cd j).H.getD c []) % ((Ad j).n : ℤ) = 0 :=
  ((Cd_all_facts j).2.1 c hc).2 row hr

theorem Cd_wc_len (j : Fin 73) : (Cd j).wc.length = N3 j := (Cd_all_facts j).2.2.1

theorem Cd_wc_hi (j : Fin 73) (c : ℕ) (hc : c < N3 j) (q : ℕ) (hq : q < N3 j)
    (h : c < q) : (wcC j c).getD q 0 % ((Ad j).n : ℤ) = 0 := by
  have h2 := ((Cd_all_facts j).2.2.2.1 c hc).1 q hq
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · rw [decide_eq_true_eq] at h2; omega
  · exact beq_iff_eq.mp h2

theorem Cd_wc_piv (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    ((wcC j c).getD c 0 - (Ad j).n / ((Cd j).H.getD c []).getD c 1) %
      ((Ad j).n : ℤ) = 0 :=
  ((Cd_all_facts j).2.2.2.1 c hc).2

theorem Cd_Bl_len (j : Fin 73) : (Cd j).Bl.length = N3 j := (Cd_all_facts j).2.2.2.2.1

theorem Cd_Bl_rowlen (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    (BlRow j c).1.length = N3 j :=
  ((Cd_all_facts j).2.2.2.2.2.1 c hc).1.1.1

theorem Cd_Bl_ech (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    Data.echelonAt c (BlRow j c).1 = true :=
  ((Cd_all_facts j).2.2.2.2.2.1 c hc).1.1.2

theorem Cd_Bl_sig (j : Fin 73) (c : ℕ) (hc : c < N3 j) (g : Data.M3)
    (hg : g ∈ (Ad j).gens) :
    Data.V3.dvd ((Ad j).n) ((BlRow j c).2.sub (g.mulV (BlRow j c).2)) = true :=
  ((Cd_all_facts j).2.2.2.2.2.1 c hc).1.2 g hg

theorem Cd_Bl_cob (j : Fin 73) (c : ℕ) (hc : c < N3 j) :
    ∀ x ∈ List.zipWith (fun a b => (a - b) % ((Ad j).n : ℤ) == 0) (BlRow j c).1
      (Data.cobVec (Ad j) ((Ad j).n) (BlRow j c).2), id x = true :=
  ((Cd_all_facts j).2.2.2.2.2.1 c hc).2

/-- Coordinate form of a `zipWith … .all id` fact. -/
theorem zipWith_coord {f : ℤ → ℤ → Bool} {l1 l2 : List ℤ}
    (h : ∀ x ∈ List.zipWith f l1 l2, id x = true) {q : ℕ} (h1 : q < l1.length)
    (h2 : q < l2.length) : f (l1.getD q 0) (l2.getD q 0) = true := by
  have hq : q < (List.zipWith f l1 l2).length := by
    rw [List.length_zipWith]; omega
  have h3 := h _ (List.getElem_mem hq)
  rw [List.getElem_zipWith] at h3
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  exact h3

theorem Cd_reps_head (j : Fin 73) :
    (Cd j).reps.head? = some (List.replicate (N3 j) 0) :=
  (Cd_all_facts j).2.2.2.2.2.2.1

theorem Cd_reps_red (j : Fin 73) (r : List ℤ) (hr : r ∈ (Cd j).reps) :
    r.length = N3 j ∧ Data.reduceBl (Cd j).Bl r = r :=
  (Cd_all_facts j).2.2.2.2.2.2.2.1 r hr

theorem Cd_add_len (j : Fin 73) : (Cd j).add.length = (Cd j).reps.length :=
  (Cd_all_facts j).2.2.2.2.2.2.2.2.1

theorem Cd_add_bound (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) (c : ℕ)
    (hc : c < N3 j) : ((Cd j).add.getD h []).getD c 0 < (Cd j).reps.length :=
  ((Cd_all_facts j).2.2.2.2.2.2.2.2.2.1 h hh c hc).1

theorem Cd_add_red (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) (c : ℕ)
    (hc : c < N3 j) :
    Data.reduceBl (Cd j).Bl
      (List.zipWith (fun x1 x2 => x1 + x2) ((Cd j).reps.getD h []) ((Cd j).H.getD c []))
      = (Cd j).reps.getD (((Cd j).add.getD h []).getD c 0) [] :=
  ((Cd_all_facts j).2.2.2.2.2.2.2.2.2.1 h hh c hc).2

theorem Cd_tgt_len (j : Fin 73) : (Cd j).targets.length = (Cd j).reps.length :=
  (Cd_all_facts j).2.2.2.2.2.2.2.2.2.2.1

theorem Cd_tgt_class (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) :
    Data.repClass ((Cd j).targets.getD h default).k = j.val :=
  ((Cd_all_facts j).2.2.2.2.2.2.2.2.2.2.2 h hh).1.1.1

theorem Cd_tgt_k (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) :
    ((Cd j).targets.getD h default).k < 230 :=
  ((Cd_all_facts j).2.2.2.2.2.2.2.2.2.2.2 h hh).1.1.2

theorem Cd_tgt_det (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) :
    ((Cd j).targets.getD h default).U.det = 1 :=
  ((Cd_all_facts j).2.2.2.2.2.2.2.2.2.2.2 h hh).1.2

theorem Cd_tgt_chk (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) :
    Data.ConjCert.chk (Ad j) ((Cd j).reps.getD h [])
      ((Cd j).targets.getD h default) = true :=
  ((Cd_all_facts j).2.2.2.2.2.2.2.2.2.2.2 h hh).2

/-! ## Extra kernel-checked certificates -/

/-- Every arithmetic generator is unimodular. -/
theorem arithGens_det_chk : (List.ofFn (fun j : Fin 73 =>
    (arithGens j).all (fun g => decide (det9 g = 1 ∨ det9 g = -1)))).all id = true := by
  decide

theorem G_det_unit (j : Fin 73) (g : ℕ) (hg : g < KK j) : IsUnit (G j g).det := by
  have hcheck := ofFn_all arithGens_det_chk j
  have hlen : (arithGens j).length = (Ad j).gens.length := by
    show ((arithGensList.getD j.val []).map codeToList).length = (Ad j).gens.length
    have h2 := congrArg List.length (Ad_gens_eq j)
    simp only [List.length_map] at h2 ⊢
    exact h2.symm
  have hg' : g < (arithGens j).length := by rw [hlen]; exact hg
  have h3 : det9 ((arithGens j).getD g []) = 1 ∨ det9 ((arithGens j).getD g []) = -1 := by
    have h4 := List.all_eq_true.mp hcheck ((arithGens j)[g]) (List.getElem_mem hg')
    rw [List.getD_eq_getElem _ _ hg']
    exact decide_eq_true_eq.mp h4
  have h5 : ((Ad j).gens.getD g Data.M3.one).toList = (arithGens j).getD g [] := by
    have hgl : g < ((Ad j).gens.map Data.M3.toList).length := by rw [List.length_map]; exact hg
    rw [show arithGens j = ((arithGensList.getD j.val []).map codeToList) from rfl, ← Ad_gens_eq j,
      List.getD_eq_getElem _ _ hg, List.getD_eq_getElem _ _ hgl, List.getElem_map]
    rfl
  have h6 : (G j g).det = det9 ((Ad j).gens.getD g Data.M3.one).toList := by
    simp only [G, gMt]
    rw [← imatOfList_toList ((Ad j).gens.getD g Data.M3.one), det9_spec]
  rw [h6, h5]
  exact Int.isUnit_iff.mpr h3

/-- `n · e_q` lies in the lattice spanned by `Bl` (for every class and every coordinate). -/
theorem Bl_nunit_chk : (List.ofFn (fun j : Fin 73 =>
    let D := Data.arithData.getD j.val default
    let C := Data.cohomData.getD j.val default
    (List.range (3 * D.gens.length)).all (fun q =>
      Data.reduceBl C.Bl
        ((List.range (3 * D.gens.length)).map fun q' => if q' = q then (D.n : ℤ) else 0)
        == List.replicate (3 * D.gens.length) 0))).all id = true := by
  decide

/-- `n · e_q ∈ span(Bl)` as a proposition. -/
theorem Bl_nunit (j : Fin 73) (q : ℕ) (hq : q < N3 j) :
    Data.reduceBl (Cd j).Bl (vunit ((Ad j).n) (N3 j) q) = vzero (N3 j) := by
  have h := ofFn_all Bl_nunit_chk j
  have h2 := List.all_eq_true.mp h q (List.mem_range.mpr hq)
  simpa [Data.reduceBl, vunit, vzero, N3, KK, Cd, Ad] using beq_iff_eq.mp h2

/-! ## The cocycle and certificate vocabulary used by the main assembly -/

/-- The generator coordinates of the cocycle `z`: block `g` is the value of `z` at the index of
generator `g`. -/
def yvec (j : Fin 73) (z : ℕ → Fin 3 → ℤ) : List ℤ :=
  Data.unblocks ((List.range (KK j)).map (fun g => CZ.ofFun (z (geni j g))))

/-- The `g`-th block of a flat vector. -/
def blk (v : List ℤ) (g : ℕ) : Data.V3 := (Data.blocks v).getD g Data.V3.zero

/-- The `wc` combination of rows of `R` attached to column `c` (length `N3`). -/
def wcComb (N3 : ℕ) (R : List (List ℤ)) (wc : List (List (ℕ × ℤ))) (c : ℕ) : List ℤ :=
  List.foldl (fun acc p => List.zipWith (fun a b => a + p.2 * b) acc (R.getD p.1 []))
    (List.replicate N3 0) (wc.getD c [])

theorem wcC_eq (j : Fin 73) (c : ℕ) :
    wcC j c = wcComb (N3 j) (Data.relRows (Ad j)) (Cd j).wc c := rfl

/-- The cocycle on `arithRep j` whose value at the `i`-th element is `z i` (and `0` off the
group). -/
noncomputable def tauOnP (j : Fin 73) (z : ℕ → Fin 3 → ℝ) : IMat → Fin 3 → ℝ :=
  fun A => if h : ∃ i, i < N j ∧ e j i = A then z h.choose else 0

theorem tauOnP_e (j : Fin 73) (z : ℕ → Fin 3 → ℝ) (i : ℕ) (hi : i < N j) :
    tauOnP j z (e j i) = z i := by
  have hmem : ∃ i', i' < N j ∧ e j i' = e j i := ⟨i, hi, rfl⟩
  have hch : Classical.choose hmem = i := by
    have h1 : Classical.choose hmem < N j := (Classical.choose_spec hmem).1
    have h2 : e j (Classical.choose hmem) = e j i := (Classical.choose_spec hmem).2
    exact e_inj j h1 hi h2
  simp only [tauOnP, dif_pos hmem, hch]

/-- The `i`-th value of the cocycle table of representative `k`. -/
def repZvec (k : Fin 230) (i : ℕ) : Data.V3 := (Data.repZ.getD k.val []).getD i Data.V3.zero

/-- The target representative attached to the `h`-th `H¹` class of class `j`. -/
noncomputable def tgtK (j : Fin 73) (h : ℕ) : Fin 230 :=
  if hh : h < (Cd j).reps.length then ⟨((Cd j).targets.getD h default).k, Cd_tgt_k j h hh⟩
  else ⟨0, by norm_num⟩

/-- The conjugating matrix of the `h`-th target certificate. -/
def Uc (j : Fin 73) (h : ℕ) : Data.M3 := ((Cd j).targets.getD h default).U

/-- The translation numerator of the `h`-th target certificate. -/
def sigc (j : Fin 73) (h : ℕ) : Data.V3 := ((Cd j).targets.getD h default).sig

/-- The image index list of the `h`-th target certificate. -/
def imgc (j : Fin 73) (h : ℕ) (i : ℕ) : ℕ := ((Cd j).targets.getD h default).img.getD i 0

/-- The source cocycle values of the `h`-th `H¹` class: `applyB` of the representative vector. -/
noncomputable def srcZ (j : Fin 73) (h : ℕ) (i : ℕ) : Fin 3 → ℝ :=
  fun c => ((Data.applyB ((Data.bmats (Ad j)).getD i []) ((Cd j).reps.getD h [])).toFun c : ℝ)
    / ((Ad j).n : ℝ)

/-- The target cocycle values of the `h`-th `H¹` class, read off the representative table. -/
noncomputable def tgtZ (j : Fin 73) (h : ℕ) (i : ℕ) : Fin 3 → ℝ :=
  fun c => ((repZvec (tgtK j h) i).toFun c : ℝ) / ((Ad j).n : ℝ)

/-- The integral model of the coboundary `s = σ/n²`: `cz σ i = (1 - e_i) σ / n`. -/
def cz (j : Fin 73) (σ : Data.V3) (i : ℕ) : Fin 3 → ℤ :=
  fun c => (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (eM j i) σ)) ((Ad j).n)).toFun c

/-- The vector needed for the `applyB` recursion of the coboundary model. -/
def czGen (j : Fin 73) (σ : Data.V3) (g : ℕ) : Fin 3 → ℤ :=
  fun c => (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (gMt j g) σ)) ((Ad j).n)).toFun c

theorem ofFun_toFun' (v : Data.V3) : CZ.ofFun (fun c => v.toFun c) = v :=
  CZ.toFun_inj (CZ.ofFun_toFun (fun c => v.toFun c))

theorem cz_geni (j : Fin 73) (σ : Data.V3) (g : ℕ) :
    CZ.ofFun (czGen j σ g) = Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (gMt j g) σ)) ((Ad j).n) :=
  ofFun_toFun' _

theorem ofFun_cz (j : Fin 73) (σ : Data.V3) (i : ℕ) :
    CZ.ofFun (cz j σ i) = Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (eM j i) σ)) ((Ad j).n) :=
  ofFun_toFun' _

theorem blocks_unblocks (l : List Data.V3) : Data.blocks (Data.unblocks l) = l := by
  induction l with
  | nil => rfl
  | cons v t ih =>
      cases v with
      | mk x y z =>
          simp only [Data.unblocks, List.flatMap_cons, Data.V3.toList, List.cons_append,
            List.nil_append, Data.blocks] at ih ⊢
          rw [ih]

theorem blocks_yvec (j : Fin 73) (z : ℕ → Fin 3 → ℤ) (g : ℕ) (hg : g < KK j) :
    blk (yvec j z) g = CZ.ofFun (z (geni j g)) := by
  rw [blk, yvec, blocks_unblocks]
  rw [List.getD_eq_getElem _ _
    (by rw [List.length_map, List.length_range]; exact hg), List.getElem_map, List.getElem_range]

/-! ## Elementary list algebra used by the assembly -/

theorem vzero_length (N : ℕ) : (vzero N).length = N := by simp [vzero]

theorem vunit_length (k : ℤ) (N q : ℕ) : (vunit k N q).length = N := by simp [vunit]

theorem vadd_getD {N : ℕ} {u v : List ℤ} (hu : u.length = N) (hv : v.length = N) (q : ℕ)
    (hq : q < N) : (vadd u v).getD q 0 = u.getD q 0 + v.getD q 0 := by
  have h1 : (vadd u v).length = N := by simp [vadd, List.length_zipWith, hu, hv]
  rw [List.getD_eq_getElem _ _ (by rw [h1]; exact hq),
    List.getD_eq_getElem _ _ (by rw [hu]; exact hq),
    List.getD_eq_getElem _ _ (by rw [hv]; exact hq)]
  simp only [vadd, List.getElem_zipWith]

theorem vsub_getD {N : ℕ} {u v : List ℤ} (hu : u.length = N) (hv : v.length = N) (q : ℕ)
    (hq : q < N) : (vsub u v).getD q 0 = u.getD q 0 - v.getD q 0 := by
  have h1 : (vsub u v).length = N := by simp [vsub, List.length_zipWith, hu, hv]
  rw [List.getD_eq_getElem _ _ (by rw [h1]; exact hq),
    List.getD_eq_getElem _ _ (by rw [hu]; exact hq),
    List.getD_eq_getElem _ _ (by rw [hv]; exact hq)]
  simp only [vsub, List.getElem_zipWith]

theorem vz_getD (k : ℤ) {N : ℕ} {u : List ℤ} (hu : u.length = N) (q : ℕ) (hq : q < N) :
    (vz k u).getD q 0 = k * u.getD q 0 := by
  have h1 : (vz k u).length = N := by simp [vz, hu]
  rw [List.getD_eq_getElem _ _ (by rw [h1]; exact hq),
    List.getD_eq_getElem _ _ (by rw [hu]; exact hq)]
  simp only [vz, List.getElem_map]

theorem linC_getD_map (H : List (List ℤ)) (t : List ℤ) (q : ℕ) :
    linC H ((List.range H.length).map (fun c => t.getD c 0)) q = linC H t q := by
  simp only [linC]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

theorem echAt_iff (c : ℕ) (row : List ℤ) : Data.echelonAt c row = true ↔ EchAt c row := by
  simp only [Data.echelonAt, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, EchAt, Bool.decide_eq_true]


/-- Membership in `arithRep j` via the certified table. -/
theorem mem_arithRep_iff (j : Fin 73) (B : IMat) :
    B ∈ arithRep j ↔ ∃ i, i < N j ∧ e j i = B := by
  constructor
  · intro hB
    rw [arithRep_eq_data] at hB
    obtain ⟨E, hE, rfl⟩ := hB
    obtain ⟨i, hi, hii⟩ := List.mem_iff_getElem.mp hE
    refine ⟨i, by rw [show N j = (Ad j).elems.length from by rw [N, Ad_elems_len]]; exact hi, ?_⟩
    simp only [e, eM, List.getD_eq_getElem _ _ hi, hii]
  · rintro ⟨i, hi, rfl⟩
    exact e_mem j i hi

/-- Sum of a constant list. -/
theorem sum_map_const (l : List ℕ) (a : ℕ) : (l.map (fun _ => a)).sum = a * l.length := by
  induction l with
  | nil => simp
  | cons x t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Length of `unblocks`. -/
theorem length_unblocks (l : List Data.V3) : (l.flatMap Data.V3.toList).length = 3 * l.length := by
  induction l with
  | nil => simp
  | cons v t ih =>
      cases v with
      | mk x y z =>
        simp only [List.flatMap_cons, Data.V3.toList, List.length_cons, List.length_nil,
          List.length_append, ih]
        omega

/-- Length of `yvec`. -/
theorem yvec_length (j : Fin 73) (z : ℕ → Fin 3 → ℤ) : (yvec j z).length = N3 j := by
  have h := length_unblocks (List.map (fun g => CZ.ofFun (z (geni j g))) (List.range (KK j)))
  simp only [yvec, Data.unblocks] at h ⊢
  rw [h, List.length_map, List.length_range]
  simp [N3, KK]

theorem yvec_len (j : Fin 73) (z : ℕ → Fin 3 → ℤ) : (yvec j z).length = 3 * KK j := by
  rw [yvec_length]; rfl


/-- The integer matrix as a real matrix. -/
def castM (A : IMat) : Matrix (Fin 3) (Fin 3) ℝ := A.map (Int.cast : ℤ → ℝ)

theorem castM_mul (A B : IMat) : castM (A * B) = castM A * castM B := by
  ext i k
  simp only [castM, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_three]
  push_cast
  ring

theorem castM_one : castM (1 : IMat) = 1 := by
  ext i k
  simp only [castM, Matrix.map_apply, Matrix.one_apply]
  split <;> simp

theorem intVec_apply (m : Fin 3 → ℤ) (c : Fin 3) : intVec m c = (m c : ℝ) := rfl

/-- `∑_{A ∈ P} τ A`, as a real vector. -/
noncomputable def sgSum (j : Fin 73) (τ : IMat → Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun c => ∑ i : Fin (N j), τ (e j i.val) c

/-- `D A = n · τ A - (Σ - A Σ)`. -/
noncomputable def Dv (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (A : IMat) : Fin 3 → ℝ :=
  fun c => (N j : ℝ) * τ A c - (sgSum j τ c - ((castM A).mulVec (sgSum j τ)) c)

theorem mulVec_Dv (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (A B : IMat) (c : Fin 3) :
    ((castM A).mulVec (Dv j τ B)) c
      = (N j : ℝ) * ((castM A).mulVec (τ B)) c - ((castM A).mulVec (sgSum j τ)) c
        + ((castM A).mulVec ((castM B).mulVec (sgSum j τ))) c := by
  have h1 : Dv j τ B
      = (N j : ℝ) • τ B - sgSum j τ + (castM B).mulVec (sgSum j τ) := by
    funext c
    simp only [Dv, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem Dv_lin (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (A B : IMat) (m : Fin 3 → ℤ)
    (hm : τ (A * B) = τ A + (castM A).mulVec (τ B) + intVec m) :
    ∀ c, Dv j τ (A * B) c
      = Dv j τ A c + ((castM A).mulVec (Dv j τ B)) c + (N j : ℝ) * m c := by
  intro c
  have h2 : ((castM (A * B)).mulVec (sgSum j τ)) c
      = ((castM A).mulVec ((castM B).mulVec (sgSum j τ))) c := by
    rw [castM_mul, ← Matrix.mulVec_mulVec]
  have hmc : τ (A * B) c = τ A c + ((castM A).mulVec (τ B)) c + m c := by
    have h := congrFun hm c
    simpa only [Pi.add_apply, intVec_apply] using h
  rw [mulVec_Dv]
  simp only [Dv]
  rw [h2, hmc]
  ring

/-- The map `i ↦ mulg j g i` is a permutation of the index set. -/
noncomputable def mulGEq (j : Fin 73) (g : ℕ) (hg : g < KK j) : Equiv.Perm (Fin (N j)) := by
  refine Equiv.ofBijective (fun i : Fin (N j) => ⟨mulg j g i.val, mulg_lt j g hg i.val i.isLt⟩)
    ⟨?_, ?_⟩
  · intro i i' h
    have h1 : mulg j g i.val = mulg j g i'.val := congrArg Fin.val h
    have h2 : e j (mulg j g i.val) = e j (mulg j g i'.val) := by rw [h1]
    rw [e_mulGen j g hg i.val i.isLt, e_mulGen j g hg i'.val i'.isLt] at h2
    have hu : IsUnit (G j g) := (Matrix.isUnit_iff_isUnit_det (G j g)).mpr (G_det_unit j g hg)
    exact Fin.ext (e_inj j i.isLt i'.isLt (IsUnit.mul_left_cancel hu h2))
  · exact Finite.injective_iff_surjective.mp (fun i i' h => by
      have h1 : mulg j g i.val = mulg j g i'.val := congrArg Fin.val h
      have h2 : e j (mulg j g i.val) = e j (mulg j g i'.val) := by rw [h1]
      rw [e_mulGen j g hg i.val i.isLt, e_mulGen j g hg i'.val i'.isLt] at h2
      have hu : IsUnit (G j g) := (Matrix.isUnit_iff_isUnit_det (G j g)).mpr (G_det_unit j g hg)
      exact Fin.ext (e_inj j i.isLt i'.isLt (IsUnit.mul_left_cancel hu h2)))

/-- Integrality of `D` at the generators. -/
theorem Dv_gen_int (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ)
    (g : ℕ) (hg : g < KK j) (c : Fin 3) :
    ∃ m : ℤ, Dv j τ (G j g) c = m := by
  have hm : ∀ i : Fin (N j), ∃ m : Fin 3 → ℤ,
      τ (G j g * e j i.val) = τ (G j g) + (castM (G j g)).mulVec (τ (e j i.val))
        + intVec m := by
    intro i
    exact hτ (G j g) (G_mem j g hg) (e j i.val) (e_mem j i.val i.isLt)
  set M : Fin (N j) → Fin 3 → ℤ := fun i => Classical.choose (hm i) with hMdef
  have hMspec : ∀ i : Fin (N j), τ (G j g * e j i.val) = τ (G j g)
      + (castM (G j g)).mulVec (τ (e j i.val)) + intVec (M i) :=
    fun i => Classical.choose_spec (hm i)
  have hsum : (∑ i : Fin (N j), τ (G j g * e j i.val) c) = sgSum j τ c := by
    have hgen : ∀ i : Fin (N j), τ (G j g * e j i.val) c = τ (e j (mulg j g i.val)) c := by
      intro i
      rw [e_mulGen j g hg i.val i.isLt]
    rw [Finset.sum_congr rfl (fun i _ => hgen i)]
    exact Equiv.sum_comp (mulGEq j g hg) (fun n : Fin (N j) => τ (e j n.val) c)
  have hsplit : (∑ i : Fin (N j), τ (G j g * e j i.val) c)
      = ∑ i : Fin (N j), (τ (G j g) c + ((castM (G j g)).mulVec (τ (e j i.val))) c
          + (M i c : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    have h := congrFun (hMspec i) c
    simpa only [Pi.add_apply, intVec_apply] using h
  have hconst : (∑ i : Fin (N j), τ (G j g) c) = (N j : ℝ) * τ (G j g) c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmid : (∑ i : Fin (N j), ((castM (G j g)).mulVec (τ (e j i.val))) c)
      = ((castM (G j g)).mulVec (sgSum j τ)) c := by
    rw [← Finset.sum_apply]
    have h2 : (∑ i : Fin (N j), (castM (G j g)).mulVec (τ (e j i.val)))
        = (castM (G j g)).mulVec (sgSum j τ) := by
      have h3 : sgSum j τ = (∑ i : Fin (N j), τ (e j i.val)) := by
        funext c
        rw [Finset.sum_apply]
        rfl
      rw [h3]
      exact (Matrix.mulVec_sum (castM (G j g)) Finset.univ
        (fun i : Fin (N j) => τ (e j i.val))).symm
    rw [h2]
  have hlast : (∑ i : Fin (N j), ((M i c : ℤ) : ℝ)) = (((∑ i : Fin (N j), M i c : ℤ)) : ℝ) := by
    push_cast
    rfl
  have hmain : sgSum j τ c = (N j : ℝ) * τ (G j g) c
      + ((castM (G j g)).mulVec (sgSum j τ)) c + (((∑ i : Fin (N j), M i c : ℤ)) : ℝ) := by
    rw [← hsum, hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, hconst, hmid, hlast]
  refine ⟨-(∑ i : Fin (N j), M i c), ?_⟩
  simp only [Dv]
  push_cast
  linarith

/-- Integrality of a matrix times an integral vector. -/
theorem mulVec_int (A : IMat) (v : Fin 3 → ℝ) (hv : ∀ c, ∃ m : ℤ, v c = m) (c : Fin 3) :
    ∃ m : ℤ, ((castM A).mulVec v) c = m := by
  obtain ⟨m0, hm0⟩ := hv 0
  obtain ⟨m1, hm1⟩ := hv 1
  obtain ⟨m2, hm2⟩ := hv 2
  refine ⟨A c 0 * m0 + A c 1 * m1 + A c 2 * m2, ?_⟩
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, castM, Matrix.map_apply]
  rw [hm0, hm1, hm2]
  push_cast
  ring

theorem tau_one_int (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ)
    (c : Fin 3) : ∃ m : ℤ, τ (1 : IMat) c = m := by
  have h1 : (1 : IMat) ∈ arithRep j := by
    rw [← e_one j]; exact e_mem j 0 (N_pos j)
  obtain ⟨m, hm⟩ := hτ (1 : IMat) h1 (1 : IMat) h1
  refine ⟨- m c, ?_⟩
  have h := congrFun hm c
  simp only [Matrix.mul_one, Pi.add_apply, intVec_apply] at h
  rw [show Matrix.map (1 : IMat) (Int.cast : ℤ → ℝ) = castM (1 : IMat) from rfl,
    castM_one, Matrix.one_mulVec] at h
  push_cast
  linarith

theorem Dv_one_eq (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (c : Fin 3) :
    Dv j τ (1 : IMat) c = (N j : ℝ) * τ (1 : IMat) c := by
  simp only [Dv, castM_one, Matrix.one_mulVec]
  ring

theorem Dv_one_int (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ)
    (c : Fin 3) : ∃ m : ℤ, Dv j τ (1 : IMat) c = m := by
  obtain ⟨m, hm⟩ := tau_one_int j τ hτ c
  refine ⟨(N j : ℤ) * m, ?_⟩
  rw [Dv_one_eq, hm]
  push_cast
  ring

/-- Integrality of `D` on the whole point group. -/
theorem Dv_int (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ) :
    ∀ i, i < N j → ∀ c : Fin 3, ∃ m : ℤ, Dv j τ (e j i) c = m := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi c
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [e_one j]
      exact Dv_one_int j τ hτ c
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hpar : (Ad j).par.length + 1 = N j := by simpa only [N] using Ad_par_len j
      have hk : k < (Ad j).par.length := by omega
      have hkN : k < N j := by omega
      have hp1 : par1 j k < KK j := par1_lt j k hk
      have hp2 : par2 j k < N j := by
        have h1 := par2_le j k hk
        omega
      rw [e_par j k hk]
      obtain ⟨m, hm⟩ := hτ (G j (par1 j k)) (G_mem j (par1 j k) hp1)
        (e j (par2 j k)) (e_mem j (par2 j k) hp2)
      obtain ⟨m1, hm1⟩ := Dv_gen_int j τ hτ (par1 j k) hp1 c
      obtain ⟨m3, hm3⟩ := mulVec_int (G j (par1 j k)) (Dv j τ (e j (par2 j k)))
        (fun c' => ih (par2 j k) (by have h1 := par2_le j k hk; omega) hp2 c') c
      refine ⟨m1 + m3 + (N j : ℤ) * m c, ?_⟩
      have hlin := Dv_lin j τ (G j (par1 j k)) (e j (par2 j k)) m hm c
      rw [hlin, hm1, hm3]
      push_cast
      ring

/-- The averaging translation `s₀ = -Σ/n`. -/
noncomputable def s0 (j : Fin 73) (τ : IMat → Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun c => -(sgSum j τ c) / (N j : ℝ)

/-- The averaged cocycle `τ₀ = τ + s₀ - A s₀ = τ - (Σ - AΣ)/n`. -/
noncomputable def tau0 (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (A : IMat) : Fin 3 → ℝ :=
  fun c => τ A c + s0 j τ c - ((castM A).mulVec (s0 j τ)) c

theorem tau0_Dv (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (A : IMat) (c : Fin 3) :
    (N j : ℝ) * tau0 j τ A c = Dv j τ A c := by
  have hn : (N j : ℝ) ≠ 0 := by
    have h := N_pos j
    positivity
  have hs : s0 j τ = (-(1 / (N j : ℝ))) • sgSum j τ := by
    funext c
    simp only [s0, Pi.smul_apply, smul_eq_mul]
    ring
  rw [tau0, hs, Matrix.mulVec_smul, Dv]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The integer vector model of the averaged cocycle at element `i`. -/
noncomputable def avgZ (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ)
    (i : ℕ) : Fin 3 → ℤ :=
  fun c => if h : i < N j then Classical.choose (Dv_int j τ hτ i h c) else 0

theorem avgZ_spec (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ)
    (i : ℕ) (hi : i < N j) (c : Fin 3) :
    (avgZ j τ hτ i c : ℝ) = Dv j τ (e j i) c := by
  simp only [avgZ, dif_pos hi]
  exact (Classical.choose_spec (Dv_int j τ hτ i hi c)).symm

/-- Averaging: the cocycle is equivalent to an integral-valued cocycle on the class. -/
theorem exists_avgZ (j : Fin 73) {τ : IMat → Fin 3 → ℝ} (hτ : IsIntCocycle (arithRep j) τ) :
    ∃ z : ℕ → Fin 3 → ℤ,
      (Data.V3.dvd ((Ad j).n) (CZ.ofFun (z 0)) = true) ∧
      (∀ i, i < N j → ∀ c, (z i c : ℝ) = (N j : ℝ) * tau0 j τ (e j i) c) := by
  have hn : (N j : ℝ) ≠ 0 := by
    have h := N_pos j
    positivity
  refine ⟨avgZ j τ hτ, ?_, ?_⟩
  · rw [dvd_ofFun_iff]
    intro c
    obtain ⟨k, hk⟩ := tau_one_int j τ hτ c
    refine ⟨k, ?_⟩
    have h2 : avgZ j τ hτ 0 c = (N j : ℤ) * k := by
      apply Int.cast_injective (α := ℝ)
      rw [avgZ_spec j τ hτ 0 (N_pos j) c, e_one j, Dv_one_eq, hk]
      push_cast
      ring
    exact h2
  · intro i hi c
    rw [avgZ_spec j τ hτ i hi c, tau0_Dv]


end RC

end Work.SG
