import Mathlib
import Submission.Work.SGsep.symAux.defs
import Submission.Work.SGsep.bmats_dvd

/-!
# Table facts for `symChk_yes`

The certified table `Data.repArith k` (kernel-checked by `Data.arithData_chk`) is the BFS
presentation of the arithmetic class of `k`: generators `gens`, elements `elems` with
`elems 0 = 1`, `elems (i+1) = gens[par i] * elems[par i.2]`, and multiplication tables
`mulGen`/`genIdx`.  This file extracts those facts as a structure `DkFacts k`, derives the
handful of consequences used by the `sym`-soundness argument, and records the facts about the
cocycle table `Data.repZ k` that `bmats_dvd` already extracted (`repZ_facts`).

All the statements are phrased in terms of `(Dk k)` and the aliases of `symAux/defs`; the
`rfl`-equations `eK_eq`, `GK_eq`, ... bridge the two vocabularies where rewriting needs it.

Nothing here is `sorry`ed.
-/

namespace Work.SGsep

open Work.SG

/-! ## The vocabulary bridges -/

theorem eK_eq (k : Fin 230) (i : ℕ) :
    eK k i = ((Dk k).elems.getD i Data.M3.one).toIMat := rfl

theorem GK_eq (k : Fin 230) (g : ℕ) :
    GK k g = ((Dk k).gens.getD g Data.M3.one).toIMat := rfl

theorem nK_eq (k : Fin 230) : nK k = (Dk k).n := rfl

theorem kK_eq (k : Fin 230) : kK k = (Dk k).gens.length := rfl

theorem geni_eq (k : Fin 230) (g : ℕ) : geni k g = (Dk k).genIdx.getD g 0 := rfl

theorem mulg_eq (k : Fin 230) (g i : ℕ) :
    mulg k g i = ((Dk k).mulGen.getD g []).getD i 0 := rfl

theorem par1_eq (k : Fin 230) (i : ℕ) : par1 k i = ((Dk k).par.getD i (0, 0)).1 := rfl

theorem par2_eq (k : Fin 230) (i : ℕ) : par2 k i = ((Dk k).par.getD i (0, 0)).2 := rfl

theorem zK_eq (k : Fin 230) (i : ℕ) :
    zK k i = (Data.repZ.getD k.val []).getD i Data.V3.zero := rfl

theorem zK_eq_zTab (k : Fin 230) (i : ℕ) : zK k i = zTab k i := rfl

theorem Dk_eq (k : Fin 230) : Dk k = Data.repArith k.val := rfl

theorem elems_eq (k : Fin 230) : (Dk k).elems = (Data.repArith k.val).elems := rfl

/-- The kernel check `Data.arithData_chk`, phrased for the table `Dk k`. -/
theorem dk_chk (k : Fin 230) : (Dk k).chk (Data.repClass k.val) = true := arith_chk k

/-- The facts about the certified table of `Dk k` that `Data.arithData_chk` provides,
in the form used by the `sym` soundness argument. -/
structure DkFacts (k : Fin 230) : Prop where
  elems_len : (Dk k).elems.length = (Dk k).n
  nodup : (Dk k).elems.Nodup
  head : (Dk k).elems.head? = some Data.M3.one
  par_len : (Dk k).par.length + 1 = (Dk k).n
  par_bound1 : ∀ t, t < (Dk k).par.length → ((Dk k).par.getD t (0, 0)).1 < (Dk k).gens.length
  par_le : ∀ t, t < (Dk k).par.length → ((Dk k).par.getD t (0, 0)).2 ≤ t
  par_rel : ∀ t, t < (Dk k).par.length →
      (Dk k).elems.getD (t + 1) Data.M3.one =
        Data.M3.mul ((Dk k).gens.getD ((Dk k).par.getD t (0, 0)).1 Data.M3.one)
          ((Dk k).elems.getD ((Dk k).par.getD t (0, 0)).2 Data.M3.one)
  mulgen_len : (Dk k).mulGen.length = (Dk k).gens.length
  mulgen_rowlen : ∀ g, g < (Dk k).gens.length →
      ((Dk k).mulGen.getD g []).length = (Dk k).n
  mulgen_bound : ∀ g, g < (Dk k).gens.length → ∀ i, i < (Dk k).n →
      ((Dk k).mulGen.getD g []).getD i 0 < (Dk k).n
  mulgen_rel : ∀ g, g < (Dk k).gens.length → ∀ i, i < (Dk k).n →
      (Dk k).elems.getD (((Dk k).mulGen.getD g []).getD i 0) Data.M3.one =
        Data.M3.mul ((Dk k).gens.getD g Data.M3.one) ((Dk k).elems.getD i Data.M3.one)
  genidx_len : (Dk k).genIdx.length = (Dk k).gens.length
  genidx_bound : ∀ g, g < (Dk k).gens.length → (Dk k).genIdx.getD g 0 < (Dk k).n
  genidx_rel : ∀ g, g < (Dk k).gens.length →
      (Dk k).elems.getD ((Dk k).genIdx.getD g 0) Data.M3.one =
        (Dk k).gens.getD g Data.M3.one

theorem dk_facts (k : Fin 230) : DkFacts k := by
  have h := dk_chk k
  simp only [Data.ArithData.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hlen⟩, hhead⟩, hparlen⟩, hpar⟩, hmglen⟩, hmul⟩, hgilen⟩,
    hgen⟩, hnodup⟩
  refine ⟨hlen, hnodup, hhead, hparlen, ?_, ?_, ?_, hmglen, ?_, ?_, ?_, hgilen, ?_, ?_⟩
  · intro t ht; exact (hpar t (by omega)).1.1
  · intro t ht; exact (hpar t (by omega)).1.2
  · intro t ht; exact (hpar t (by omega)).2
  · intro g hg; exact (hmul g hg).1
  · intro g hg i hi; exact ((hmul g hg).2 i hi).1
  · intro g hg i hi; exact ((hmul g hg).2 i hi).2
  · intro g hg; exact (hgen g hg).1
  · intro g hg; exact (hgen g hg).2

/-! ## Consequences in the alias vocabulary -/

theorem dk_elems_len (k : Fin 230) : (Dk k).elems.length = nK k := (dk_facts k).elems_len

theorem dk_nodup (k : Fin 230) : (Dk k).elems.Nodup := (dk_facts k).nodup

theorem dk_par_length (k : Fin 230) : (Dk k).par.length = nK k - 1 := by
  have h : (Dk k).par.length = (Dk k).n - 1 := by
    have h2 := (dk_facts k).par_len
    omega
  simpa only [nK_eq k] using h

/-- The order of a certified arithmetic class is positive. -/
theorem nK_pos (k : Fin 230) : 0 < nK k := by
  have hlen : (Dk k).elems.length = (Dk k).n := (dk_facts k).elems_len
  rcases List.head?_eq_some_iff.mp (dk_facts k).head with ⟨t, ht⟩
  have h1 : 0 < (Dk k).n := by rw [← hlen, ht]; simp
  simpa only [nK_eq k] using h1

/-- The identity is the first element of the table. -/
theorem eK_zero (k : Fin 230) : eK k 0 = 1 := by
  rcases List.head?_eq_some_iff.mp (dk_facts k).head with ⟨t, ht⟩
  show ((Dk k).elems.getD 0 Data.M3.one).toIMat = 1
  rw [ht, List.getD_cons_zero, Data.M3.toIMat_one]

/-- The BFS recursion of the element table. -/
theorem eK_par (k : Fin 230) (i : ℕ) (hi : i < (Dk k).par.length) :
    eK k (i + 1) = GK k (par1 k i) * eK k (par2 k i) := by
  have h := (dk_facts k).par_rel i hi
  show ((Dk k).elems.getD (i + 1) Data.M3.one).toIMat =
      ((Dk k).gens.getD ((Dk k).par.getD i (0, 0)).1 Data.M3.one).toIMat *
        ((Dk k).elems.getD ((Dk k).par.getD i (0, 0)).2 Data.M3.one).toIMat
  rw [h, Data.M3.toIMat_mul]

/-- The `g`-th generator is the `geni k g`-th element. -/
theorem eK_geni (k : Fin 230) (g : ℕ) (hg : g < kK k) : eK k (geni k g) = GK k g := by
  have h := (dk_facts k).genidx_rel g hg
  show ((Dk k).elems.getD ((Dk k).genIdx.getD g 0) Data.M3.one).toIMat =
      ((Dk k).gens.getD g Data.M3.one).toIMat
  rw [h]

/-- Multiplication by a generator in the element table. -/
theorem eK_mulgen (k : Fin 230) (g i : ℕ) (hg : g < kK k) (hi : i < nK k) :
    eK k (mulg k g i) = GK k g * eK k i := by
  have h := (dk_facts k).mulgen_rel g hg i hi
  show ((Dk k).elems.getD (((Dk k).mulGen.getD g []).getD i 0) Data.M3.one).toIMat =
      ((Dk k).gens.getD g Data.M3.one).toIMat * ((Dk k).elems.getD i Data.M3.one).toIMat
  rw [h, Data.M3.toIMat_mul]

/-! ## The cocycle table `Data.repZ k` -/

theorem zK_head (k : Fin 230) : zK k 0 = Data.V3.zero := by
  rw [zK_eq_zTab]
  exact (repZ_facts k).1

/-- `repZ_facts` rephrased in the vocabulary of `symAux/defs`. -/
theorem repZ_facts_Dk (k : Fin 230) :
    zK k 0 = Data.V3.zero ∧
    (∀ g, g < kK k → ∀ i, i < nK k →
      (Data.V3.sub (zK k (mulg k g i))
        (Data.V3.add (zK k (geni k g))
          (Data.M3.mulV ((Dk k).gens.getD g Data.M3.one) (zK k i)))).dvd ((Dk k).n : ℤ)
        = true) := repZ_facts k

/-- The integer form of the cocycle recursion `z(g·A) ≡ z(g) + g z(A) (mod n)`. -/
theorem repZ_cocycle (k : Fin 230) (g i : ℕ) (hg : g < kK k) (hi : i < nK k) :
    ∃ m : Fin 3 → ℤ, (zK k (mulg k g i)).toFun
      = (zK k (geni k g)).toFun + (GK k g).mulVec (zK k i).toFun + (nK k : ℤ) • m := by
  have h0 := (repZ_facts_Dk k).2 g hg i hi
  simp only [zK_eq, Dk_eq] at h0
  rw [dvd_iff_toFun] at h0
  have hc : ∀ c : Fin 3, ∃ m : ℤ,
      (zK k (mulg k g i)).toFun c
        = (zK k (geni k g)).toFun c + ((GK k g).mulVec (zK k i).toFun) c
          + (nK k : ℤ) * m := by
    intro c
    obtain ⟨w, hw⟩ := h0 c
    refine ⟨w, ?_⟩
    simp only [zK_eq, GK_eq, nK_eq, mulg_eq, geni_eq, Dk_eq,
      V3_toFun_sub, Pi.sub_apply, V3_toFun_add, Pi.add_apply, M3_toIMat_mulV] at hw ⊢
    linarith
  choose m hm using hc
  refine ⟨m, funext fun c => ?_⟩
  have hh := hm c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh ⊢
  exact hh

/-! ## Values of `sgTau` on the table -/

/-- `TauOnTable k` in the vocabulary of this development. -/
theorem sgTau_eK (k : Fin 230) (hk : TauOnTable k) (i : ℕ) (hi : i < nK k) :
    sgTau k (eK k i) = fun c => ((zK k i).toFun c : ℝ) / (nK k : ℝ) := hk i hi

/-! ## Membership in `arithRep (sgArith k)` -/

/-- The elements of `arithRep (sgArith k)` are exactly the `eK k i`. -/
theorem mem_arithRep_iff (k : Fin 230) (A : IMat) :
    A ∈ arithRep (sgArith k) ↔ ∃ i, i < nK k ∧ A = eK k i := by
  have h1 : arithRep (sgArith k) = {A : IMat | ∃ e ∈ (Dk k).elems, A = e.toIMat} := by
    rw [arithRep_eq_data (sgArith k), ← repArith_eq_data_getD k]
  rw [h1]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, hi, hii⟩ := List.mem_iff_getElem.mp he
    have hi' : i < (Dk k).elems.length := hi
    refine ⟨i, by rw [← dk_elems_len k]; exact hi', ?_⟩
    have h2 : eK k i = e.toIMat := by
      show ((Dk k).elems.getD i Data.M3.one).toIMat = e.toIMat
      rw [List.getD_eq_getElem (Dk k).elems Data.M3.one hi', hii]
    exact h2.symm
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < (Dk k).elems.length := by rw [dk_elems_len k]; exact hi
    exact ⟨(Dk k).elems[i]'hi', List.getElem_mem hi', by
      show ((Dk k).elems.getD i Data.M3.one).toIMat = ((Dk k).elems[i]'hi').toIMat
      rw [List.getD_eq_getElem (Dk k).elems Data.M3.one hi']⟩

/-! ## The defect at the identity -/

theorem symDef_one (k : Fin 230) (a : Data.SymCert) (hk : TauOnTable k) :
    symDef k a 1 ∈ zLat := by
  have hz : sgTau k (1 : IMat) = 0 := by
    rw [← eK_zero k, sgTau_eK k hk 0 (nK_pos k), zK_head k, V3_toFun_zero]
    funext c
    simp
  have h1 : symDef k a 1 = (a.o : ℝ) • sgTau k (1 : IMat) := by
    show (a.o : ℝ) • sgTau k 1 - (symSig k a - (toRMat (1 : IMat)).mulVec (symSig k a))
        = (a.o : ℝ) • sgTau k 1
    rw [toRMat_one, Matrix.one_mulVec, sub_self, sub_zero]
  rw [h1, hz, smul_zero]
  exact zLat.zero_mem

end Work.SGsep
