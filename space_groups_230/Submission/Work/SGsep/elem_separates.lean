import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.vA_conj
import Submission.Work.SGsep.det_trace_conj
import Submission.Work.SGsep.IsOrdOf_conj
import Submission.Work.SGsep.IsOrdOf_unique
import Submission.Work.SGsep.NZ_conj
import Submission.Work.SGsep.NZ_annihilates
import Submission.Work.SGsep.keyE_conj

/-!
# The `elem` invariant separates the 230 space-group representatives

This file proves `Work.SGsep.elem_separates`: the counts of elements of two representatives with
key `(det, trace, order of v_A in ℤ³/N_Aℤ³)` are invariants of integral equivalence, so if the
counts stored in the data (`Data.elemCount`) for the same key differ, no integral equivalence
with unimodular `U` exists.

The two main ingredients are

* `keyE_conj` (imported): `keyE` is invariant under `A ↦ U A U⁻¹`;
* `ElemTbl.keyE_table`: the lattice-theoretic `keyE` of the `i`-th table element of a
  representative equals the flat data key `Data.ekey k i` (using `TauOnTable` and the
  order certificates `Data.elemTab`).
-/

namespace Work.SGsep

open Work.SG
open Work.SG.Data
open LeanEval.Geometry.SpaceGroupsProblem
open Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## 1. Lists, ring inverses and table facts -/

/-- A list is the list of its `getD`-values. -/
theorem map_eq_map_getD {α β : Type*} (l : List α) (f : α → β) (d : α) :
    l.map f = (List.range l.length).map (fun i => f (l.getD i d)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.getD_cons_zero, ih]
    congr 1

/-- `Ring.inverse` is the identity on units of `ℤ`. -/
theorem Ring_inverse_int {u : ℤ} (hu : IsUnit u) : Ring.inverse u = u := by
  rcases Int.isUnit_iff.mp hu with h | h
  · rw [h]; exact Ring.inverse_one ℤ
  · rw [h]
    have h1 : Ring.inverse (-1 : ℤ) * (-1) = 1 :=
      Ring.inverse_mul_cancel (-1) (Int.isUnit_iff.mpr (Or.inr rfl))
    omega

/-- The matrix inverse `⁻¹` on integer matrices agrees with `invMat` on unimodular matrices
(`Ring.inverse` of `det U = ±1` is `det U`). -/
theorem Matrix_inv_eq_invMat {U : IMat} (hU : IsUnit U.det) : (U⁻¹ : IMat) = invMat U := by
  rw [Matrix.inv_def, invMat, Ring_inverse_int hU]

/-- The element table of `Data.repArith k` is duplicate-free and has length `n`. -/
theorem repArith_elems (k : Fin 230) :
    (Data.repArith k).elems.Nodup ∧ (Data.repArith k).elems.length = (Data.repArith k).n := by
  have h := of_decide_eq_true (List.all_eq_true.mp arithData_elems_nodup_len
    (Data.repClass k.val) (List.mem_range.mpr (repClass_lt k)))
  have hval : (sgArith k).val = Data.repClass k.val := by
    show Data.repClass k.val % 73 = Data.repClass k.val
    exact Nat.mod_eq_of_lt (repClass_lt k)
  rw [repArith_eq_data_getD k, hval]
  exact h

/-- `Data.elemTab_chk` unpacked at a fixed index `i < n`. -/
theorem elemTab_chk_at (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    ((Data.elemTab.getD k []).getD i default).chk k i = true := by
  obtain ⟨_, h2⟩ := Data.elemTab_chk
  have hk := List.all_eq_true.mp h2 k.val (List.mem_range.mpr k.isLt)
  obtain ⟨_, hall⟩ := Bool.and_eq_true_iff.mp hk
  exact List.all_eq_true.mp hall i (List.mem_range.mpr hi)

/-! ## 2. The lattice-theoretic key of a table element equals the flat data key -/

namespace ElemTbl

/-- A flat `V3` as a real vector. -/
def toRV (v : Data.V3) : Fin 3 → ℝ := toRVec v.toFun

theorem toRV_inj : Function.Injective toRV :=
  fun _ _ h => Data.V3.toFun_injective (toRVec_injective h)

@[simp] theorem toRV_smul (c : ℤ) (v : Data.V3) : toRV (Data.V3.smul c v) = c • toRV v := by
  funext i; fin_cases i <;> simp [toRV, toRVec, Data.V3.smul, Data.V3.toFun]

/-- `mulV` commutes with the passage to real vectors. -/
theorem mulV_toRV (A : Data.M3) (v : Data.V3) :
    toRV (A.mulV v) = (toRMat A.toIMat).mulVec (toRV v) := by
  show toRVec (A.mulV v).toFun = (toRMat A.toIMat).mulVec (toRVec v.toFun)
  rw [← Data.M3.toIMat_mulV, mulVec_toRVec]

/-- Membership in `M ℤ³` is membership in the `ℤ`-span of the columns of `M`. -/
theorem mem_latImg_iff_cols (M : Data.M3) (v : Data.V3) :
    toRV v ∈ latImg M.toIMat ↔ ∃ cs : List ℤ, Data.lin M.cols cs = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := mem_latImg.mp hv
    have hw2 : M.toIMat.mulVec w = v.toFun := by
      apply toRVec_injective
      rw [← mulVec_toRVec]
      exact hw
    refine ⟨[w 0, w 1, w 2], ?_⟩
    apply Data.V3.toFun_injective
    have hwl : (fun i : Fin 3 => ([w 0, w 1, w 2] : List ℤ).getD i.val 0) = w := by
      funext i; fin_cases i <;> simp
    rw [← Data.M3.mulVec_getD M [w 0, w 1, w 2], hwl, hw2]
  · rintro ⟨cs, hcs⟩
    obtain ⟨w, hw⟩ := Data.M3.exists_mulVec_of_lin hcs
    refine ⟨w, ?_⟩
    show (toRMat M.toIMat).mulVec (toRVec w) = toRVec v.toFun
    rw [mulVec_toRVec, hw]

/-! ### The order of an `M3` and of its image matrix -/

theorem toIMat_add (A B : Data.M3) : (A.add B).toIMat = A.toIMat + B.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.add, Matrix.add_apply]

theorem toIMat_zero : ((⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Data.M3)).toIMat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat]

theorem toIMat_pow (A : Data.M3) (m : ℕ) : (A.pow m).toIMat = A.toIMat ^ m := by
  induction m with
  | zero => simp [Data.M3.pow, Data.M3.toIMat_one]
  | succ n ih => rw [Data.M3.pow, Data.M3.toIMat_mul, ih, pow_succ']

theorem toIMat_normSum (A : Data.M3) (m : ℕ) : (A.normSum m).toIMat = Nsum A.toIMat m := by
  induction m with
  | zero => simp [Data.M3.normSum, Nsum, toIMat_zero]
  | succ n ih =>
    simp only [Data.M3.normSum, toIMat_add, ih, toIMat_pow, Nsum]
    rw [Finset.sum_range_succ, add_comm]

/-- Boolean version of "`A.ord` is the order of `A`": it is positive, an exponent, and no
smaller positive exponent works.  `Bool`-valued so that the whole table can be checked by
kernel evaluation (`decide`). -/
def ordOKB (A : Data.M3) : Bool :=
  decide (0 < A.ord) && (A.pow A.ord == Data.M3.one) &&
    (List.range A.ord).all (fun r => r == 0 || (A.pow r != Data.M3.one))

/-- `OrdOK A`: `A.ord` really is the order of `A`. -/
def OrdOK (A : Data.M3) : Prop := ordOKB A = true

theorem ordOK_spec {A : Data.M3} (h : OrdOK A) :
    0 < A.ord ∧ A.pow A.ord = Data.M3.one ∧
      ∀ r, r < A.ord → 1 ≤ r → A.pow r ≠ Data.M3.one := by
  have h' : (decide (0 < A.ord) && (A.pow A.ord == Data.M3.one) &&
      (List.range A.ord).all (fun r => r == 0 || (A.pow r != Data.M3.one))) = true := h
  obtain ⟨h12, hmin⟩ := Bool.and_eq_true_iff.mp h'
  obtain ⟨h0b, hpb⟩ := Bool.and_eq_true_iff.mp h12
  refine ⟨of_decide_eq_true h0b, beq_iff_eq.mp hpb, ?_⟩
  intro r hr hr1
  have hh := List.all_eq_true.mp hmin r (List.mem_range.mpr hr)
  rcases Bool.or_eq_true_iff.mp hh with h0 | hne
  · exact absurd (beq_iff_eq.mp h0) (by omega)
  · exact fun he => bne_iff_ne.mp hne he

/-- `M3.ord` really is the order of the matrix, whenever `OrdOK` holds. -/
theorem mOrd_toIMat {A : Data.M3} (h : OrdOK A) : mOrd A.toIMat = A.ord := by
  obtain ⟨h1, h2, h3⟩ := ordOK_spec h
  have hpow' : A.toIMat ^ A.ord = 1 := by rw [← toIMat_pow, h2, Data.M3.toIMat_one]
  have hex : ∃ m, 1 ≤ m ∧ A.toIMat ^ m = 1 := ⟨A.ord, h1, hpow'⟩
  have hle : mOrd A.toIMat ≤ A.ord := mOrd_min hex h1 hpow'
  have hm := mOrd_spec hex
  by_contra hne
  have hlt : mOrd A.toIMat < A.ord := lt_of_le_of_ne hle hne
  have hbad : A.pow (mOrd A.toIMat) ≠ Data.M3.one := h3 _ hlt hm.1
  apply hbad
  apply Data.M3.toIMat_injective
  rw [toIMat_pow, hm.2, Data.M3.toIMat_one]

/-- `Data.normOf A` is `N_A` in matrix form, for `OrdOK A`. -/
theorem normOf_toIMat {A : Data.M3} (h : OrdOK A) :
    (Data.normOf A).toIMat = NZ A.toIMat := by
  rw [Data.normOf, NZ, mOrd_toIMat h, toIMat_normSum]

/-! ### Kernel-checked facts about the tables -/

theorem repArith_n_pos_chk : (List.range 230).all
    (fun k => decide (0 < (Data.repArith k).n)) = true := by decide

theorem repArith_ordOK_chk : (List.range 230).all
    (fun k => (List.range (Data.repArith k).n).all
      (fun i => ordOKB ((Data.repArith k).elems.getD i Data.M3.one))) = true := by
  decide

theorem elemTab_o_le_chk : (List.range 230).all
    (fun k => (List.range (Data.repArith k).n).all
      (fun i => decide (((Data.elemTab.getD k []).getD i default).o ≤ 47))) = true := by
  decide

theorem repArith_n_pos_at (k : Fin 230) : 0 < (Data.repArith k).n :=
  of_decide_eq_true (List.all_eq_true.mp repArith_n_pos_chk k.val (List.mem_range.mpr k.isLt))

theorem repArith_ordOK_at (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    OrdOK ((Data.repArith k).elems.getD i Data.M3.one) :=
  List.all_eq_true.mp
    (List.all_eq_true.mp repArith_ordOK_chk k.val (List.mem_range.mpr k.isLt))
    i (List.mem_range.mpr hi)

theorem elemTab_o_le_at (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) :
    ((Data.elemTab.getD k []).getD i default).o ≤ 47 :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp elemTab_o_le_chk k.val (List.mem_range.mpr k.isLt))
    i (List.mem_range.mpr hi))

/-! ### Elementary arithmetic and list lemmas -/

theorem v3_dvd_iff {n : ℤ} {w : Data.V3} (h : Data.V3.dvd n w = true) :
    n ∣ w.x ∧ n ∣ w.y ∧ n ∣ w.z := by
  simp only [Data.V3.dvd, Bool.and_eq_true_iff, beq_iff_eq] at h
  exact ⟨Int.dvd_of_emod_eq_zero h.1.1, Int.dvd_of_emod_eq_zero h.1.2,
    Int.dvd_of_emod_eq_zero h.2⟩

theorem int_ediv_cast {a : ℤ} {n : ℕ} (hn : n ≠ 0) (h : (n : ℤ) ∣ a) :
    ((a / (n : ℤ) : ℤ) : ℝ) = (n : ℝ)⁻¹ * (a : ℝ) := by
  have h2 : ((a / (n : ℤ) : ℤ) : ℝ) * (n : ℝ) = (a : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [eq_inv_mul_iff_mul_eq₀ hnR, mul_comm, h2]

theorem toRV_ediv (w : Data.V3) {n : ℕ} (hn : n ≠ 0) (hd : Data.V3.dvd (n : ℤ) w = true) :
    (n : ℝ)⁻¹ • toRV w = toRV (Data.V3.ediv w (n : ℤ)) := by
  obtain ⟨hx, hy, hz⟩ := v3_dvd_iff hd
  funext c
  fin_cases c
  · change (n : ℝ)⁻¹ * (w.x : ℝ) = ((w.x / (n : ℤ) : ℤ) : ℝ)
    exact (int_ediv_cast hn hx).symm
  · change (n : ℝ)⁻¹ * (w.y : ℝ) = ((w.y / (n : ℤ) : ℤ) : ℝ)
    exact (int_ediv_cast hn hy).symm
  · change (n : ℝ)⁻¹ * (w.z : ℝ) = ((w.z / (n : ℤ) : ℤ) : ℝ)
    exact (int_ediv_cast hn hz).symm

theorem all_zipWith_getElem {α β : Type*} {l₁ : List α} {l₂ : List β} {f : α → β → Bool}
    (h : (List.zipWith f l₁ l₂).all id = true) {j : ℕ} (h1 : j < l₁.length)
    (h2 : j < l₂.length) : f l₁[j] l₂[j] = true := by
  have hj : j < (List.zipWith f l₁ l₂).length := by
    rw [List.length_zipWith]; exact Nat.lt_min.mpr ⟨h1, h2⟩
  have hthis : (List.zipWith f l₁ l₂)[j] = true :=
    List.all_eq_true.mp h _ (List.getElem_mem hj)
  rwa [List.getElem_zipWith (f := f) (l := l₁) (l' := l₂) (i := j) (h := hj)] at hthis

theorem smallPrimes_eq : ((List.range 48).filter Nat.Prime) = Data.smallPrimes := by decide

/-- Every prime divisor of `o ≤ 47` occurs in `Data.primesOf o` (the list of "small primes"
dividing `o`). -/
theorem mem_primesOf {p o : ℕ} (hp : p.Prime) (hpo : p ∣ o) (ho0 : 0 < o) (ho : o ≤ 47) :
    p ∈ Data.primesOf o := by
  have hsmall : p ∈ Data.smallPrimes := by
    have hpl : p ≤ 47 := le_trans (Nat.le_of_dvd ho0 hpo) ho
    have : p ∈ (List.range 48).filter Nat.Prime := by
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr (by omega), decide_eq_true_eq.mpr hp⟩
    rwa [smallPrimes_eq] at this
  rw [Data.primesOf, List.mem_filter]
  exact ⟨hsmall, beq_iff_eq.mpr (Nat.dvd_iff_mod_eq_zero.mp hpo)⟩

theorem ordInLat_eq_of_IsOrdOf {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {o : ℕ}
    (h : IsOrdOf L v o) : ordInLat L v = o :=
  IsOrdOf_unique (ordInLat_spec ⟨o, h⟩) h

/-! ### The main bridge -/

/-- The lattice-theoretic key `keyE k A` of the `i`-th element of the table of representative
`k` is exactly the flat data key `Data.ekey k i`.  Requires `TauOnTable k` (the identification
`sgTau k = repZ/n` on the table) and the element order certificate `Data.ElemCert.chk k i`
(from `Data.elemTab_chk`), which certifies that the stored order `o` is the order of `v_A` in
`ℤ³/N_Aℤ³`. -/
theorem keyE_table (k : Fin 230) (i : ℕ) (hi : i < (Data.repArith k).n) (hk : TauOnTable k)
    (hchk : ((Data.elemTab.getD k []).getD i default).chk k i = true) :
    keyE k ((Data.repArith k).elems.getD i Data.M3.one).toIMat = Data.ekey k i := by
  have hchk' := hchk
  simp only [Data.ElemCert.chk] at hchk'
  set A : Data.M3 := (Data.repArith k).elems.getD i Data.M3.one with hA
  set e : Data.ElemCert := (Data.elemTab.getD k []).getD i default with he
  set z : Data.V3 := (Data.repZ.getD k []).getD i Data.V3.zero with hz
  set N : Data.M3 := Data.normOf A with hN
  obtain ⟨hrest, hzip⟩ := Bool.and_eq_true_iff.mp hchk'
  obtain ⟨hrest, hlenb⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hrest, hyes⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨h1d, hdvd⟩ := Bool.and_eq_true_iff.mp hrest
  have h1 : 1 ≤ e.o := of_decide_eq_true h1d
  have hlen : e.nos.length = (Data.primesOf e.o).length := beq_iff_eq.mp hlenb
  have hordOK : OrdOK A := repArith_ordOK_at k i hi
  have hNZ : NZ A.toIMat = N.toIMat := by
    rw [hN]; exact (normOf_toIMat hordOK).symm
  have hτ : sgTau k A.toIMat = fun c => (z.toFun c : ℝ) / ((Data.repArith k).n : ℝ) := hk i hi
  have hnpos : 0 < (Data.repArith k).n := repArith_n_pos_at k
  have hn0 : (Data.repArith k).n ≠ 0 := ne_of_gt hnpos
  have hvA : vA (sgTau k) A.toIMat = toRV (Data.vOf k i) := by
    have hfun : (fun c => (z.toFun c : ℝ) / ((Data.repArith k).n : ℝ))
        = ((Data.repArith k).n : ℝ)⁻¹ • toRV z := by
      funext c
      simp only [Pi.smul_apply, toRV, toRVec, Data.V3.toFun, div_eq_mul_inv]
      ring
    rw [vA, hτ, hNZ, hfun, Matrix.mulVec_smul, ← mulV_toRV]
    rw [Data.vOf]
    exact toRV_ediv (N.mulV z) hn0 hdvd
  have hIsOrd : IsOrdOf (latImg (NZ A.toIMat)) (vA (sgTau k) A.toIMat) e.o := by
    rw [hvA, hNZ]
    refine ⟨h1, ?_, ?_⟩
    · have hy := SpanCert.chk_yes (gs := N.cols)
        (v := Data.V3.smul ((e.o : ℕ) : ℤ) (Data.vOf k i)) (cs := e.yes) hyes
      rw [← toRV_smul]
      exact (mem_latImg_iff_cols N (Data.V3.smul ((e.o : ℕ) : ℤ) (Data.vOf k i))).mpr
        ⟨e.yes, hy⟩
    · intro p hp hpo hmem
      have ho0 : 0 < e.o := by omega
      have hpmem : p ∈ Data.primesOf e.o := mem_primesOf hp hpo ho0 (elemTab_o_le_at k i hi)
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hpmem
      have hj2 : j < e.nos.length := by rw [hlen]; exact hj
      have hzc := all_zipWith_getElem (l₁ := Data.primesOf e.o) (l₂ := e.nos)
        (f := fun p c => SpanCert.chk N.cols (Data.V3.smul ((e.o / p : ℕ) : ℤ) (Data.vOf k i))
          (SpanCert.no c.1 c.2)) hzip hj hj2
      rw [hje] at hzc
      have hno := SpanCert.chk_no (gs := N.cols)
        (v := Data.V3.smul ((e.o / p : ℕ) : ℤ) (Data.vOf k i))
        (φ := (e.nos[j]).1) (m := (e.nos[j]).2) hzc
      rw [← toRV_smul] at hmem
      obtain ⟨cs, hcs⟩ := (mem_latImg_iff_cols N (Data.V3.smul ((e.o / p : ℕ) : ℤ)
        (Data.vOf k i))).mp hmem
      exact hno ⟨cs, hcs⟩
  have hord_eq : ordInLat (latImg (NZ A.toIMat)) (vA (sgTau k) A.toIMat) = e.o :=
    ordInLat_eq_of_IsOrdOf hIsOrd
  unfold keyE Data.ekey
  dsimp only
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact Data.M3.toIMat_det A
  · exact Data.M3.toIMat_trace A
  · exact hord_eq

end ElemTbl

open ElemTbl (keyE_table)

/-! ## 3. `Data.elemCount` is the `EInv` count -/

/-- The flat data count `Data.elemCount k d t o` (counting indices `i` of the table with
`Data.ekey k i = (d,t,o)`) equals the lattice-level count `EInv k d t o` (counting the elements
`A ∈ Tk k` with `keyE k A = (d,t,o)`). -/
theorem elemCount_eq_EInv (k : Fin 230) (d t : ℤ) (o : ℕ) (hk : TauOnTable k) :
    Data.elemCount k d t o = EInv k d t o := by
  obtain ⟨hnodup, hlen⟩ := repArith_elems k
  set L : List IMat := (Data.repArith k).elems.map Data.M3.toIMat with hL
  have hnodupL : L.Nodup := by rw [hL]; exact hnodup.map Data.M3.toIMat_injective
  have h1 : L.toFinset.filter (fun A => keyE k A = (d, t, o))
      = (List.filter (fun A => decide (keyE k A = (d, t, o))) L).toFinset := by
    rw [List.toFinset_filter]
    ext x
    simp [Finset.mem_filter, decide_eq_true_eq]
  have key : EInv k d t o = List.countP (fun A => decide (keyE k A = (d, t, o))) L := by
    rw [EInv, show Tk k = L.toFinset from rfl, h1]
    rw [List.toFinset_card_of_nodup (hnodupL.filter _), List.countP_eq_length_filter]
  rw [key]
  simp only [Data.elemCount]
  rw [hL, map_eq_map_getD (Data.repArith k).elems Data.M3.toIMat Data.M3.one, List.countP_map,
    hlen]
  apply List.countP_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [Function.comp_apply, keyE_table k i hi hk (elemTab_chk_at k i hi), decide_eq_true_eq,
    beq_iff_eq]

/-! ## 4. `EInv` is an invariant of integral equivalence -/

/-- The `elem` count is invariant under an integral equivalence: the conjugation map
`A ↦ U A U⁻¹` is a bijection between the two element sets which preserves `keyE` (by
`keyE_conj`). -/
theorem EInv_eq_of_intEquiv (k l : Fin 230) (d t : ℤ) (o : ℕ) (U : IMat) (s : Fin 3 → ℝ)
    (hU : IsUnit U.det)
    (hIE : IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s) :
    EInv k d t o = EInv l d t o := by
  have hinv : (U⁻¹ : IMat) = invMat U := Matrix_inv_eq_invMat hU
  have hcoc : ∀ {A : IMat}, A ∈ arithRep (sgArith k) → ∃ n : Fin 3 → ℤ,
      sgTau l (U * A * invMat U) = (toRMat U).mulVec (sgTau k A) + s
        - (toRMat (U * A * invMat U)).mulVec s + toRVec n := by
    intro A hA
    obtain ⟨n, hn⟩ := hIE.2 A hA
    have hshape : U * A * U⁻¹ = U * A * invMat U := by rw [hinv]
    rw [hshape] at hn
    exact ⟨n, hn⟩
  have hconj : ∀ A : IMat, invMat U * (U * A * invMat U) * U = A := by
    intro A
    calc invMat U * (U * A * invMat U) * U
        = (invMat U * U) * A * (invMat U * U) := by noncomm_ring
      _ = A := by rw [invMat_mul hU, one_mul, mul_one]
  have hinj : ∀ {A B : IMat}, U * A * invMat U = U * B * invMat U → A = B := by
    intro A B h
    have hh := congrArg (fun M => invMat U * M * U) h
    rwa [hconj A, hconj B] at hh
  rw [EInv, EInv]
  refine Finset.card_bij (fun A _ => U * A * invMat U) ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter] at hA ⊢
    obtain ⟨hA1, hA2⟩ := hA
    refine ⟨?_, ?_⟩
    · rw [mem_Tk_iff]
      exact (hIE.1 (U * A * invMat U)).mpr ⟨A, (mem_Tk_iff k A).mp hA1, by rw [hinv]⟩
    · rw [← hA2]
      exact keyE_conj k l U s hU (hcoc ((mem_Tk_iff k A).mp hA1))
  · intro A1 hA1 A2 hA2 h
    exact hinj h
  · intro B hB
    simp only [Finset.mem_filter] at hB
    obtain ⟨hB1, hB2⟩ := hB
    obtain ⟨A, hA, hAB⟩ := (hIE.1 B).mp ((mem_Tk_iff l B).mp hB1)
    have hAB' : B = U * A * invMat U := by rw [hAB, hinv]
    refine ⟨A, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨(mem_Tk_iff k A).mpr hA, ?_⟩
      rw [← keyE_conj k l U s hU (hcoc hA), ← hAB']
      exact hB2
    · exact hAB'.symm

/-! ## 5. The separation theorem -/

/-- The `elem` invariant separates: if the counts of elements of the two representatives with
key `(det, trace, order of v_A in ℤ³/N_Aℤ³)` equal to `(d,t,o)` differ, there is no integral
equivalence.  `Data.elemCount` is the data-level count; `TauOnTable k`/`l` identify `sgTau`
with `repZ/n` on the tables, and `Data.elemTab_chk` (imported) certifies that the order in the
table really is the order of `v_A` in `ℤ³/N_Aℤ³`.  Tools: `latImg_conj_eq_map`,
`latImg_le_conj_iff`, `conj_sub_one`, `NZ_conj`, `vA_conj`, `IsOrdOf_conj`, `IsOrdOf_unique`,
`det_trace_conj`, `table_facts`, the `Data.M3`/`V3` bridges and `SpanCert.chk_yes/no` in
`SGsepDefs`. -/
theorem elem_separates (k l : Fin 230) (d t : ℤ) (o : ℕ)
    (hk : TauOnTable k) (hl : TauOnTable l)
    (h : Data.elemCount k d t o ≠ Data.elemCount l d t o) :
    ¬ ∃ U : IMat, IsUnit U.det ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s := by
  rintro ⟨U, hU, s, hIE⟩
  exact h ((elemCount_eq_EInv k d t o hk).trans
    ((EInv_eq_of_intEquiv k l d t o U s hU hIE).trans (elemCount_eq_EInv l d t o hl).symm))

end Work.SGsep
