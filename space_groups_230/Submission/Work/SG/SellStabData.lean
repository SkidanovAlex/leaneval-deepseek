import Mathlib
import Submission.Work.SG.SellStabDefs

/-! Kernel-checked facts about the generated Selling certificate tables (`decide +kernel`,
no `native_decide`).  These are the "Cayley table" axioms used by `conj_to_arithRep`; every
statement is a closed proposition about concrete data. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

namespace CZ

theorem stab_nodup_all : ∀ i : Fin 6, (Sof i).stab.Nodup := by decide +kernel

/-- The stabiliser table has no repeated entries. -/
theorem stab_nodup (i : Fin 6) : (Sof i).stab.Nodup := stab_nodup_all i

theorem tab_all : ∀ i : Fin 6,
    (Sof i).one < (Sof i).stab.length ∧
    mat (Sof i) (Sof i).one = Data.M3.one ∧
    (∀ a ∈ List.range (Sof i).stab.length, ∀ b ∈ List.range (Sof i).stab.length,
      gmul (Sof i) a b < (Sof i).stab.length ∧
      mat (Sof i) (gmul (Sof i) a b) =
        Data.M3.mul (mat (Sof i) a) (mat (Sof i) b)) := by decide +kernel

/-- The identity index is in range. -/
theorem one_lt (i : Fin 6) : (Sof i).one < (Sof i).stab.length := (tab_all i).1

/-- The identity index indexes the identity matrix. -/
theorem one_spec (i : Fin 6) : mat (Sof i) (Sof i).one = Data.M3.one := (tab_all i).2.1

/-- The multiplication table stays in range. -/
theorem mul_lt (i : Fin 6) {a b : ℕ} (ha : a < (Sof i).stab.length)
    (hb : b < (Sof i).stab.length) : gmul (Sof i) a b < (Sof i).stab.length :=
  ((tab_all i).2.2 a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)).1

/-- The multiplication table computes products of the stabiliser elements. -/
theorem mul_spec (i : Fin 6) {a b : ℕ} (ha : a < (Sof i).stab.length)
    (hb : b < (Sof i).stab.length) :
    mat (Sof i) (gmul (Sof i) a b) = Data.M3.mul (mat (Sof i) a) (mat (Sof i) b) :=
  ((tab_all i).2.2 a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)).2

theorem subs_lt_all : ∀ i : Fin 6, ∀ T ∈ (Sof i).subs, T < 2 ^ (Sof i).stab.length := by
  decide +kernel

/-- Every listed subgroup mask fits in `|stab|` bits. -/
theorem subs_lt (i : Fin 6) : ∀ T ∈ (Sof i).subs, T < 2 ^ (Sof i).stab.length := subs_lt_all i

theorem one_mask_mem_all : ∀ i : Fin 6, (1 <<< (Sof i).one) ∈ (Sof i).subs := by decide +kernel

/-- The trivial subgroup is listed. -/
theorem one_mask_mem (i : Fin 6) : (1 <<< (Sof i).one) ∈ (Sof i).subs := one_mask_mem_all i

/-- Injectivity of the index-to-matrix map on the in-range part of the table. -/
theorem stab_getD_inj (i : Fin 6) {a b : ℕ} (ha : a < (Sof i).stab.length)
    (hb : b < (Sof i).stab.length) (h : mat (Sof i) a = mat (Sof i) b) : a = b := by
  have hnd := stab_nodup i
  have h1 : (Sof i).stab[a] = (Sof i).stab[b] := by
    rw [← List.getD_eq_getElem _ _ ha, ← List.getD_eq_getElem _ _ hb]
    exact h
  exact (List.Nodup.getElem_inj_iff hnd).mp h1

/-- `mat` is `List.getElem` in range. -/
theorem mat_eq_getElem {S : Data.SellData} {a : ℕ} (ha : a < S.stab.length) :
    mat S a = S.stab[a] := List.getD_eq_getElem _ _ ha

/-! ### `arithData` facts -/

theorem arith_elems_len : ∀ j : Fin 73,
    (Data.arithData.getD j.val default).elems.length = (Data.arithData.getD j.val default).n := by
  decide +kernel

theorem arith_one_mem : ∀ j : Fin 73,
    Data.M3.one ∈ (Data.arithData.getD j.val default).elems := by decide +kernel

end CZ

end Work.SG
