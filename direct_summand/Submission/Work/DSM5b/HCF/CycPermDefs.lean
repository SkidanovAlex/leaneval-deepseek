import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs

/-!
# The cyclic permutation of the "deleted interval" (HCF bookkeeping)

For `a < b : Fin (n+2)` this file defines the permutation `cycPerm a b hab` of `Fin (n+1)`

* `av ↦ bv - 1 ↦ bv - 2 ↦ ⋯ ↦ av + 1 ↦ av`  (where `av = (a:ℕ)`, `bv = (b:ℕ)`),

fixing every index outside the interval `[av, bv-1]`.  It is the permutation relating the two
deleted tuples `tupDel a v` and `tupDel b v` when `v a = v b` (see
`Work.DSM5b.HCF.tupDel_cycPerm`), and its sign is `(-1)^(bv - av - 1)`
(`Work.DSM5b.HCF.sign_cycPerm`).

The construction goes through `Equiv.Perm.extendDomain`: the interval `[av, bv-1]` is identified
with `Fin (bv - av)` by `intEquiv`, and `cycPerm` is the extension by the identity of
`(finRotate (bv-av)).symm` (the predecessor cycle).  Its sign is thus `sign (finRotate (bv-av))`
by `Equiv.Perm.sign_extendDomain` and `Equiv.Perm.sign_symm`.
-/

namespace Work.DSM5b.HCF

open scoped Classical

/-! ### Two bookkeeping lemmas about `finRotate` -/

lemma finRotate_symm_val_of_ne_zero {d : ℕ} [NeZero d] (i : Fin d) (hi : i ≠ 0) :
    (((finRotate d).symm i : Fin d) : ℕ) = (i : ℕ) - 1 := by
  rw [finRotate_symm_apply]
  exact Fin.val_sub_one_of_ne_zero hi

lemma finRotate_symm_zero_val {d : ℕ} [NeZero d] :
    (((finRotate d).symm (0 : Fin d) : Fin d) : ℕ) = d - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 :=
    ⟨d - 1, by have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d); omega⟩
  have h : (finRotate (m + 1)).symm (0 : Fin (m + 1)) = Fin.last m := by
    rw [Equiv.symm_apply_eq]
    exact finRotate_last.symm
  rw [h, Fin.val_last]
  simp

/-! ### The interval `[av, bv-1]` as `Fin (bv - av)` -/

/-- The increasing identification of `Fin (bv - av)` with the indices `x` with
`av ≤ x < bv`. -/
noncomputable def intEquiv {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) :
    Fin ((b : ℕ) - (a : ℕ)) ≃
      {x : Fin (n + 1) // (a : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (b : ℕ)} where
  toFun y := ⟨⟨(a : ℕ) + (y : ℕ), by have hb := b.isLt; have ha := a.isLt; omega⟩,
    by
      have hb := b.isLt; have ha := a.isLt; have hy := y.isLt
      refine ⟨?_, ?_⟩ <;> simp only [Fin.val_mk] <;> omega⟩
  invFun z := ⟨(z.1 : ℕ) - (a : ℕ), by have hz2 := z.2.2; have hz1 := z.2.1; omega⟩
  left_inv y := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  right_inv z := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

lemma intEquiv_apply_val {n : ℕ} (a b : Fin (n + 2)) (hab : a < b)
    (y : Fin ((b : ℕ) - (a : ℕ))) :
    (((intEquiv a b hab) y : Fin (n + 1)) : ℕ) = (a : ℕ) + (y : ℕ) := rfl

lemma intEquiv_symm_val {n : ℕ} (a b : Fin (n + 2)) (hab : a < b)
    (z : {x : Fin (n + 1) // (a : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (b : ℕ)}) :
    (((intEquiv a b hab).symm z : Fin _) : ℕ) = ((z : Fin (n + 1)) : ℕ) - (a : ℕ) := rfl

/-! ### The cyclic permutation -/

/-- The cyclic permutation `av ↦ bv-1 ↦ bv-2 ↦ ⋯ ↦ av+1 ↦ av` of the indices in `[av, bv-1]`,
fixing every other index. -/
noncomputable def cycPerm {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.extendDomain ((finRotate ((b : ℕ) - (a : ℕ))).symm) (intEquiv a b hab)

/-- `cycPerm` fixes every index outside the interval `[av, bv-1]`. -/
lemma cycPerm_apply_of_not_mem {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {x : Fin (n + 1)}
    (h : ¬ ((a : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (b : ℕ))) : cycPerm a b hab x = x := by
  rw [cycPerm]
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ h

/-- The value of `cycPerm` at an index below the interval. -/
lemma cycPerm_val_of_lt {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {x : Fin (n + 1)}
    (h : (x : ℕ) < (a : ℕ)) : (cycPerm a b hab x : ℕ) = (x : ℕ) := by
  rw [cycPerm_apply_of_not_mem a b hab (by omega)]

/-- The value of `cycPerm` at an index of the interval other than its left end. -/
lemma cycPerm_val_of_mem {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {x : Fin (n + 1)}
    (h1 : (a : ℕ) ≤ (x : ℕ)) (h2 : (x : ℕ) < (b : ℕ)) (h3 : (x : ℕ) ≠ (a : ℕ)) :
    (cycPerm a b hab x : ℕ) = (x : ℕ) - 1 := by
  haveI : NeZero ((b : ℕ) - (a : ℕ)) := ⟨by omega⟩
  have hx : (a : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (b : ℕ) := ⟨h1, h2⟩
  rw [cycPerm,
    Equiv.Perm.extendDomain_apply_subtype ((finRotate _).symm) (intEquiv a b hab) (b := x) hx]
  have hyval : (((intEquiv a b hab).symm ⟨x, hx⟩ : Fin ((b : ℕ) - (a : ℕ))) : ℕ) = (x : ℕ) - (a : ℕ) :=
    intEquiv_symm_val a b hab ⟨x, hx⟩
  have hy0 : ((intEquiv a b hab).symm ⟨x, hx⟩ : Fin ((b : ℕ) - (a : ℕ))) ≠ 0 := by
    intro hz
    rw [hz] at hyval
    simp only [Fin.val_zero] at hyval
    omega
  rw [intEquiv_apply_val, finRotate_symm_val_of_ne_zero _ hy0, hyval]
  omega

/-- The value of `cycPerm` at the left end `av` of the interval. -/
lemma cycPerm_val_of_eq {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {x : Fin (n + 1)}
    (h : (x : ℕ) = (a : ℕ)) : (cycPerm a b hab x : ℕ) = (b : ℕ) - 1 := by
  haveI : NeZero ((b : ℕ) - (a : ℕ)) := ⟨by omega⟩
  have hx : (a : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (b : ℕ) := by refine ⟨?_, ?_⟩ <;> omega
  rw [cycPerm,
    Equiv.Perm.extendDomain_apply_subtype ((finRotate _).symm) (intEquiv a b hab) (b := x) hx]
  have hyval : (((intEquiv a b hab).symm ⟨x, hx⟩ : Fin ((b : ℕ) - (a : ℕ))) : ℕ) = 0 := by
    rw [intEquiv_symm_val]
    change (x : ℕ) - (a : ℕ) = 0
    omega
  have hy0 : ((intEquiv a b hab).symm ⟨x, hx⟩ : Fin ((b : ℕ) - (a : ℕ))) = 0 := by
    apply Fin.ext
    rw [intEquiv_symm_val]
    change (x : ℕ) - (a : ℕ) = ((0 : Fin ((b : ℕ) - (a : ℕ))) : ℕ)
    simp only [Fin.val_zero]
    omega
  rw [intEquiv_apply_val, hy0, finRotate_symm_zero_val]
  omega

/-- The value of `cycPerm` at an index at or above the right end of the interval. -/
lemma cycPerm_val_of_ge {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {x : Fin (n + 1)}
    (h : (b : ℕ) ≤ (x : ℕ)) : (cycPerm a b hab x : ℕ) = (x : ℕ) := by
  rw [cycPerm_apply_of_not_mem a b hab (by omega)]

/-- **The sign of the deleted-interval cycle** is `(-1)^(bv - av - 1)`. -/
theorem sign_cycPerm {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) :
    Equiv.Perm.sign (cycPerm a b hab) = (-1 : ℤˣ) ^ ((b : ℕ) - (a : ℕ) - 1) := by
  rw [cycPerm, Equiv.Perm.sign_extendDomain, Equiv.Perm.sign_symm]
  simp

end Work.DSM5b.HCF
