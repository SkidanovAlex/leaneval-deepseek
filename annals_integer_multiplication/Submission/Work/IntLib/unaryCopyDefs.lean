import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.Layout.Base

/-!
# Plumbing for `Work.IntLib.unaryCopy`

`unaryCopy` copies the unary counter `Unary m Ca` sitting on stack `a` to a second stack `b`
(initialised with `gEnd :: Cb`), using a third scratch stack `c` and one working register `r0`,
in time `O(m+1)`, restoring everything else.

This file provides the *notation* for stack functions used by the programs in this directory:

* `st2 X k₁ k₂ v₁ v₂` — the stack function `X` with `k₁` replaced by `v₁` and `k₂` by `v₂`;
* `st3 X a b c A B C` — three replacements, presented in the `st2` shape with frame the
  `b`-update, so that a program touching `a` and `c` can be run inside it.

All the lemmas below are pure `Function.update` bookkeeping.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- The working register of the `unaryCopy` program. -/
def r0 : Reg := (0 : Fin 16)

/-- `X` with `k₁ := v₁` and `k₂ := v₂` (the `k₁` update outermost). -/
def st2 (X : Stk → List Glyph) (k₁ k₂ : Stk) (v₁ v₂ : List Glyph) : Stk → List Glyph :=
  Function.update (Function.update X k₂ v₂) k₁ v₁

/-- `X` with `a := A`, `b := B`, `c := C`, written as a `st2` with frame `Function.update X b B`. -/
def st3 (X : Stk → List Glyph) (a b c : Stk) (A B C : List Glyph) : Stk → List Glyph :=
  st2 (Function.update X b B) a c A C

@[simp] theorem st2_self₁ (X : Stk → List Glyph) (k₁ k₂ : Stk) (v₁ v₂ : List Glyph) :
    st2 X k₁ k₂ v₁ v₂ k₁ = v₁ := by simp [st2]

theorem st2_self₂ {X : Stk → List Glyph} {k₁ k₂ : Stk} {v₁ v₂ : List Glyph} (h : k₂ ≠ k₁) :
    st2 X k₁ k₂ v₁ v₂ k₂ = v₂ := by
  simp [st2, Function.update, h]

theorem st2_of_ne {X : Stk → List Glyph} {k₁ k₂ k : Stk} {v₁ v₂ : List Glyph}
    (h₁ : k ≠ k₁) (h₂ : k ≠ k₂) : st2 X k₁ k₂ v₁ v₂ k = X k := by
  simp [st2, Function.update, h₁, h₂]

theorem upd_st2₁ (X : Stk → List Glyph) (k₁ k₂ : Stk) (v₁ v₂ v : List Glyph) :
    Function.update (st2 X k₁ k₂ v₁ v₂) k₁ v = st2 X k₁ k₂ v v₂ := by
  unfold st2
  rw [Function.update_idem]

theorem upd_st2₂ {X : Stk → List Glyph} {k₁ k₂ : Stk} {v₁ v₂ v : List Glyph} (h : k₁ ≠ k₂) :
    Function.update (st2 X k₁ k₂ v₁ v₂) k₂ v = st2 X k₁ k₂ v₁ v := by
  unfold st2
  rw [Function.update_comm h, Function.update_idem]

@[simp] theorem st3_self_a (X : Stk → List Glyph) (a b c : Stk) (A B C : List Glyph) :
    st3 X a b c A B C a = A := st2_self₁ ..

theorem st3_self_c {X : Stk → List Glyph} {a b c : Stk} {A B C : List Glyph} (h : c ≠ a) :
    st3 X a b c A B C c = C := st2_self₂ h

theorem st3_self_b {X : Stk → List Glyph} {a b c : Stk} {A B C : List Glyph}
    (ha : b ≠ a) (hc : b ≠ c) : st3 X a b c A B C b = B := by
  unfold st3 st2
  rw [Function.update_of_ne ha, Function.update_of_ne hc, Function.update_self]

theorem st3_of_ne {X : Stk → List Glyph} {a b c k : Stk} {A B C : List Glyph}
    (h₁ : k ≠ a) (h₂ : k ≠ b) (h₃ : k ≠ c) : st3 X a b c A B C k = X k := by
  unfold st3 st2
  rw [Function.update_of_ne h₁, Function.update_of_ne h₃, Function.update_of_ne h₂]

theorem upd_st3_a (X : Stk → List Glyph) (a b c : Stk) (A B C A' : List Glyph) :
    Function.update (st3 X a b c A B C) a A' = st3 X a b c A' B C := upd_st2₁ ..

theorem upd_st3_c {X : Stk → List Glyph} {a b c : Stk} {A B C C' : List Glyph} (h : a ≠ c) :
    Function.update (st3 X a b c A B C) c C' = st3 X a b c A B C' := upd_st2₂ h

theorem upd_st3_b {X : Stk → List Glyph} {a b c : Stk} {A B C B' : List Glyph}
    (ha : b ≠ a) (hc : b ≠ c) :
    Function.update (st3 X a b c A B C) b B' = st3 X a b c A B' C := by
  unfold st3 st2
  rw [Function.update_comm (Ne.symm ha), Function.update_comm (Ne.symm hc), Function.update_idem]

/-! ## A scratch stack -/

/-- There is a stack different from `a`, from `b` and from `14` (the index of `gTok`). -/
theorem exists_scratch (a b : Stk) : ∃ c : Stk, c ≠ a ∧ c ≠ b ∧ c ≠ (14 : Fin 16) := by
  have h3 : ({a, b, (14 : Stk)} : Finset Stk).card ≤ 3 := by
    have h1 := Finset.card_insert_le a ({b, (14 : Stk)} : Finset Stk)
    have h2 := Finset.card_insert_le b ({(14 : Stk)} : Finset Stk)
    simp only [Finset.card_singleton] at h2
    omega
  have h16 : ({a, b, (14 : Stk)} : Finset Stk).card < (Finset.univ : Finset Stk).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card h16
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2.1, hc.2.2⟩

theorem gmk_eq_gTok_iff (c : Stk) : gmk c = gTok ↔ c = (14 : Fin 16) := by
  constructor
  · intro h; exact Glyph.mk.inj h
  · intro h; rw [h]; rfl

theorem gmk_ne_gTok {c : Stk} (h : c ≠ (14 : Fin 16)) : gmk c ≠ gTok :=
  fun hh => h ((gmk_eq_gTok_iff c).mp hh)

/-- `st2` collapses to a single update when the value stored at `k₁` is put back there. -/
theorem st2_eq_update {X : Stk → List Glyph} {k₁ k₂ : Stk} {v₁ v₂ : List Glyph}
    (hne : k₁ ≠ k₂) (h : X k₁ = v₁) : st2 X k₁ k₂ v₁ v₂ = Function.update X k₂ v₂ := by
  funext k
  unfold st2
  by_cases hk : k = k₁
  · subst hk
    rw [Function.update_self, Function.update_of_ne hne, ← h]
  · rw [Function.update_of_ne hk]

/-- `st3` collapses to a `st2` when the value stored at `b` is put back there. -/
theorem st3_eq_st2 {X : Stk → List Glyph} {a b c : Stk} {A B C : List Glyph} (h : X b = B) :
    st3 X a b c A B C = st2 X a c A C := by
  unfold st3
  rw [← h, Function.update_eq_self]

theorem st2_eq_st3 {X : Stk → List Glyph} {a b c : Stk} {A B C : List Glyph} (h : X b = B) :
    st2 X a c A C = st3 X a b c A B C := (st3_eq_st2 h).symm

/-- the `b`-update of a `st2` frame is invisible -/
theorem st2_update_b {X : Stk → List Glyph} {a b c : Stk} {A C B : List Glyph}
    (h : X b = B) : st2 (Function.update X b B) a c A C = st2 X a c A C := by
  rw [← h, Function.update_eq_self]


/-! ## Lists of the shape `replicate m gTok ++ h :: L` -/

theorem headD_replicate_cons (m : ℕ) (h d : Glyph) (L : List Glyph) :
    (List.replicate m gTok ++ h :: L).headD d = if m = 0 then h else gTok := by
  cases m with
  | zero => simp
  | succ m => simp [List.replicate_succ]

theorem tail_replicate_cons_succ (m : ℕ) (h : Glyph) (L : List Glyph) :
    (List.replicate (m + 1) gTok ++ h :: L).tail = List.replicate m gTok ++ h :: L := by
  simp [List.replicate_succ]

theorem headD_tok_succ (m : ℕ) (h : Glyph) (L : List Glyph) :
    (List.replicate (m + 1) gTok ++ h :: L).headD Glyph.eos = gTok := by
  simp [List.replicate_succ]

end Work.IntLib
