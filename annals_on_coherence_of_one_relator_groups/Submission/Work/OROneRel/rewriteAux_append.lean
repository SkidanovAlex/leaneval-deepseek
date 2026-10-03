/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# `rewriteAux` is additive over concatenation of words

The Magnus rewriting `rewriteAux t i L` deletes the letters equal to `t` from the word `L` and
decorates every remaining letter with the running exponent sum in `t` before it, starting from `i`.
This file records the fundamental compatiblity of `rewriteAux` with concatenation of words: the
rewriting of `L₁ ++ L₂` is the rewriting of `L₁` followed by the rewriting of `L₂`, the latter
starting from the exponent sum accumulated by `L₁`, namely `i + sigmaList t L₁`.
-/
import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- `sigmaList` of a cons: the sign of the head plus `sigmaList` of the tail. -/
private theorem sigmaList_cons_aux' (t : α) (p : α × Bool) (L : List (α × Bool)) :
    sigmaList t (p :: L) = letterSign t p + sigmaList t L := by
  simp [sigmaList]

/-- The sign of a letter equal to `t`. -/
private theorem letterSign_pair_eq_aux' (t : α) {a : α} (h : a = t) (b : Bool) :
    letterSign t (a, b) = (if b then (1 : ℤ) else -1) := by
  subst h
  cases b <;> simp [letterSign]

/-- The sign of a letter different from `t` vanishes. -/
private theorem letterSign_pair_ne_aux' (t : α) {a : α} (h : a ≠ t) (b : Bool) :
    letterSign t (a, b) = 0 := by
  simp [letterSign, h]

/-- Computation rule for `rewriteAux` on a cons whose head is the letter `t`: the head is dropped and
the starting exponent is shifted by its sign. -/
private theorem rewriteAux_cons_eq_aux' (t : α) {a : α} (h : a = t) (b : Bool) (i : ℤ)
    (L : List (α × Bool)) :
    rewriteAux t i ((a, b) :: L) = rewriteAux t (i + (if b then (1 : ℤ) else -1)) L := by
  rw [rewriteAux.eq_2, dif_pos (show (a, b).1 = t from h)]

/-- Computation rule for `rewriteAux` on a cons whose head differs from `t`: the head is decorated
with the current exponent sum and the tail is rewritten with the same starting value. -/
private theorem rewriteAux_cons_ne_aux' (t : α) {a : α} (h : a ≠ t) (b : Bool) (i : ℤ)
    (L : List (α × Bool)) :
    rewriteAux t i ((a, b) :: L) = ((⟨a, h⟩, i), b) :: rewriteAux t i L := by
  rw [rewriteAux.eq_2, dif_neg (show ¬(a, b).1 = t from fun hh => h hh)]

theorem rewriteAux_append {α : Type u} (t : α) (i : ℤ) (L₁ L₂ : List (α × Bool)) :
    Work.OROneRel.rewriteAux t i (L₁ ++ L₂) =
      Work.OROneRel.rewriteAux t i L₁ ++
        Work.OROneRel.rewriteAux t (i + Work.OROneRel.sigmaList t L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [sigmaList, rewriteAux.eq_1]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = t
    · -- the head is `t`: it is dropped and the exponent is shifted
      rw [List.cons_append, rewriteAux_cons_eq_aux' t h b i (L ++ L₂),
        rewriteAux_cons_eq_aux' t h b i L, ih (i + (if b then (1 : ℤ) else -1))]
      have hidx : (i + (if b then (1 : ℤ) else -1)) + sigmaList t L
          = i + sigmaList t ((a, b) :: L) := by
        rw [sigmaList_cons_aux', letterSign_pair_eq_aux' t h]
        ring
      rw [hidx]
    · -- the head differs from `t`: it is decorated at the current exponent and the index is kept
      rw [List.cons_append, rewriteAux_cons_ne_aux' t h b i (L ++ L₂),
        rewriteAux_cons_ne_aux' t h b i L, ih i]
      have hidx : i + sigmaList t ((a, b) :: L) = i + sigmaList t L := by
        rw [sigmaList_cons_aux', letterSign_pair_ne_aux' t h]
        simp
      rw [hidx, List.cons_append]

end Work.OROneRel
