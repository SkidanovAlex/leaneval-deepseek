/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus rewriting telescopes

The Magnus rewriting `rewriteAux t i L` of a word `L : List (α × Bool)` with respect to a letter `t`
deletes the letters equal to `t` and decorates every other letter with the running exponent sum of `t`
before it (starting from `i`).  Its expansion `expand t` replaces a decorated letter `((s,j),b)` by
the conjugate `t ^ j * s ^ b * t ^ (-j)`.  This file proves the telescoping identity

  `t ^ i * mk L = expand t (rewriteAux t i L) * t ^ (i + sigmaList t L)`

by induction on `L`, generalizing the initial exponent `i`: the `t`-letters that `rewrite` has
dropped reappear as the frame corrections of the conjugates, and the deficit of the exponent sums is
exactly `sigmaList t L`.  This is the combinatorial identity underlying the fact that
`zeta t : F((α \ {t}) × ℤ) →* F α`, `(s,j) ↦ t ^ j * s * t ^ (-j)`, computes the Magnus rewriting.
-/
import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- `FreeGroup.mk` of a one-letter word: `of a` (if `b = true`) or its inverse (if `b = false`),
written as a `ℤ`-power. -/
theorem mk_singleton_aux (a : α) (b : Bool) :
    FreeGroup.mk [(a, b)] = (FreeGroup.of a) ^ (if b then (1 : ℤ) else -1) := by
  cases b
  · rw [show (if (false : Bool) then (1 : ℤ) else -1) = (-1 : ℤ) from rfl, zpow_neg_one]
    simp only [FreeGroup.of, FreeGroup.inv_mk]
    rfl
  · rw [show (if (true : Bool) then (1 : ℤ) else -1) = (1 : ℤ) from rfl, zpow_one]
    rfl

/-- `FreeGroup.mk` of a cons: the first letter is taken out as a `ℤ`-power. -/
theorem mk_cons_aux (p : α × Bool) (L : List (α × Bool)) :
    FreeGroup.mk (p :: L) =
      (FreeGroup.of p.1) ^ (if p.2 then (1 : ℤ) else -1) * FreeGroup.mk L := by
  rw [← List.singleton_append, ← FreeGroup.mul_mk, mk_singleton_aux]

/-- `sigmaList` of a cons is the sign of the first letter plus `sigmaList` of the tail. -/
theorem sigmaList_cons_aux (t : α) (p : α × Bool) (L : List (α × Bool)) :
    sigmaList t (p :: L) = letterSign t p + sigmaList t L := by
  simp [sigmaList]

/-- The sign of a letter equal to `t`. -/
theorem letterSign_eq_aux (t : α) (b : Bool) :
    letterSign t (t, b) = (if b then (1 : ℤ) else -1) := by
  cases b <;> simp [letterSign]

/-- The sign of a letter different from `t` vanishes. -/
theorem letterSign_ne_aux (t : α) {a : α} (h : a ≠ t) (b : Bool) : letterSign t (a, b) = 0 := by
  simp [letterSign, h]

/-- The expansion of a cons is the expansion of the first letter times the expansion of the tail. -/
theorem expand_cons_aux (t : α) (x : ({a : α // a ≠ t} × ℤ) × Bool)
    (v : List (({a : α // a ≠ t} × ℤ) × Bool)) :
    expand t (x :: v) = expandLetter t x * expand t v := by
  simp [expand]

/-- The expansion of a decorated letter `((a,j),b)` is the conjugate `t ^ j * a ^ b * t ^ (-j)`. -/
theorem expandLetter_pair_aux (t : α) (a : α) (ha : a ≠ t) (i : ℤ) (b : Bool) :
    expandLetter t (((⟨a, ha⟩ : {a // a ≠ t}), i), b) =
      (FreeGroup.of t) ^ i * (FreeGroup.of a) ^ (if b then (1 : ℤ) else -1) *
        (FreeGroup.of t) ^ (-i) := rfl

/-- Computation rule for `rewriteAux` on a cons whose head is the letter `t`. -/
theorem rewriteAux_cons_eq_aux (t : α) {a : α} (h : a = t) (b : Bool) (i : ℤ)
    (L : List (α × Bool)) :
    rewriteAux t i ((a, b) :: L) = rewriteAux t (i + (if b then (1 : ℤ) else -1)) L := by
  rw [rewriteAux.eq_2, dif_pos (show (a, b).1 = t from h)]

/-- Computation rule for `rewriteAux` on a cons whose head differs from `t`: the head is decorated
with the current exponent sum and the tail is rewritten with the same starting value. -/
theorem rewriteAux_cons_ne_aux (t : α) {a : α} (h : a ≠ t) (b : Bool) (i : ℤ)
    (L : List (α × Bool)) :
    rewriteAux t i ((a, b) :: L) = ((⟨a, h⟩, i), b) :: rewriteAux t i L := by
  rw [rewriteAux.eq_2, dif_neg (show ¬(a, b).1 = t from fun hh => h hh)]

/-- The conjugation identity used in the induction step: `g ^ i * h * w` can be written as the
conjugate `g ^ i * h * g ^ (-i)` followed by `g ^ i * w`. -/
theorem conj_zpow_mul_aux {G : Type*} [Group G] (g h w : G) (i : ℤ) :
    (g ^ i * h) * w = (g ^ i * h * g ^ (-i)) * (g ^ i * w) := by
  calc (g ^ i * h) * w
      = (g ^ i * h) * (g ^ (-i) * (g ^ i * w)) := by
          congr 1
          rw [← mul_assoc, zpow_neg, inv_mul_cancel, one_mul]
    _ = (g ^ i * h * g ^ (-i)) * (g ^ i * w) := by rw [← mul_assoc]

theorem mk_eq_expand_rewriteAux {α : Type u} (t : α) (i : ℤ) (L : List (α × Bool)) :
    (FreeGroup.of t) ^ i * FreeGroup.mk L =
      Work.OROneRel.expand t (Work.OROneRel.rewriteAux t i L) *
        (FreeGroup.of t) ^ (i + Work.OROneRel.sigmaList t L) := by
  classical
  induction L generalizing i with
  | nil =>
      rw [rewriteAux.eq_1, ← FreeGroup.one_eq_mk]
      simp [expand, sigmaList]
  | cons p L ih =>
      obtain ⟨a, b⟩ := p
      by_cases h : a = t
      · rw [rewriteAux_cons_eq_aux t h b i L, h, mk_cons_aux, ← mul_assoc, ← zpow_add, ih]
        rw [sigmaList_cons_aux, letterSign_eq_aux]
        rw [Int.add_assoc]
      · rw [rewriteAux_cons_ne_aux t h b i L, expand_cons_aux, mk_cons_aux]
        rw [expandLetter_pair_aux t a h i b, ← mul_assoc, conj_zpow_mul_aux, ih i, ← mul_assoc]
        rw [sigmaList_cons_aux, letterSign_ne_aux t h]
        simp

end Work.OROneRel
