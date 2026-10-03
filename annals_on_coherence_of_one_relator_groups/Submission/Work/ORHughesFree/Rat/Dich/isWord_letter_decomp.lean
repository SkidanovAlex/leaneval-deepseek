/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The letter decomposition of a word of `Rat(U)`

A *word* `x` of `Rat(U)` (an element of the `U`-biset `U ♮ X`, see
`Submission/Work/ORHughesFree/Rat/Word.lean`) is either the image of a group element, or its
normal form in `ℕ[U ♮ X]` is a monomial on a *letter* of the `X`-part: there is a non-empty list
`l` of non-zero elements of `Rat(U)` such that

  `Psi x = single (Sum.inr ⟦⟨l, hl⟩⟧) 1`  and  `Tree y < Tree x` for every `y ∈ l`.

The strict complexity bound is what makes the statement usable for the induction of [JZLA20,
Proposition 5.1]: it says that every letter occurring in the `X`-word of a word is the value of a
*smaller* word, so that one may recurse on the complexity `Tree x`.

The proof is a direct induction on the generation of `RatU.IsWord x`:

* `x = ofGroup u` is the first alternative;
* `x = y⋄` with `y ≠ 0` has normal form the single letter `Xgen y`, and
  `Tree y < Tree (y⋄) = exp (exp (Tree y))`;
* `x = a * b`: `Psi` is multiplicative, so `Psi x` is the monomial on the product of the two
  normal forms `p * q : U ♮ X`; the four cases `Ugen * Ugen`, `Ugen * X`, `X * Ugen`, `X * X`
  are read off from the multiplication table of `U ♮ X` (`NU.Ugen_mul`, `NU.Ugen_mul_mk`,
  `NU.mk_mul_Ugen`, `NU.mk_mul_mk`), and the entries of the resulting list are the old entries
  (`mulFirst`/`mulLast` change them by multiplication by a group element, which preserves
  `Tree`), together with the list concatenation bound `Tree a ≤ Tree a * Tree b` of
  `Rat.treeOrderFacts`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.Word
import Submission.Work.ORHughesFree.RatU.exists_decomp
import Submission.Work.ORHughesFree.Rat.treeOrderFacts
import Submission.Work.ORHughesFree.Rat.FreeProduct.Model

set_option autoImplicit false

namespace Work.ORHughesFree.Rat.Dich

open Work.ORHughesFree

namespace IsWordLetterDecomp

variable {U : Type} [Group U]

/-! ### Lists all of whose entries lie strictly below a given tree -/

/-- `ListGood t l`: every entry of the list `l` is a non-zero element of `Rat(U)` whose complexity
`Tree` is strictly below `t`. -/
def ListGood (t : Tree) (l : List (RatU U)) : Prop :=
  ∀ y ∈ l, y ≠ 0 ∧ Tree.lt (Rat.treeOfRat U y) t

/-- Strict form of the transitivity of the tree order. -/
theorem lt_of_lt_of_le {x y z : Tree} (h₁ : Tree.lt x y) (h₂ : Tree.le y z) : Tree.lt x z := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact Tree.lt_trans h₁ h₂

/-- `ListGood` is monotone in the bound. -/
theorem ListGood.mono {t t' : Tree} {l : List (RatU U)} (h : ListGood t l)
    (ht : Tree.le t t') : ListGood t' l :=
  fun y hy => ⟨(h y hy).1, lt_of_lt_of_le (h y hy).2 ht⟩

/-- A concatenation of two lists with the same bound is again good. -/
theorem ListGood.append {t t' t'' : Tree} {l m : List (RatU U)}
    (h₁ : ListGood t l) (h₂ : ListGood t' m) (h₁' : Tree.le t t'') (h₂' : Tree.le t' t'') :
    ListGood t'' (l ++ m) := by
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact ⟨(h₁ y hy).1, lt_of_lt_of_le (h₁ y hy).2 h₁'⟩
  · exact ⟨(h₂ y hy).1, lt_of_lt_of_le (h₂ y hy).2 h₂'⟩

/-! ### The two `U`-actions on `Rat(U)` preserve the complexity -/

theorem treeOfRat_actL (u : U) (x : RatU U) :
    Rat.treeOfRat U (FreeProduct.actL u x) = Rat.treeOfRat U x := by
  rw [FreeProduct.actL, RatU.treeOfRat_mul_ofGroup]

theorem treeOfRat_actR (u : U) (x : RatU U) :
    Rat.treeOfRat U (FreeProduct.actR u x) = Rat.treeOfRat U x := by
  rw [FreeProduct.actR, RatU.treeOfRat_ofGroup_mul]

theorem actL_ne_zero {u : U} {x : RatU U} : FreeProduct.actL u x ≠ 0 ↔ x ≠ 0 := by
  rw [FreeProduct.actL]
  constructor
  · intro h hx0
    exact h (by rw [hx0, zero_mul])
  · intro hx
    exact RatU.mul_ne_zero hx (FreeProduct.ofGroup_ne_zero u⁻¹)

theorem actR_ne_zero {u : U} {x : RatU U} : FreeProduct.actR u x ≠ 0 ↔ x ≠ 0 := by
  rw [FreeProduct.actR]
  constructor
  · intro h hx0
    exact h (by rw [hx0, mul_zero])
  · intro hx
    exact RatU.mul_ne_zero (FreeProduct.ofGroup_ne_zero u⁻¹) hx

/-- The complexity of a word is a non-zero tree (a restatement of `RatU.isWord_ne_zero'` through
`Rat.treeOfRat_eq_zero_iff`). -/
theorem treeOfRat_isWord_ne_zero {x : RatU U} (hx : RatU.IsWord x) :
    Rat.treeOfRat U x ≠ 0 :=
  fun h => RatU.isWord_ne_zero' hx ((Rat.treeOfRat_eq_zero_iff U x).mp h)

/-! ### `mulFirst` and `mulLast` preserve goodness -/

/-- `mulFirst u` multiplies the *first* entry by a group element; it changes the entries only by
`actL`, which preserves both non-vanishing and the complexity, so `ListGood` is preserved. -/
theorem ListGood.mulFirst {t : Tree} {l : List (RatU U)} (h : ListGood t l) (u : U) :
    ListGood t (FreeProduct.mulFirst u l) := by
  match l with
  | [] => intro a ha; simp [FreeProduct.mulFirst] at ha
  | c :: cs =>
    intro a ha
    rw [FreeProduct.mulFirst_cons] at ha
    rcases List.mem_cons.mp ha with hh | ha
    · rw [hh]
      exact ⟨actL_ne_zero.mpr (h c (by simp)).1,
        by rw [treeOfRat_actL]; exact (h c (by simp)).2⟩
    · exact h a (List.mem_cons_of_mem c ha)

/-- `mulLast · u` multiplies the *last* entry by a group element; as for `mulFirst`, `ListGood` is
preserved. -/
theorem ListGood.mulLast {t : Tree} (u : U) :
    ∀ (l : List (RatU U)), ListGood t l → ListGood t (FreeProduct.mulLast l u) := by
  intro l
  induction l with
  | nil => intro _ a ha; simp [FreeProduct.mulLast] at ha
  | cons c cs ih =>
    cases cs with
    | nil =>
      intro h a ha
      rw [FreeProduct.mulLast] at ha
      rcases List.mem_singleton.mp ha with rfl
      exact ⟨actR_ne_zero.mpr (h c (by simp)).1,
        by rw [treeOfRat_actR]; exact (h c (by simp)).2⟩
    | cons d ds =>
      intro h a ha
      rw [FreeProduct.mulLast] at ha
      rcases List.mem_cons.mp ha with hh | ha
      · rw [hh]; exact h c (by simp)
      · exact ih (fun y hy => h y (List.mem_cons_of_mem c hy)) a ha

/-- The single-letter list `[y]` is good for the bound `Tree (y⋄) = exp (exp (Tree y))`. -/
theorem listGood_rat_singleton {y : RatU U} (hy : y ≠ 0) :
    ListGood (Rat.treeOfRat U (RatU.rational.ratOp y)) [y] := by
  intro a ha
  rw [List.mem_singleton] at ha
  rw [ha]
  exact ⟨hy, by rw [Rat.treeOfRat_rat_rational hy]; exact RatU.tree_lt_exp_exp _⟩

/-! ### The provenance of `Psi` on words -/

/-- **The letter decomposition of a word**, in the form used for the induction: the normal form of
`Psi x` on `U ♮ X` is either a group letter `Ugen u` (and then `x = ofGroup u`), or an `X`-letter
whose representative list consists of non-zero elements of complexity strictly below `Tree x`. -/
theorem isWord_prov {x : RatU U} (hx : RatU.IsWord x) :
    ∃ p : FreeProduct.NU U, FreeProduct.Psi x = MonoidAlgebra.single p 1 ∧
      ((∃ u : U, p = FreeProduct.NU.Ugen u ∧ x = RatU.ofGroup u) ∨
       (∃ L : FreeProduct.NEL (U := U),
          p = Sum.inr (Quotient.mk (FreeProduct.relNESetoid U) L) ∧
          ListGood (Rat.treeOfRat U x) L.1)) := by
  induction hx with
  | ofGroup u =>
      exact ⟨FreeProduct.NU.Ugen u, FreeProduct.Psi_ofGroup u, Or.inl ⟨u, rfl, rfl⟩⟩
  | rat y hy =>
      refine ⟨FreeProduct.NU.Xgen y, FreeProduct.Psi_ratOp hy, Or.inr ⟨⟨[y], by simp⟩, ?_, ?_⟩⟩
      · show (FreeProduct.NU.Xgen y : FreeProduct.NU U) =
          Sum.inr (Quotient.mk (FreeProduct.relNESetoid U) ⟨[y], by simp⟩)
        rfl
      · exact listGood_rat_singleton hy
  | mul ha hb iha ihb =>
      rename_i x y
      obtain ⟨pa, hpa, hprova⟩ := iha
      obtain ⟨pb, hpb, hprovb⟩ := ihb
      have hPsi : FreeProduct.Psi (x * y) = MonoidAlgebra.single (pa * pb) 1 := by
        rw [map_mul, hpa, hpb, MonoidAlgebra.single_mul_single, mul_one]
      rcases hprova with ⟨u, rfl, hxU⟩ | ⟨La, hpa', hLa⟩
      · -- `pa = Ugen u`
        rcases hprovb with ⟨v, rfl, hyU⟩ | ⟨Lb, hpb', hLb⟩
        · -- both factors are group letters
          exact ⟨FreeProduct.NU.Ugen (u * v), by rw [hPsi, FreeProduct.NU.Ugen_mul],
            Or.inl ⟨u * v, rfl, by rw [hxU, hyU, RatU.ofGroup_mul]⟩⟩
        · -- a group letter times an `X`-letter
          refine ⟨Sum.inr (Quotient.mk (FreeProduct.relNESetoid U)
              ⟨FreeProduct.mulFirst u Lb.1, FreeProduct.mulFirst_ne_nil u Lb.2⟩), ?_,
            Or.inr ⟨⟨FreeProduct.mulFirst u Lb.1, FreeProduct.mulFirst_ne_nil u Lb.2⟩, rfl,
              ?_⟩⟩
          · rw [hPsi, hpb', FreeProduct.NU.Ugen_mul_mk]
          · rw [hxU, RatU.treeOfRat_ofGroup_mul]
            exact hLb.mulFirst u
      · -- `pa = Xgen …`
        rcases hprovb with ⟨v, rfl, hyU⟩ | ⟨Lb, hpb', hLb⟩
        · -- an `X`-letter times a group letter
          refine ⟨Sum.inr (Quotient.mk (FreeProduct.relNESetoid U)
              ⟨FreeProduct.mulLast La.1 v, FreeProduct.mulLast_ne_nil v La.2⟩), ?_,
            Or.inr ⟨⟨FreeProduct.mulLast La.1 v, FreeProduct.mulLast_ne_nil v La.2⟩, rfl,
              ?_⟩⟩
          · rw [hPsi, hpa', FreeProduct.NU.mk_mul_Ugen]
          · rw [hyU, RatU.treeOfRat_mul_ofGroup]
            exact hLa.mulLast v
        · -- two `X`-letters: the lists are concatenated
          refine ⟨Sum.inr (Quotient.mk (FreeProduct.relNESetoid U)
              ⟨La.1 ++ Lb.1, by simp [La.2]⟩), ?_,
            Or.inr ⟨⟨La.1 ++ Lb.1, by simp [La.2]⟩, rfl, ?_⟩⟩
          · rw [hPsi, hpa', hpb', FreeProduct.NU.mk_mul_mk]
          · rw [Rat.treeOfRat_mul]
            refine ListGood.append hLa hLb ?_ ?_
            · exact Rat.treeOrderFacts.2.1 _ _ (treeOfRat_isWord_ne_zero ha)
                (treeOfRat_isWord_ne_zero hb)
            · rw [Tree.mul_comm]
              exact Rat.treeOrderFacts.2.1 _ _ (treeOfRat_isWord_ne_zero hb)
                (treeOfRat_isWord_ne_zero ha)

end IsWordLetterDecomp

set_option linter.unusedVariables false in
theorem isWord_letter_decomp {U : Type} [Group U] (x : Work.ORHughesFree.RatU U)
    (hx : Work.ORHughesFree.RatU.IsWord x) (hx0 : x ≠ 0) :
    (∃ u : U, x = Work.ORHughesFree.RatU.ofGroup u) ∨
      (∃ l : List (Work.ORHughesFree.RatU U), ∃ hl : l ≠ [],
        (∀ y ∈ l, y ≠ 0 ∧ Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U y)
          (Work.ORHughesFree.Rat.treeOfRat U x)) ∧
        Work.ORHughesFree.Rat.FreeProduct.Psi x =
          MonoidAlgebra.single (Sum.inr (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U)
            ⟨l, hl⟩) : Work.ORHughesFree.Rat.FreeProduct.NU U) 1) := by
  obtain ⟨p, hp, hprov⟩ := IsWordLetterDecomp.isWord_prov hx
  rcases hprov with ⟨u, rfl, hxU⟩ | ⟨L, hpL, hL⟩
  · exact Or.inl ⟨u, hxU⟩
  · exact Or.inr ⟨L.1, L.2, hL, by rw [hp, hpL]⟩

end Work.ORHughesFree.Rat.Dich
