import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.AltList
import Submission.Work.ORBassSerre.CoprodTree.coprod_mk_injective_of_isReduced_univ

/-!
# Alternating lists in a free product have non-trivial product

Let `l = [x₀, x₁, …, x_{n-1}]` be a non-empty list of elements of `A ∗ B`, where `x_j` lies in the
factor prescribed by the alternating side sequence `sideAfter s j` and `x_j ≠ 1` for every `j`.
Then the product of `l` in `A ∗ B` is non-trivial.

The proof is the normal form theorem for free products.  For every `j` we choose the letter
`c_j ∈ A ⊕ B` with `letter c_j = x_j` (via `letterOf`, using the projection onto the relevant
factor); the resulting list `c` of letters is *reduced*: no letter is an identity (as `x_j ≠ 1`)
and consecutive letters lie in different factors (as consecutive sides are different).  If
`l.prod = 1` then `mk c = 1 = mk []`, so `coprod_mk_injective_of_isReduced_univ` forces `c = []`
and hence `l = []`, contradicting `l ≠ []`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORBassSerre.CoprodTree

open Monoid

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-! ## The side of a letter -/

/-- The factor in which a letter of the free product lies. -/
def sideOf {A : Type u} {B : Type v} : A ⊕ B → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

@[simp] theorem sideOf_inl {A : Type u} {B : Type v} (a : A) :
    sideOf (Sum.inl a : A ⊕ B) = true := rfl

@[simp] theorem sideOf_inr {A : Type u} {B : Type v} (b : B) :
    sideOf (Sum.inr b : A ⊕ B) = false := rfl

/-- Two letters of the free product lie in the same factor exactly when they are on the same
side. -/
theorem sameFactor_iff_sideOf {A : Type u} {B : Type v} (a b : A ⊕ B) :
    SameFactor a b ↔ sideOf a = sideOf b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [SameFactor, sideOf]

theorem not_sameFactor_iff_sideOf {A : Type u} {B : Type v} (a b : A ⊕ B) :
    ¬ SameFactor a b ↔ sideOf a ≠ sideOf b :=
  not_congr (sameFactor_iff_sideOf a b)

/-! ## The letter of an element of a factor -/

/-- A letter of `A ⊕ B` whose image in the free product is the given element `x` of the factor of
the side `s`. -/
noncomputable def letterOf : (s : Bool) → (x : Monoid.Coprod A B) →
    x ∈ sideFactor A B s → A ⊕ B
  | true, x, _ => Sum.inl (Monoid.Coprod.fst x)
  | false, x, _ => Sum.inr (Monoid.Coprod.snd x)

theorem letter_letterOf (s : Bool) (x : Monoid.Coprod A B) (hx : x ∈ sideFactor A B s) :
    letter (letterOf s x hx) = x := by
  cases s with
  | true =>
    rw [sideFactor_true] at hx
    obtain ⟨a, rfl⟩ := hx
    simp [letterOf]
  | false =>
    rw [sideFactor_false] at hx
    obtain ⟨b, rfl⟩ := hx
    simp [letterOf]

theorem sideOf_letterOf (s : Bool) (x : Monoid.Coprod A B) (hx : x ∈ sideFactor A B s) :
    sideOf (letterOf s x hx) = s := by
  cases s <;> rfl

/-! ## The list of letters of an alternating list -/

/-- The list of letters in `A ⊕ B` whose images under `letter` are the entries of `l`, each taken
on the side prescribed by `sideAfter s`. -/
noncomputable def letters (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j)) : List (A ⊕ B) :=
  List.ofFn fun j : Fin l.length => letterOf (sideAfter s j) (l.get j) (h j j.isLt)

theorem letters_eq (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j)) :
    letters s l h = List.ofFn (fun j : Fin l.length =>
      letterOf (sideAfter s j) (l.get j) (h j j.isLt)) := rfl

theorem letters_length (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j)) :
    (letters s l h).length = l.length := by
  rw [letters_eq, List.length_ofFn]

theorem letters_map_letter (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j)) :
    (letters s l h).map letter = l := by
  rw [letters_eq, List.map_ofFn]
  conv_rhs => rw [← List.ofFn_get l]
  congr 1
  funext j
  exact letter_letterOf (sideAfter s j) (l.get j) (h j j.isLt)

theorem letters_ne_one (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j))
    (hone : ∀ x ∈ l, x ≠ 1) :
    ∀ c ∈ letters s l h, c ≠ Sum.inl 1 ∧ c ≠ Sum.inr 1 := by
  intro c hc
  rw [letters_eq, List.mem_ofFn] at hc
  obtain ⟨j, hj⟩ := hc
  have hxj : l.get j ≠ 1 := hone _ (List.get_mem l j)
  have hletter : letter (letterOf (sideAfter s j) (l.get j) (h j j.isLt)) ≠ 1 := by
    rw [letter_letterOf]
    exact hxj
  rw [← hj]
  exact ⟨fun h1 => hletter (by rw [h1]; simp),
    fun h2 => hletter (by rw [h2]; simp)⟩

theorem letters_isChain (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j)) :
    (letters s l h).IsChain (fun a b : A ⊕ B => ¬ SameFactor a b) := by
  rw [letters_eq, List.isChain_ofFn]
  intro i hi
  rw [not_sameFactor_iff_sideOf, sideOf_letterOf, sideOf_letterOf]
  exact (sideAfter_ne s i).symm

theorem letters_isReduced (s : Bool) (l : List (Monoid.Coprod A B))
    (h : ∀ j (hj : j < l.length), l[j] ∈ sideFactor A B (sideAfter s j))
    (hone : ∀ x ∈ l, x ≠ 1) : IsReduced (letters s l h) :=
  ⟨letters_ne_one s l h hone, letters_isChain s l h⟩

/-! ## The class of a word is the product of its letters -/

theorem coprod_mk_eq_prod_letter {A : Type u} {B : Type v} [Group A] [Group B]
    (l : List (A ⊕ B)) :
    Monoid.Coprod.mk (FreeMonoid.ofList l) = (l.map letter).prod := by
  have h := Monoid.Coprod.lift_apply_mk (Monoid.Coprod.inl (M := A) (N := B))
    (Monoid.Coprod.inr (M := A) (N := B)) (FreeMonoid.ofList l)
  rw [Monoid.Coprod.lift_inl_inr] at h
  have h' : Monoid.Coprod.mk (FreeMonoid.ofList l) =
      FreeMonoid.lift (Sum.elim Monoid.Coprod.inl Monoid.Coprod.inr)
        (FreeMonoid.ofList l) := by
    simpa using h
  have hletter : (Sum.elim Monoid.Coprod.inl Monoid.Coprod.inr : A ⊕ B → Monoid.Coprod A B) =
      letter := by
    funext c
    cases c <;> rfl
  rw [h', FreeMonoid.lift_ofList, hletter]

/-! ## The main theorem -/

theorem altList_prod_ne_one {A : Type u} {B : Type v} [Group A] [Group B] (s : Bool) (l : List (Monoid.Coprod A B)) (hne : l ≠ []) (hmem : ∀ j (hj : j < l.length), l[j] ∈ Work.ORBassSerre.CoprodTree.sideFactor A B (Work.ORBassSerre.CoprodTree.sideAfter s j)) (hone : ∀ x ∈ l, x ≠ 1) : l.prod ≠ 1 := by
  intro hprod
  have hred : IsReduced (letters s l hmem) := letters_isReduced s l hmem hone
  have hlen : (letters s l hmem).length = l.length := letters_length s l hmem
  have hnil : letters s l hmem ≠ [] := by
    intro h0
    have h1 : (letters s l hmem).length = 0 := by rw [h0]; rfl
    rw [hlen] at h1
    exact hne (List.length_eq_zero_iff.mp h1)
  have hmk : Monoid.Coprod.mk (FreeMonoid.ofList (letters s l hmem)) =
      Monoid.Coprod.mk (FreeMonoid.ofList ([] : List (A ⊕ B))) := by
    rw [coprod_mk_eq_prod_letter, letters_map_letter, coprod_mk_eq_prod_letter]
    simpa using hprod
  exact hnil (coprod_mk_injective_of_isReduced_univ (l₁ := letters s l hmem) (l₂ := [])
    hred isReduced_nil hmk)

end Work.ORBassSerre.CoprodTree
