/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The four-way decomposition of a non-zero element of `Rat(U)`

[JZLA20, Proposition 5.1] is proved by induction on the complexity `Tree x` of an element
`x ∈ Rat(U) \ {0}`.  The induction step rests on the following four-way case distinction on `x`:

* `x = ofGroup u` is the image of a group element (the base case);
* `x = y * z` with `y`, `z` *words* of strictly smaller complexity (the product case);
* `x = y + z` with `y`, `z ≠ 0` of strictly smaller complexity (the sum case);
* `x = y⋄` with `Tree y < Tree x` (the rational-operation case).

An element of `Rat(U) = ℕ[U ♮ X] \ {0}` is a finite sum of words ([JZLA20, §4.2]; in the term
model this is `RatU.isWord_sum_decomp`), so if the sum has at least two terms the sum case
applies; if it has a single term `w` then `x = w` is a word, and a word is decomposed by
`RatU.word_decomp`: a product of two words of strictly smaller complexity, or a `⋄`, or a group
element.

The strictness of the complexity in the product case is the delicate point, and it is where the
identities `(t ⋄) v = (v⁻¹ t)⋄` and `u (t ⋄) = (t u⁻¹)⋄` — direct consequences of the axiom
`(u r v)⋄ = v⁻¹ r⋄ u⁻¹` (`RationalUSemiring.rat_smul`) — are used: they allow a group element
sitting next to a `⋄` to be absorbed into the argument of the `⋄`, so that a word whose only
"non-trivial" factor is a single `⋄` is itself of the form `y⋄`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.Word
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.ratComplexity_model
import Submission.Work.ORHughesFree.Rat.treeOrderFacts
import Submission.Work.ORHughesFree.Tree.Log
import Submission.Work.ORHughesFree.Tree.lt_exp_exp
import Submission.Work.ORHughesFree.RatU.add_eq_zero_iff
import Submission.Work.ORHughesFree.RatU.mul_ne_zero

set_option autoImplicit false

namespace Work.ORHughesFree.RatU

open Work.ORHughesFree

variable {U : Type} [Group U]

/-! ### Two consequences of the rational axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` -/

/-- The axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` with `u = v⁻¹`, `v = 1`: a group element to the right of a
`⋄` is absorbed into the argument of the `⋄`. -/
theorem ratOp_mul_ofGroup (t : RatU U) (v : U) :
    RatU.rational.ratOp t * ofGroup v = RatU.rational.ratOp (ofGroup v⁻¹ * t) := by
  have h := (RatU.rational (U := U)).rat_smul v⁻¹ 1 t
  change RatU.ratOp (RatU.smul v⁻¹ (RatU.smulRight t 1)) =
    RatU.smulRight (RatU.smul 1⁻¹ (RatU.ratOp t)) (v⁻¹)⁻¹ at h
  simp only [RatU.smul_eq_ofGroup_mul, RatU.smulRight_eq_mul_ofGroup, RatU.ofGroup_one,
    inv_one, one_mul, mul_one, inv_inv] at h
  exact h.symm

/-- The axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` with `u = 1`, `v = u⁻¹`: a group element to the left of a
`⋄` is absorbed into the argument of the `⋄`. -/
theorem ofGroup_mul_ratOp (u : U) (t : RatU U) :
    ofGroup u * RatU.rational.ratOp t = RatU.rational.ratOp (t * ofGroup u⁻¹) := by
  have h := (RatU.rational (U := U)).rat_smul 1 u⁻¹ t
  change RatU.ratOp (RatU.smul 1 (RatU.smulRight t u⁻¹)) =
    RatU.smulRight (RatU.smul (u⁻¹)⁻¹ (RatU.ratOp t)) 1⁻¹ at h
  simp only [RatU.smul_eq_ofGroup_mul, RatU.smulRight_eq_mul_ofGroup, RatU.ofGroup_one,
    inv_one, one_mul, mul_one, inv_inv] at h
  exact h.symm

/-! ### Multiplying by the image of a group element does not change the complexity -/

theorem treeOfRat_ofGroup_mul (u : U) (a : RatU U) :
    Rat.treeOfRat U (ofGroup u * a) = Rat.treeOfRat U a := by
  rw [Rat.treeOfRat_mul, Rat.treeOfRat_ofGroup, one_mul]

theorem treeOfRat_mul_ofGroup (a : RatU U) (u : U) :
    Rat.treeOfRat U (a * ofGroup u) = Rat.treeOfRat U a := by
  rw [Rat.treeOfRat_mul, Rat.treeOfRat_ofGroup, mul_one]

/-! ### Strict comparison of the complexity -/

/-- Every tree is strictly below its double root extension.  This is `Tree.lt_exp_exp` except
that the hypothesis `x ≠ 0` is dropped: for `x = 0` the statement is `0 < exp 1`, which holds
because `exp 1 ≠ 0`. -/
theorem tree_lt_exp_exp (x : Tree) : Tree.lt x (Tree.exp (Tree.exp x)) := by
  by_cases h : x = 0
  · subst h
    exact Tree.lt_of_le_of_ne (Tree.le_zero _) (Ne.symm (Tree.exp_ne_zero _))
  · exact Tree.lt_exp_exp h

/-- The complexity of a product strictly exceeds that of its left factor, when the right factor
is a word of complexity `≠ 1` (i.e. is not the image of a group element). -/
theorem tree_lt_mul_left {a b : RatU U} (ha : a ≠ 0) (hb : b ≠ 0)
    (hb1 : Rat.treeOfRat U b ≠ 1) :
    Tree.lt (Rat.treeOfRat U a) (Rat.treeOfRat U (a * b)) := by
  have hta : Rat.treeOfRat U a ≠ 0 := fun h => ha ((Rat.treeOfRat_eq_zero_iff U a).mp h)
  have htb : Rat.treeOfRat U b ≠ 0 := fun h => hb ((Rat.treeOfRat_eq_zero_iff U b).mp h)
  have hle := Rat.treeOrderFacts.2.1 (Rat.treeOfRat U a) (Rat.treeOfRat U b) hta htb
  rw [Rat.treeOfRat_mul]
  exact Tree.lt_of_le_of_ne hle
    (fun h => hb1 ((Rat.treeOrderFacts.2.2 _ _ hta htb).mp h.symm))

/-- The complexity of a product strictly exceeds that of its right factor, when the left factor
is a word of complexity `≠ 1`. -/
theorem tree_lt_mul_right {a b : RatU U} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : Rat.treeOfRat U a ≠ 1) :
    Tree.lt (Rat.treeOfRat U b) (Rat.treeOfRat U (a * b)) := by
  have hta : Rat.treeOfRat U a ≠ 0 := fun h => ha ((Rat.treeOfRat_eq_zero_iff U a).mp h)
  have htb : Rat.treeOfRat U b ≠ 0 := fun h => hb ((Rat.treeOfRat_eq_zero_iff U b).mp h)
  rw [Rat.treeOfRat_mul, Tree.mul_comm]
  exact Tree.lt_of_le_of_ne (Rat.treeOrderFacts.2.1 _ _ htb hta)
    (fun h => ha1 ((Rat.treeOrderFacts.2.2 _ _ htb hta).mp h.symm))

/-- The complexity of a sum strictly exceeds that of its left summand, when the right summand is
non-zero. -/
theorem tree_lt_add_left {a b : RatU U} (hb : b ≠ 0) :
    Tree.lt (Rat.treeOfRat U a) (Rat.treeOfRat U (a + b)) := by
  rw [Rat.treeOfRat_add]
  refine Tree.lt_of_le_of_ne ?_ ?_
  · simpa using Tree.le_add (Tree.le_refl (Rat.treeOfRat U a)) (Tree.le_zero (Rat.treeOfRat U b))
  · intro h
    exact hb ((Rat.treeOfRat_eq_zero_iff U b).mp ((Tree.add_eq_self_iff _ _).mp h.symm))

/-- The complexity of a sum strictly exceeds that of its right summand, when the left summand is
non-zero. -/
theorem tree_lt_add_right {a b : RatU U} (ha : a ≠ 0) :
    Tree.lt (Rat.treeOfRat U b) (Rat.treeOfRat U (a + b)) := by
  rw [Rat.treeOfRat_add, Tree.add_comm]
  refine Tree.lt_of_le_of_ne ?_ ?_
  · simpa using Tree.le_add (Tree.le_refl (Rat.treeOfRat U b)) (Tree.le_zero (Rat.treeOfRat U a))
  · intro h
    exact ha ((Rat.treeOfRat_eq_zero_iff U a).mp ((Tree.add_eq_self_iff _ _).mp h.symm))

/-! ### Words: non-vanishing, sums, and the one-word decomposition -/

/-- A word of `Rat(U)` is non-zero. -/
theorem isWord_ne_zero' {x : RatU U} (h : IsWord x) : x ≠ 0 := by
  induction h with
  | ofGroup u =>
    intro h0
    have h1 : Rat.treeOfRat U (ofGroup u) = 0 := by rw [h0, Rat.treeOfRat_zero]
    rw [Rat.treeOfRat_ofGroup] at h1
    exact Tree.one_ne_zero h1
  | mul hx hy ihx ihy => exact RatU.mul_ne_zero ihx ihy
  | rat y hy =>
    intro h0
    have h1 : Rat.treeOfRat U (RatU.rational.ratOp y) = 0 := by rw [h0, Rat.treeOfRat_zero]
    rw [Rat.treeOfRat_rat_rational hy] at h1
    exact Tree.exp_ne_zero _ h1

/-- A non-empty sum of non-zero elements of `Rat(U)` is non-zero (`Rat(U)` has no additive zero
divisors, `RatU.add_eq_zero_iff`). -/
theorem list_sum_ne_zero {l : List (RatU U)} (hl : ∀ w ∈ l, w ≠ 0) (hne : l ≠ []) :
    l.sum ≠ 0 := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    rw [List.sum_cons]
    cases t with
    | nil => simpa using hl a List.mem_cons_self
    | cons b t' =>
      intro h
      obtain ⟨ha, ht⟩ := (RatU.add_eq_zero_iff a ((b :: t').sum)).mp h
      exact ih (fun w hw => hl w (List.mem_cons_of_mem a hw)) (by simp) ht

/-- Every element of `Rat(U)` is a finite sum of words.  (This is the version
`RatU.isWord_sum_decomp` of `Submission/Work/ORHughesFree/RatU/isWord_sum_decomp.lean`; it is
reproved here in a form that is available to the proof below without importing that module.) -/
theorem exists_word_sum (x : RatU U) :
    ∃ l : List (RatU U), (∀ w ∈ l, IsWord w) ∧ x = l.sum := by
  refine Quotient.inductionOn x ?_
  intro t
  show ∃ l : List (RatU U), (∀ w ∈ l, IsWord w) ∧ RatU.mk t = l.sum
  induction t with
  | z => exact ⟨[], by simp [RatU.mk_zero]⟩
  | o =>
    refine ⟨[ofGroup (1 : U)], ?_, ?_⟩
    · intro w hw
      obtain rfl := List.mem_singleton.mp hw
      exact IsWord.ofGroup 1
    · simp [RatU.mk_one, ofGroup_one]
  | add a b iha ihb =>
    obtain ⟨la, hla, ha⟩ := iha
    obtain ⟨lb, hlb, hb⟩ := ihb
    refine ⟨la ++ lb, ?_, ?_⟩
    · intro w hw
      rw [List.mem_append] at hw
      exact hw.elim (hla w) (hlb w)
    · rw [RatU.mk_add, ha, hb, List.sum_append]
  | mul a b iha ihb =>
    obtain ⟨la, hla, ha⟩ := iha
    obtain ⟨lb, hlb, hb⟩ := ihb
    refine ⟨la.flatMap fun w₁ => lb.map fun w₂ => w₁ * w₂, ?_, ?_⟩
    · intro w hw
      rw [List.mem_flatMap] at hw
      obtain ⟨w₁, hw₁, hw⟩ := hw
      rw [List.mem_map] at hw
      obtain ⟨w₂, hw₂, rfl⟩ := hw
      exact IsWord.mul (hla w₁ hw₁) (hlb w₂ hw₂)
    · rw [RatU.mk_mul, ha, hb]
      have key : ∀ (la lb : List (RatU U)),
          (la.flatMap fun a => lb.map fun b => a * b).sum = la.sum * lb.sum := by
        intro la lb
        have hflat : ∀ (l : List (RatU U)) (f : RatU U → List (RatU U)),
            (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
          intro l f
          induction l with
          | nil => simp
          | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]
        rw [hflat]
        have h1 : ∀ a : RatU U, (lb.map fun b => a * b).sum = a * lb.sum := by
          intro a
          rw [List.sum_map_mul_left]; simp
        rw [show (la.map fun a => (lb.map fun b => a * b).sum) = (la.map fun a => a * lb.sum)
          from List.map_congr_left (fun a _ => h1 a)]
        rw [List.sum_map_mul_right]; simp
      exact (key la lb).symm
  | rat a _iha =>
    by_cases ha : (RatU.mk a : RatU U) = 0
    · refine ⟨[], by simp, ?_⟩
      rw [RatU.mk_rat, ha, RatU.ratOp_zero]; simp
    · refine ⟨[RatU.rational.ratOp (RatU.mk a)], ?_, ?_⟩
      · intro w hw
        obtain rfl := List.mem_singleton.mp hw
        exact IsWord.rat _ ha
      · rw [RatU.mk_rat, List.sum_singleton]; rfl
  | smulL u a iha =>
    obtain ⟨la, hla, ha⟩ := iha
    refine ⟨la.map fun w => ofGroup u * w, ?_, ?_⟩
    · intro w hw
      rw [List.mem_map] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      exact IsWord.mul (IsWord.ofGroup u) (hla w₀ hw₀)
    · rw [RatU.mk_smulL, RatU.smul_eq_ofGroup_mul, ha, List.sum_map_mul_left]; simp
  | smulR u a iha =>
    obtain ⟨la, hla, ha⟩ := iha
    refine ⟨la.map fun w => w * ofGroup u, ?_, ?_⟩
    · intro w hw
      rw [List.mem_map] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      exact IsWord.mul (hla w₀ hw₀) (IsWord.ofGroup u)
    · rw [RatU.mk_smulR, RatU.smulRight_eq_mul_ofGroup, ha, List.sum_map_mul_right]; simp

/-- **A word decomposes.**  A word of `Rat(U)` is either the image of a group element, or a
product of two words of strictly smaller complexity, or the `⋄` of an element of strictly smaller
complexity.

The proof is by induction on the generation of `IsWord`.  In the product case `w = x * y`, if
both `x` and `y` have complexity `≠ 1` the factorisation `(x, y)` itself has both factors of
strictly smaller complexity (`tree_lt_mul_left`, `tree_lt_mul_right`).  If `x` is the image of a
group element, `Tree (x * y) = Tree y`, and the decomposition of `y` is transported across the
multiplication by `x` — the only non-trivial sub-case being `y = t⋄`, where `x · t⋄ = (t x⁻¹)⋄`
(`ofGroup_mul_ratOp`); the case `y ∈ U` is symmetric, using `t⋄ · y = (y⁻¹ t)⋄`
(`ratOp_mul_ofGroup`). -/
theorem word_decomp (w : RatU U) (hw : IsWord w) :
    (∃ u : U, w = ofGroup u) ∨
    (∃ y z : RatU U, w = y * z ∧ IsWord y ∧ IsWord z ∧
      Tree.lt (Rat.treeOfRat U y) (Rat.treeOfRat U w) ∧
      Tree.lt (Rat.treeOfRat U z) (Rat.treeOfRat U w)) ∨
    (∃ y : RatU U, w = RatU.rational.ratOp y ∧
      Tree.lt (Rat.treeOfRat U y) (Rat.treeOfRat U w)) := by
  induction hw with
  | ofGroup u => exact Or.inl ⟨u, rfl⟩
  | rat y hy =>
    exact Or.inr (Or.inr ⟨y, rfl, by rw [Rat.treeOfRat_rat_rational hy]; exact tree_lt_exp_exp _⟩)
  | mul hx hy ihx ihy =>
    rename_i x y
    by_cases hxU : ∃ u : U, x = ofGroup u
    · obtain ⟨u, rfl⟩ := hxU
      by_cases hyU : ∃ v : U, y = ofGroup v
      · obtain ⟨v, rfl⟩ := hyU
        exact Or.inl ⟨u * v, by rw [ofGroup_mul]⟩
      · rcases ihy with h | ⟨y1, y2, hy12, hy1, hy2, hlt1, hlt2⟩ | ⟨t, ht, hlt⟩
        · exact absurd h hyU
        · refine Or.inr (Or.inl ⟨ofGroup u * y1, y2, ?_,
            IsWord.mul (IsWord.ofGroup u) hy1, hy2, ?_, ?_⟩)
          · rw [hy12, mul_assoc]
          · simp only [treeOfRat_ofGroup_mul]; exact hlt1
          · simp only [treeOfRat_ofGroup_mul]; exact hlt2
        · refine Or.inr (Or.inr ⟨t * ofGroup u⁻¹, ?_, ?_⟩)
          · rw [ht, ofGroup_mul_ratOp]
          · simp only [treeOfRat_mul_ofGroup, treeOfRat_ofGroup_mul]; exact hlt
    · by_cases hyU : ∃ v : U, y = ofGroup v
      · obtain ⟨v, rfl⟩ := hyU
        rcases ihx with h | ⟨x1, x2, hx12, hx1, hx2, hlt1, hlt2⟩ | ⟨t, ht, hlt⟩
        · exact absurd h hxU
        · refine Or.inr (Or.inl ⟨x1, x2 * ofGroup v, ?_, hx1,
            IsWord.mul hx2 (IsWord.ofGroup v), ?_, ?_⟩)
          · rw [hx12, mul_assoc]
          · simp only [treeOfRat_mul_ofGroup]; exact hlt1
          · simp only [treeOfRat_mul_ofGroup]; exact hlt2
        · refine Or.inr (Or.inr ⟨ofGroup v⁻¹ * t, ?_, ?_⟩)
          · rw [ht, ratOp_mul_ofGroup]
          · simp only [treeOfRat_ofGroup_mul, treeOfRat_mul_ofGroup]; exact hlt
      · have hx0 : x ≠ 0 := isWord_ne_zero' hx
        have hy0 : y ≠ 0 := isWord_ne_zero' hy
        have hx1 : Rat.treeOfRat U x ≠ 1 := fun h => hxU ((Rat.treeOfRat_eq_one_iff x).mp h)
        have hy1 : Rat.treeOfRat U y ≠ 1 := fun h => hyU ((Rat.treeOfRat_eq_one_iff y).mp h)
        exact Or.inr (Or.inl ⟨x, y, rfl, hx, hy,
          tree_lt_mul_left hx0 hy0 hy1, tree_lt_mul_right hx0 hy0 hx1⟩)

theorem exists_decomp {U : Type} [Group U] (x : Work.ORHughesFree.RatU U) (hx : x ≠ 0) :
    (∃ u : U, x = Work.ORHughesFree.RatU.ofGroup u) ∨
    (∃ y z : Work.ORHughesFree.RatU U, x = y * z ∧ Work.ORHughesFree.RatU.IsWord y ∧
      Work.ORHughesFree.RatU.IsWord z ∧
      Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U y)
        (Work.ORHughesFree.Rat.treeOfRat U x) ∧
      Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U z)
        (Work.ORHughesFree.Rat.treeOfRat U x)) ∨
    (∃ y z : Work.ORHughesFree.RatU U, x = y + z ∧ y ≠ 0 ∧ z ≠ 0 ∧
      Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U y)
        (Work.ORHughesFree.Rat.treeOfRat U x) ∧
      Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U z)
        (Work.ORHughesFree.Rat.treeOfRat U x)) ∨
    (∃ y : Work.ORHughesFree.RatU U, x = Work.ORHughesFree.RatU.rational.ratOp y ∧
      Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U y)
        (Work.ORHughesFree.Rat.treeOfRat U x)) := by
  obtain ⟨l, hl, hxl⟩ := exists_word_sum x
  rcases l with _ | ⟨w, t⟩
  · rw [List.sum_nil] at hxl
    exact absurd hxl hx
  · rcases t with _ | ⟨w2, t'⟩
    · -- a single word
      have hxw : x = w := by rw [List.sum_singleton] at hxl; exact hxl
      rcases word_decomp w (hl w (by simp)) with
        ⟨u, hu⟩ | ⟨y, z, hyz, hwy, hwz, hlt1, hlt2⟩ | ⟨y, hy, hlt⟩
      · exact Or.inl ⟨u, by rw [hxw, hu]⟩
      · refine Or.inr (Or.inl ⟨y, z, ?_, hwy, hwz, ?_, ?_⟩)
        · rw [hxw, hyz]
        · rw [hxw]; exact hlt1
        · rw [hxw]; exact hlt2
      · exact Or.inr (Or.inr (Or.inr ⟨y, by rw [hxw, hy], by rw [hxw]; exact hlt⟩))
    · -- a sum of at least two words
      rw [List.sum_cons] at hxl
      have hw : IsWord w := hl w (by simp)
      have hz : (w2 :: t').sum ≠ 0 :=
        list_sum_ne_zero (fun v hv => isWord_ne_zero' (hl v (List.mem_cons_of_mem w hv))) (by simp)
      refine Or.inr (Or.inr (Or.inl ⟨w, (w2 :: t').sum, hxl, isWord_ne_zero' hw, hz, ?_, ?_⟩))
      · rw [hxl]; exact tree_lt_add_left hz
      · rw [hxl]; exact tree_lt_add_right (isWord_ne_zero' hw)

end Work.ORHughesFree.RatU
