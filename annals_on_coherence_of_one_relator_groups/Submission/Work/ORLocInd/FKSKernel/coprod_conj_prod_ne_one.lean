import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreeDefs

/-!
# Non-triviality of a product of conjugates in a free product

Let `M : ι → Type*` be a family of groups and let `P = Monoid.CoprodI M` be their free
product.  Given two distinct indices `i ≠ j` and a non-empty list `l : List (M i × M j)`
such that

* the second component of every element of `l` is non-trivial, and
* consecutive elements of `l` have distinct first components,

we prove that the product `∏ (a, b) ∈ l, of a * of b * (of a)⁻¹` is a non-trivial element
of `P`.

The proof builds the reduced letter list of this element.  Writing
`l = [(a₁,b₁), …, (aₙ,bₙ)]`, the element is the product of the letters

`of a₁, of b₁, (of a₁)⁻¹, of a₂, of b₂, (of a₂)⁻¹, …, (of aₙ)⁻¹`.

Merging the adjacent `M i`-letters `(of a_k)⁻¹` and `of a_{k+1}` into the single letter
`of (a_k⁻¹ a_{k+1})` produces the alternating list

`of a₁, of b₁, of (a₁⁻¹a₂), of b₂, …, of bₙ, (of aₙ)⁻¹`.

The middle letters are automatically non-trivial (because of the chain condition), and the
only letters that can vanish are the first and the last one; they are simply omitted.  The
resulting list is a non-empty reduced word, so its product is non-trivial by
`letters_prod_ne_one`.
-/

open Classical

namespace Work.ORLocInd.FKSKernel

universe u

/-- Auxiliary letter list.  Given an element `prev : M i` and a list `t : List (M i × M j)`,
`lettersAux prev t` is the list of letters of the reduced word of
`(of prev)⁻¹ * ∏ (a,b) ∈ t, of a * of b * (of a)⁻¹`,
starting with the `M i`-letter obtained by merging the pending `prev` with the first
component of the head of `t`.  If `t` is empty, the only letter is the closing
`M i`-letter `(of prev)⁻¹`, which is omitted when it is trivial. -/
noncomputable def lettersAux {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] (i j : ι)
    (prev : M i) : List (M i × M j) → List (Σ k : ι, M k)
  | [] => if prev = 1 then [] else [⟨i, prev⁻¹⟩]
  | (a, b) :: t => ⟨i, prev⁻¹ * a⟩ :: ⟨j, b⟩ :: lettersAux M i j a t

/-- The reduced letter list of the element `∏ (a,b) ∈ l, of a * of b * (of a)⁻¹`. -/
noncomputable def letters {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] (i j : ι) :
    List (M i × M j) → List (Σ k : ι, M k)
  | [] => []
  | (a, b) :: t =>
      if a = 1 then ⟨j, b⟩ :: lettersAux M i j a t
      else ⟨i, a⟩ :: ⟨j, b⟩ :: lettersAux M i j a t

@[simp] lemma lettersAux_nil {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] (i j : ι)
    (prev : M i) :
    lettersAux M i j prev ([] : List (M i × M j)) =
      (if prev = 1 then [] else [⟨i, prev⁻¹⟩]) := rfl

@[simp] lemma lettersAux_cons {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] (i j : ι)
    (prev a : M i) (b : M j) (t : List (M i × M j)) :
    lettersAux M i j prev ((a, b) :: t) =
      ⟨i, prev⁻¹ * a⟩ :: ⟨j, b⟩ :: lettersAux M i j a t := rfl

@[simp] lemma letters_nil {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] (i j : ι) :
    letters M i j ([] : List (M i × M j)) = [] := rfl

@[simp] lemma letters_cons {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] (i j : ι)
    (a : M i) (b : M j) (t : List (M i × M j)) :
    letters M i j ((a, b) :: t) =
      (if a = 1 then ⟨j, b⟩ :: lettersAux M i j a t
       else ⟨i, a⟩ :: ⟨j, b⟩ :: lettersAux M i j a t) := rfl

/-- `of` of the letters of `lettersAux prev t` multiplies to `(of prev)⁻¹` times the product
defining the target element for `t`. -/
lemma lettersAux_prod {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] {i j : ι}
    (t : List (M i × M j)) (prev : M i) :
    ((lettersAux M i j prev t).map (fun x => Monoid.CoprodI.of x.2)).prod
      = (Monoid.CoprodI.of prev)⁻¹ *
        ((t.map (fun x => Monoid.CoprodI.of x.1 * Monoid.CoprodI.of x.2 *
          (Monoid.CoprodI.of x.1)⁻¹)).prod) := by
  induction t generalizing prev with
  | nil =>
      by_cases h : prev = 1
      · subst h
        simp
      · simp [lettersAux, h]
  | cons hd t ih =>
      obtain ⟨a, b⟩ := hd
      rw [lettersAux_cons]
      simp only [List.map_cons, List.prod_cons]
      rw [ih a]
      simp only [map_mul, map_inv]
      group

/-- `of` of the letters of `letters` multiplies to the target element. -/
lemma letters_prod {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] {i j : ι}
    (l : List (M i × M j)) :
    ((letters M i j l).map (fun x => Monoid.CoprodI.of x.2)).prod
      = (l.map (fun x => Monoid.CoprodI.of x.1 * Monoid.CoprodI.of x.2 *
          (Monoid.CoprodI.of x.1)⁻¹)).prod := by
  cases l with
  | nil => simp
  | cons hd t =>
      obtain ⟨a, b⟩ := hd
      by_cases ha : a = 1
      · rw [letters_cons, if_pos ha]
        simp only [List.map_cons, List.prod_cons]
        rw [lettersAux_prod M t a, ha]
        simp
      · rw [letters_cons, if_neg ha]
        simp only [List.map_cons, List.prod_cons]
        rw [lettersAux_prod M t a]
        group

/-- If `x ≠ y` then `x⁻¹ * y ≠ 1`. -/
lemma inv_mul_ne_one_of_ne {G : Type*} [Group G] {x y : G} (h : x ≠ y) : x⁻¹ * y ≠ 1 := by
  intro hh
  apply h
  have h2 := congrArg (fun z => x * z) hh
  simpa [mul_assoc] using h2.symm

/-- The letter list `lettersAux prev t` is reduced (no letter equal to `1`) and alternating,
it starts with an `M i`-letter, provided the "pending" letter `prev` differs from the first
component of the head of `t` and the list `t` satisfies the same hypotheses as in the main
statement. -/
lemma lettersAux_spec {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)] {i j : ι}
    (hij : i ≠ j) :
    ∀ (t : List (M i × M j)) (prev : M i),
      (∀ x ∈ t, x.2 ≠ 1) → t.IsChain (fun x y => x.1 ≠ y.1) →
      (∀ hd, t.head? = some hd → prev ≠ hd.1) →
      (∀ x ∈ lettersAux M i j prev t, x.2 ≠ 1) ∧
      (lettersAux M i j prev t).IsChain (fun x y : Σ k : ι, M k => x.1 ≠ y.1) ∧
      (∀ hd : Σ k : ι, M k, (lettersAux M i j prev t).head? = some hd → hd.1 = i) := by
  intro t
  induction t with
  | nil =>
      intro prev hne hch hlink
      by_cases h : prev = 1
      · subst h
        refine ⟨by intro x hx; simp at hx, by simp, ?_⟩
        intro hd hdhd
        simp at hdhd
      · refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rw [lettersAux_nil, if_neg h, List.mem_singleton] at hx
          subst hx
          simpa using h
        · rw [lettersAux_nil, if_neg h]
          exact List.isChain_singleton _
        · intro hd hdhd
          rw [lettersAux_nil, if_neg h, List.head?_cons, Option.some.injEq] at hdhd
          subst hdhd
          rfl
  | cons hd t ih =>
      intro prev hne hch hlink
      obtain ⟨a, b⟩ := hd
      have hne_t : ∀ x ∈ t, x.2 ≠ 1 := fun x hx => hne x (List.mem_cons_of_mem _ hx)
      obtain ⟨hc1, hc2⟩ := List.isChain_cons.mp hch
      have hpa : prev ≠ a := hlink (a, b) rfl
      obtain ⟨A1, A2, A3⟩ := ih a hne_t hc2 hc1
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [lettersAux_cons, List.mem_cons] at hx
        rcases hx with h1 | h2 | h3
        · subst h1
          exact inv_mul_ne_one_of_ne hpa
        · subst h2
          exact hne (a, b) (by simp)
        · exact A1 x h3
      · rw [lettersAux_cons]
        refine List.IsChain.cons (List.IsChain.cons A2 ?_) ?_
        · intro y hy
          rw [A3 y hy]
          exact Ne.symm hij
        · intro y hy
          simp only [List.head?_cons, Option.mem_some_iff] at hy
          subst hy
          exact hij
      · intro hd' hdhd
        rw [lettersAux_cons, List.head?_cons, Option.some.injEq] at hdhd
        subst hdhd
        rfl

theorem coprod_conj_prod_ne_one {ι : Type u} (M : ι → Type u) [∀ i, Group (M i)]
    {i j : ι} (hij : i ≠ j) (l : List (M i × M j)) (hl : l ≠ [])
    (hne : ∀ x ∈ l, x.2 ≠ 1) (hch : l.IsChain (fun x y => x.1 ≠ y.1)) :
    (l.map (fun x => Monoid.CoprodI.of x.1 * Monoid.CoprodI.of x.2 *
      (Monoid.CoprodI.of x.1)⁻¹)).prod ≠ 1 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons hd t =>
      obtain ⟨a, b⟩ := hd
      have hb : b ≠ 1 := hne (a, b) (by simp)
      have hne_t : ∀ x ∈ t, x.2 ≠ 1 := fun x hx => hne x (List.mem_cons_of_mem _ hx)
      obtain ⟨hlink, hchain_t⟩ := List.isChain_cons.mp hch
      obtain ⟨A1, A2, A3⟩ := lettersAux_spec M hij t a hne_t hchain_t hlink
      have hneL : ∀ x ∈ letters M i j ((a, b) :: t), x.2 ≠ 1 := by
        intro x hx
        by_cases ha : a = 1
        · rw [letters_cons, if_pos ha] at hx
          simp only [List.mem_cons] at hx
          rcases hx with h1 | h2
          · subst h1; exact hb
          · exact A1 x h2
        · rw [letters_cons, if_neg ha] at hx
          simp only [List.mem_cons] at hx
          rcases hx with h1 | h2 | h3
          · subst h1; exact ha
          · subst h2; exact hb
          · exact A1 x h3
      have hchainL : (letters M i j ((a, b) :: t)).IsChain
          (fun x y : Σ k : ι, M k => x.1 ≠ y.1) := by
        by_cases ha : a = 1
        · rw [letters_cons, if_pos ha]
          refine List.IsChain.cons A2 ?_
          intro y hy
          rw [A3 y hy]
          exact Ne.symm hij
        · rw [letters_cons, if_neg ha]
          refine List.IsChain.cons (List.IsChain.cons A2 ?_) ?_
          · intro y hy
            rw [A3 y hy]
            exact Ne.symm hij
          · intro y hy
            simp only [List.head?_cons, Option.mem_some_iff] at hy
            subst hy
            exact hij
      have hlen : letters M i j ((a, b) :: t) ≠ [] := by
        by_cases ha : a = 1
        · rw [letters_cons, if_pos ha]; simp
        · rw [letters_cons, if_neg ha]; simp
      have key := Work.ORLocInd.CoprodTree.letters_prod_ne_one hneL hchainL hlen
      rw [letters_prod M ((a, b) :: t)] at key
      exact key

end Work.ORLocInd.FKSKernel
