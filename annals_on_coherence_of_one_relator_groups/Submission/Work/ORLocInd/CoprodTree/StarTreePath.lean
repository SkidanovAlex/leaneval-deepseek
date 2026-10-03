/-
# Paths in the Bass--Serre tree of a free product: the state, the steps, and the invariant

This file sets up the bookkeeping used to prove that the graph `Vertex M` of
`Submission.Work.ORLocInd.CoprodTree.StarTreeDefs` is a tree, i.e. that it has no non-trivial
reduced closed path.

A path in the tree started at a vertex `vtx k g` is followed in the group: the *state* `stt k g p`
of a path `p` is the label of its last arrow (or `g` for the empty path).  The vertices of the tree
alternate between "central" vertices (`vtx none _`) and "leaf"/coset vertices (`vtx (some _) _`),
so the side of the endpoint of `p` is determined by the parity of `p.length` and by the starting
side `k`: this is the Boolean `isLeafSide k p.length`.

Whenever an arrow starts at a leaf vertex, the quotient of the states (the "step") lies in the
corresponding factor of the free product: these steps are the *letters* of the path, recorded in
`letters k g p` together with the index of the factor.  `llidx k g p` is the index of the last
letter.

The invariant `Inv k g p` collects everything a reduced path satisfies; it is established in
`StarTreeInv.lean` and used in `StarTreeTree.lean` to show that every reduced closed path is
trivial.
-/
import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreeDefs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CoprodTree

open Quiver
open Work.ORBassSerre
open Classical

variable {ι : Type u}

/-! ## The side of the endpoint -/

/-- The side of the vertex reached after `n` arrows from a vertex of side `k`: `true` if it is a
leaf (coset) vertex `vtx (some i) _`, `false` if it is a central vertex `vtx none _`. -/
def isLeafSide (k : Option ι) (n : ℕ) : Bool :=
  match k with
  | none => decide (n % 2 = 1)
  | some _ => decide (n % 2 = 0)

@[simp]
theorem isLeafSide_none (n : ℕ) : isLeafSide (none : Option ι) n = decide (n % 2 = 1) := rfl

@[simp]
theorem isLeafSide_some (i : ι) (n : ℕ) : isLeafSide (some i) n = decide (n % 2 = 0) := rfl

/-- The side alternates: after one more arrow we are on the other side. -/
theorem isLeafSide_succ (k : Option ι) (n : ℕ) :
    isLeafSide k (n + 1) = !isLeafSide k n := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn
  · have h1 : (n + 1) % 2 = 1 := by omega
    cases k <;> simp [isLeafSide, hn, h1]
  · have h1 : (n + 1) % 2 = 0 := by omega
    cases k <;> simp [isLeafSide, hn, h1]

/-! ## The state, the last index, the letters -/

/-- The state of a path started at `vtx k g`: the label of its last arrow, or `g` if the path is
empty. -/
def stt {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    {y : Vertex M} → Quiver.Path (vtx k g) y → Monoid.CoprodI M
  | _, .nil => g
  | _, Quiver.Path.cons p e => e.lbl

@[simp]
theorem stt_nil {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    stt k g (Quiver.Path.nil : Quiver.Path (vtx k g) (vtx k g)) = g := rfl

@[simp]
theorem stt_cons {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι} {g : Monoid.CoprodI M}
    {x y : Vertex M} (p : Quiver.Path (vtx k g) x) (e : x ⟶ y) :
    stt k g (p.cons e) = e.lbl := rfl

/-- The index of the last arrow of a path (if the path is non-empty). -/
def lidx {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    {y : Vertex M} → Quiver.Path (vtx k g) y → Option ι
  | _, .nil => none
  | _, Quiver.Path.cons p e => some e.idx

@[simp]
theorem lidx_nil {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    lidx k g (Quiver.Path.nil : Quiver.Path (vtx k g) (vtx k g)) = none := rfl

@[simp]
theorem lidx_cons {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι} {g : Monoid.CoprodI M}
    {x y : Vertex M} (p : Quiver.Path (vtx k g) x) (e : x ⟶ y) :
    lidx k g (p.cons e) = some e.idx := rfl

/-- The letters of a path started at `vtx k g`: the steps taken from leaf (coset) vertices,
together with the index of the factor in which they lie. -/
def letters {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    {y : Vertex M} → Quiver.Path (vtx k g) y → List (ι × Monoid.CoprodI M)
  | _, .nil => []
  | _, Quiver.Path.cons p e =>
      letters k g p ++
        (if h : isLeafSide k p.length = true then [(e.idx, (stt k g p)⁻¹ * e.lbl)] else [])

@[simp]
theorem letters_nil {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    letters k g (Quiver.Path.nil : Quiver.Path (vtx k g) (vtx k g)) = [] := rfl

theorem letters_cons {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι} {g : Monoid.CoprodI M}
    {x y : Vertex M} (p : Quiver.Path (vtx k g) x) (e : x ⟶ y) :
    letters k g (p.cons e) = letters k g p ++
      (if h : isLeafSide k p.length = true then [(e.idx, (stt k g p)⁻¹ * e.lbl)]
        else []) := rfl

/-- The index of the last letter of a path (if the path has a letter). -/
def llidx {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    {y : Vertex M} → Quiver.Path (vtx k g) y → Option ι
  | _, .nil => none
  | _, Quiver.Path.cons p e =>
      if h : isLeafSide k p.length = true then some e.idx else llidx k g p

@[simp]
theorem llidx_nil {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M) :
    llidx k g (Quiver.Path.nil : Quiver.Path (vtx k g) (vtx k g)) = none := rfl

theorem llidx_cons {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι} {g : Monoid.CoprodI M}
    {x y : Vertex M} (p : Quiver.Path (vtx k g) x) (e : x ⟶ y) :
    llidx k g (p.cons e) =
      if h : isLeafSide k p.length = true then some e.idx else llidx k g p := rfl

/-- The last letter of `letters k g p` has index `llidx k g p`. -/
theorem llidx_eq_getLast {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι)
    (g : Monoid.CoprodI M) :
    ∀ {y : Vertex M} (p : Quiver.Path (vtx k g) y),
      (letters k g p).getLast?.map (fun x => x.1) = llidx k g p := by
  intro y p
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [letters_cons, llidx_cons]
    by_cases h : isLeafSide k p.length = true
    · rw [dif_pos h, dif_pos h, List.getLast?_append]
      simp
    · rw [dif_neg h, dif_neg h, List.getLast?_append]
      simp [ih]

/-- The number of letters of a path starting at a central vertex. -/
theorem letters_length_none {M : ι → Type u} [∀ i, Group (M i)] (g : Monoid.CoprodI M) :
    ∀ {y : Vertex M} (p : Quiver.Path (vtx (none : Option ι) g) y),
      (letters none g p).length = p.length / 2 := by
  intro y p
  induction p with
  | nil => simp only [letters_nil, Quiver.Path.length_nil, List.length_nil, Nat.zero_div]
  | cons p e ih =>
    rw [letters_cons, List.length_append, ih, Quiver.Path.length_cons]
    by_cases h : isLeafSide (none : Option ι) p.length = true
    · have h' : p.length % 2 = 1 := of_decide_eq_true h
      rw [dif_pos h]
      simp only [List.length_cons, List.length_nil, zero_add]
      omega
    · have h' : ¬ (p.length % 2 = 1) := fun hc =>
        h (by rw [isLeafSide_none, decide_eq_true_eq]; exact hc)
      rw [dif_neg h]
      simp only [List.length_nil, Nat.add_zero]
      omega

/-- The number of letters of a path starting at a leaf vertex. -/
theorem letters_length_some {M : ι → Type u} [∀ i, Group (M i)] (i : ι)
    (g : Monoid.CoprodI M) :
    ∀ {y : Vertex M} (p : Quiver.Path (vtx (some i) g) y),
      (letters (some i) g p).length = (p.length + 1) / 2 := by
  intro y p
  induction p with
  | nil => simp only [letters_nil, Quiver.Path.length_nil, List.length_nil, Nat.zero_div]
  | cons p e ih =>
    rw [letters_cons, List.length_append, ih, Quiver.Path.length_cons]
    by_cases h : isLeafSide (some i) p.length = true
    · have h' : p.length % 2 = 0 := of_decide_eq_true h
      rw [dif_pos h]
      simp only [List.length_cons, List.length_nil, zero_add]
      omega
    · have h' : ¬ (p.length % 2 = 0) := fun hc =>
        h (by rw [isLeafSide_some, decide_eq_true_eq]; exact hc)
      rw [dif_neg h]
      simp only [List.length_nil, Nat.add_zero]
      omega

/-! ## The invariant -/

/-- **The invariant of a reduced path.**  A path `p` from `vtx k g` satisfying `Inv k g p` has its
endpoint determined by its state, its letters are honest steps in the factors of the free product
with distinct consecutive indices, and the index of the last letter is related to the index of the
last arrow. -/
structure Inv {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M)
    {y : Vertex M} (p : Quiver.Path (vtx k g) y) : Prop where
  /-- If the endpoint is a leaf vertex, it is the leaf of the state. -/
  endpoint_some : isLeafSide k p.length = true →
    (∃ i, y = vtx (some i) (stt k g p)) ∧
      (∀ i, lidx k g p = some i → y = vtx (some i) (stt k g p))
  /-- If the endpoint is a central vertex, it is the central vertex of the state. -/
  endpoint_none : isLeafSide k p.length = false → y = vtx none (stt k g p)
  /-- The product of the letters is the total change of state. -/
  prod_letters : ((letters k g p).map (fun x => x.2)).prod = g⁻¹ * stt k g p
  /-- Consecutive letters lie in different factors. -/
  chain : (letters k g p).IsChain (fun a b => a.1 ≠ b.1)
  /-- Every letter lies in the factor of its index. -/
  mem : ∀ x ∈ letters k g p, x.2 ∈ factor M x.1
  /-- For a path starting at a central vertex, no letter is trivial. -/
  ne_one_central : k = none → ∀ x ∈ letters k g p, x.2 ≠ 1
  /-- Only the first letter can be trivial. -/
  ne_one_tail : ∀ x ∈ (letters k g p).tail, x.2 ≠ 1
  /-- If the endpoint is central, the last letter is the step of the last arrow. -/
  llidx_eq : isLeafSide k p.length = false → llidx k g p = lidx k g p
  /-- If the endpoint is a leaf and the path is non-empty, the last letter is not the step of the
  last arrow. -/
  llidx_ne : isLeafSide k p.length = true → p.length ≠ 0 → llidx k g p ≠ lidx k g p

/-! ## The normal-form length bound -/

/-- **The number of letters is bounded by the length of the reduced word** representing the
product.  This is the uniqueness of the normal form in the free product. -/
theorem letters_length_le_word_length {M : ι → Type u} [∀ i, Group (M i)]
    {l : List (Σ i : ι, M i)} (hne : ∀ x ∈ l, x.2 ≠ 1)
    (hchain : l.IsChain fun a b => a.1 ≠ b.1) {y : Monoid.CoprodI M}
    (hprod : (l.map fun x => Monoid.CoprodI.of x.2).prod = y) :
    l.length ≤ (Monoid.CoprodI.Word.equiv (M := M) y).toList.length := by
  classical
  have hw : (⟨l, fun x hx => hne x hx, hchain⟩ : Monoid.CoprodI.Word M)
      = Monoid.CoprodI.Word.equiv (M := M) y := by
    have h1 := (Monoid.CoprodI.Word.equiv (M := M)).right_inv
      (⟨l, fun x hx => hne x hx, hchain⟩ : Monoid.CoprodI.Word M)
    rw [← h1]
    exact congrArg (Monoid.CoprodI.Word.equiv (M := M)) hprod
  have hlen : l.length = (Monoid.CoprodI.Word.equiv (M := M) y).toList.length :=
    congrArg List.length (congrArg Monoid.CoprodI.Word.toList hw)
  exact le_of_eq hlen

/-- The same bound with the letters given as elements of the free product. -/
theorem letters_length_le_word_length' {M : ι → Type u} [∀ i, Group (M i)]
    {l : List (ι × Monoid.CoprodI M)} (hmem : ∀ x ∈ l, x.2 ∈ factor M x.1)
    (hne : ∀ x ∈ l, x.2 ≠ 1) (hchain : l.IsChain fun a b => a.1 ≠ b.1)
    {y : Monoid.CoprodI M} (hprod : (l.map fun x => x.2).prod = y) :
    l.length ≤ (Monoid.CoprodI.Word.equiv (M := M) y).toList.length := by
  classical
  have hpre : ∀ x ∈ l, Monoid.CoprodI.of (preimage M x.1 x.2) = x.2 :=
    fun x hx => of_preimage (hmem x hx)
  have hl : (l.map (fun x => (⟨x.1, preimage M x.1 x.2⟩ : Σ i : ι, M i))).length = l.length := by
    simp
  have hne' : ∀ x ∈ l.map (fun x => (⟨x.1, preimage M x.1 x.2⟩ : Σ i : ι, M i)), x.2 ≠ 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
    subst hyx
    intro hcon
    have hcon' : preimage M y.1 y.2 = 1 := hcon
    exact hne y hy (by rw [← hpre y hy, hcon', map_one])
  have hchain' : (l.map (fun x => (⟨x.1, preimage M x.1 x.2⟩ : Σ i : ι, M i))).IsChain
      (fun a b => a.1 ≠ b.1) := by
    refine List.isChain_of_isChain_map (f := fun x : Σ i : ι, M i => x.1) (fun a b h => h) ?_
    rw [show (l.map (fun x => (⟨x.1, preimage M x.1 x.2⟩ : Σ i : ι, M i))).map
        (fun x : Σ i : ι, M i => x.1) = l.map (fun y : ι × Monoid.CoprodI M => y.1) from by
      rw [List.map_map]
      rfl]
    exact List.isChain_map_of_isChain (f := fun y : ι × Monoid.CoprodI M => y.1)
      (fun a b (h : a.1 ≠ b.1) => h) hchain
  have hprod' : ((l.map (fun x => (⟨x.1, preimage M x.1 x.2⟩ : Σ i : ι, M i))).map
      (fun x => Monoid.CoprodI.of x.2)).prod = y := by
    have h : (l.map (fun x => (⟨x.1, preimage M x.1 x.2⟩ : Σ i : ι, M i))).map
        (fun x => Monoid.CoprodI.of x.2) = l.map (fun x => x.2) := by
      rw [List.map_map]
      exact List.map_congr_left (fun x hx => hpre x hx)
    rw [h, hprod]
  rw [← hl]
  exact letters_length_le_word_length hne' hchain' hprod'

end Work.ORLocInd.CoprodTree
