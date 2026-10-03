/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The boundary walk of a face is a walk in the 1-skeleton of `Λ''`

`Dunwoody/FaceWalk.lean` defines, for a word `w` and a base point `c`, the list
`faceWalk D c w : List (Vertex D)` of vertices of the subdivided Cayley complex `Λ''`
visited when the word is read at `c`, each generator edge being subdivided by the
geodesic data and each cell being split at its pattern point.

This file proves that this list is a *walk* in the 1-skeleton `Dunwoody.graph` of `Λ''`:
consecutive entries are adjacent or equal.

The proof decomposes the walk into the block
`block a x = (c,∗) :: edgeTail a x`, where `edgeTail a x` is the tail of the traversal of
the letter `x` at `a`.  For each block we prove

* that it is a chain (`edgeTail*_chain` together with the first step `edgeTail*_start`), and
* that its last vertex is the base point of the next letter (`edgeTail*_getLast`).

The walk is then obtained by an induction on the word, gluing each block to the remainder
with `List.IsChain.append`, the junction being supplied by the chain property of the
remainder itself (`List.IsChain.rel_head?`).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk
import Submission.Work.ORDunwoody.faceWalk_getLast

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-- The relation defining a walk of the 1-skeleton of `Λ''`: two consecutive vertices are
adjacent, or (for a degenerate step) equal. -/
def faceWalkRel (D : Work.ORDunwoody.Cayley.GeoData T t₀ P) (v w : Vertex D) : Prop :=
  (graph (D := D)).Adj v w ∨ v = w

namespace FaceWalkChain

/-- The step relation refines the walk relation. -/
theorem faceWalkRel_of_stepRel {v w : Vertex D} (h : StepRel v w) : faceWalkRel D v w := by
  rcases eq_or_ne v w with hvw | hne
  · exact Or.inr hvw
  · exact Or.inl ((graph_adj_iff (D := D)).2 ⟨hne, Or.inl h⟩)

/-- The walk relation is symmetric. -/
theorem faceWalkRel_symm {v w : Vertex D} (h : faceWalkRel D v w) : faceWalkRel D w v := by
  rcases h with h | rfl
  · exact Or.inl h.symm
  · exact Or.inr rfl

/-! ## Chains of `flatMap`s

The two tails `edgeTailPos` and `edgeTailNeg` have the shape
`(list of indices).flatMap (fun k => [pattern point, interior point])`.  A `flatMap` of
nonempty blocks, each a chain, glued along a `next`-chain of indices, is a chain. -/

theorem isChain_flatMap_of_chain {ι α : Type*} (R : α → α → Prop) (next : ι → ι → Prop)
    {l : List ι} {f : ι → List α}
    (hl : l.IsChain next)
    (hne : ∀ i ∈ l, f i ≠ [])
    (hblk : ∀ i ∈ l, (f i).IsChain R)
    (hlink : ∀ i ∈ l, ∀ j ∈ l, next i j → ∀ x ∈ (f i).getLast?, ∀ y ∈ (f j).head?, R x y) :
    (l.flatMap f).IsChain R := by
  induction l with
  | nil => simp
  | cons i l' ih =>
      rw [List.flatMap_cons]
      refine List.IsChain.append (hblk i (by simp)) ?_ ?_
      · exact ih hl.tail (fun j hj => hne j (by simp [hj])) (fun j hj => hblk j (by simp [hj]))
          (fun j hj j' hj' h => hlink j (by simp [hj]) j' (by simp [hj']) h)
      · intro x hx y hy
        cases l' with
        | nil => simp at hy
        | cons j l'' =>
            rw [List.flatMap_cons, List.head?_append_of_ne_nil _ (hne j (by simp))] at hy
            exact hlink i (by simp) j (by simp) (hl.rel_head? (by simp)) x hx y hy

/-! ## The first step of a traversal

Starting from the base point `a`, the first vertex visited by the traversal of the letter
`(j,true)` (resp. `(j,false)`) is adjacent to `a`. -/

/-- The first block of a `flatMap` over `finRange L`, for positive `L`, is the block at index
`0`. -/
theorem finRange_flatMap_head_of_pos {L : ℕ} (hL : 0 < L)
    (f : (k : Fin L) → List (Vertex D)) (hf : ∀ k, f k ≠ []) :
    ((List.finRange L).flatMap f).head? = (f ⟨0, hL⟩).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hL)
  rw [List.finRange_succ, List.flatMap_cons, List.head?_append_of_ne_nil _ (hf 0)]
  exact congrArg (fun k : Fin (n + 1) => (f k).head?) (Fin.ext rfl)

/-- The first block of a `flatMap` over the reversal of `finRange L`, for positive `L`, is the
block at index `L - 1`. -/
theorem finRange_reverse_flatMap_head_of_pos {L : ℕ} (hL : 0 < L)
    (f : (k : Fin L) → List (Vertex D)) (hf : ∀ k, f k ≠ []) :
    (((List.finRange L).reverse).flatMap f).head? = (f ⟨L - 1, by omega⟩).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hL)
  rw [finRange_succ_last, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons, List.head?_append_of_ne_nil _ (hf _)]
  exact congrArg (fun k : Fin (n + 1) => (f k).head?) (Fin.ext (by simp))

/-- The pattern point at the start of the positive traversal of `(j,true)` at `a` is
adjacent to `a`. -/
theorem edgeTailPos_start (a : G) (j : Fin P.n) :
    ∀ b ∈ (edgeTailPos D a j).head?, faceWalkRel D (Sum.inl (a, Sum.inl ())) b := by
  intro b hb
  by_cases hL : D.L (j, true) = 0
  · simp only [edgeTailPos, if_pos hL, List.head?_singleton, Option.mem_some_iff] at hb
    subst hb
    exact faceWalkRel_of_stepRel (Or.inr ⟨a, j, hL, rfl, rfl⟩)
  · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero hL
    simp only [edgeTailPos, if_neg hL] at hb
    rw [finRange_flatMap_head_of_pos hpos
      (fun k : Fin (D.L (j, true)) =>
        ([Sum.inr (⟨a, ⟨j, k⟩⟩ : MidV D), Sum.inl (pos D a j (k + 1))] : List (Vertex D)))
      (fun k => by simp)] at hb
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst hb
    exact faceWalkRel_of_stepRel (Or.inl ⟨⟨a, j, ⟨0, hpos⟩⟩, Or.inl ⟨rfl, rfl⟩⟩)

/-- The pattern point at the start of the negative traversal of `(j,false)` at `a` is
adjacent to `a`. -/
theorem edgeTailNeg_start (a : G) (j : Fin P.n) :
    ∀ b ∈ (edgeTailNeg D a j).head?, faceWalkRel D (Sum.inl (a, Sum.inl ())) b := by
  intro b hb
  by_cases hL : D.L (j, true) = 0
  · simp only [edgeTailNeg, if_pos hL, List.head?_singleton, Option.mem_some_iff] at hb
    subst hb
    have key : faceWalkRel D
        (Sum.inl (a * (CayV.genE P (j, true))⁻¹, Sum.inl ()) : Vertex D)
        (Sum.inl (a * (CayV.genE P (j, true))⁻¹ * CayV.genE P (j, true), Sum.inl ()) : Vertex D) :=
      faceWalkRel_of_stepRel (Or.inr ⟨a * (CayV.genE P (j, true))⁻¹, j, hL, rfl, rfl⟩)
    rw [show a * (CayV.genE P (j, true))⁻¹ * CayV.genE P (j, true) = a from by
      rw [mul_assoc, inv_mul_cancel, mul_one]] at key
    exact faceWalkRel_symm key
  · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero hL
    simp only [edgeTailNeg, if_neg hL] at hb
    rw [finRange_reverse_flatMap_head_of_pos hpos
      (fun k : Fin (D.L (j, true)) =>
        ([Sum.inr (⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩ : MidV D),
          Sum.inl (pos D (a * (CayV.genE P (j, true))⁻¹) j k)] : List (Vertex D)))
      (fun k => by simp)] at hb
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst hb
    have htgt : (⟨a * (CayV.genE P (j, true))⁻¹, j, ⟨D.L (j, true) - 1, by omega⟩⟩ :
        Cell D).tgt = (a, Sum.inl ()) := by
      simp only [Cell.tgt]
      rw [pos_succ_of_not_lt D _ j (i := D.L (j, true) - 1) (by omega)]
      exact Prod.ext (by rw [mul_assoc, inv_mul_cancel, mul_one]) rfl
    have key : faceWalkRel D
        (Sum.inr ((⟨a * (CayV.genE P (j, true))⁻¹, j, ⟨D.L (j, true) - 1, by omega⟩⟩ :
          Cell D).mid) : Vertex D)
        (Sum.inl ((⟨a * (CayV.genE P (j, true))⁻¹, j, ⟨D.L (j, true) - 1, by omega⟩⟩ :
          Cell D).tgt) : Vertex D) :=
      faceWalkRel_of_stepRel (Or.inl ⟨_, Or.inr ⟨rfl, rfl⟩⟩)
    rw [htgt] at key
    exact faceWalkRel_symm key

/-! ## The traversals are chains -/

/-- The positive traversal of `(j,true)` at `a` is a chain of the walk relation. -/
theorem edgeTailPos_chain (a : G) (j : Fin P.n) : (edgeTailPos D a j).IsChain (faceWalkRel D) := by
  by_cases hL : D.L (j, true) = 0
  · simp only [edgeTailPos, if_pos hL]
    exact List.isChain_singleton _
  · simp only [edgeTailPos, if_neg hL]
    refine isChain_flatMap_of_chain (faceWalkRel D)
      (fun k k' : Fin (D.L (j, true)) => (k : ℕ) + 1 = (k' : ℕ)) ?_ ?_ ?_ ?_
    · rw [← List.ofFn_id (D.L (j, true)), List.isChain_ofFn]
      intro i hi
      rfl
    · intro k _
      simp
    · intro k _
      exact List.IsChain.cons_cons
        (faceWalkRel_of_stepRel (Or.inl ⟨⟨a, j, k⟩, Or.inr ⟨rfl, rfl⟩⟩))
        (List.isChain_singleton _)
    · intro k _ k' _ hkk' x hx y hy
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hx
      subst hy
      rw [hkk']
      exact faceWalkRel_of_stepRel (Or.inl ⟨⟨a, j, k'⟩, Or.inl ⟨rfl, rfl⟩⟩)

/-- The negative traversal of `(j,false)` at `a` is a chain of the walk relation. -/
theorem edgeTailNeg_chain (a : G) (j : Fin P.n) : (edgeTailNeg D a j).IsChain (faceWalkRel D) := by
  by_cases hL : D.L (j, true) = 0
  · simp only [edgeTailNeg, if_pos hL]
    exact List.isChain_singleton _
  · simp only [edgeTailNeg, if_neg hL]
    refine isChain_flatMap_of_chain (faceWalkRel D)
      (fun k k' : Fin (D.L (j, true)) => (k : ℕ) = (k' : ℕ) + 1) ?_ ?_ ?_ ?_
    · rw [List.isChain_reverse, ← List.ofFn_id (D.L (j, true)), List.isChain_ofFn]
      intro i hi
      rfl
    · intro k _
      simp
    · intro k _
      exact List.IsChain.cons_cons
        (faceWalkRel_symm (faceWalkRel_of_stepRel
          (Or.inl ⟨⟨a * (CayV.genE P (j, true))⁻¹, j, k⟩, Or.inl ⟨rfl, rfl⟩⟩)))
        (List.isChain_singleton _)
    · intro k _ k' _ hkk' x hx y hy
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hx
      subst hy
      rw [hkk']
      exact faceWalkRel_symm (faceWalkRel_of_stepRel
        (Or.inl ⟨⟨a * (CayV.genE P (j, true))⁻¹, j, k'⟩, Or.inr ⟨rfl, rfl⟩⟩))

/-- A block of the walk: the base point of the traversal of `(j,true)` at `a`, followed by
the whole traversal. -/
theorem blockPos_chain (a : G) (j : Fin P.n) :
    (Sum.inl (a, Sum.inl ()) :: edgeTailPos D a j : List (Vertex D)).IsChain (faceWalkRel D) :=
  List.IsChain.cons (edgeTailPos_chain a j) (edgeTailPos_start a j)

/-- A block of the walk: the base point of the traversal of `(j,false)` at `a`, followed by
the whole traversal. -/
theorem blockNeg_chain (a : G) (j : Fin P.n) :
    (Sum.inl (a, Sum.inl ()) :: edgeTailNeg D a j : List (Vertex D)).IsChain (faceWalkRel D) :=
  List.IsChain.cons (edgeTailNeg_chain a j) (edgeTailNeg_start a j)

/-! ## The tail of the boundary walk is a walk -/

/-- The tail of the boundary walk of `w` read at `a`, prefixed by the base point `a`, is a
chain of the walk relation. -/
theorem walkList_chain (a : G) (w : List (Fin P.n × Bool)) :
    (Sum.inl (a, Sum.inl ()) :: faceAux D a w : List (Vertex D)).IsChain (faceWalkRel D) := by
  induction w generalizing a with
  | nil => exact List.isChain_singleton _
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | false =>
          rw [faceAux_false, ← List.cons_append]
          refine List.IsChain.append (blockNeg_chain a j)
            (List.IsChain.tail (ih (a * (CayV.genE P (j, true))⁻¹))) ?_
          intro y hy z hz
          rw [← List.singleton_append, List.getLast?_append, edgeTailNeg_getLast,
            Option.some_or] at hy
          simp only [Option.mem_some_iff] at hy
          subst hy
          exact (ih (a * (CayV.genE P (j, true))⁻¹)).rel_head? hz
      | true =>
          rw [faceAux_true, ← List.cons_append]
          refine List.IsChain.append (blockPos_chain a j)
            (List.IsChain.tail (ih (a * CayV.genE P (j, true)))) ?_
          intro y hy z hz
          rw [← List.singleton_append, List.getLast?_append, edgeTailPos_getLast,
            Option.some_or] at hy
          simp only [Option.mem_some_iff] at hy
          subst hy
          exact (ih (a * CayV.genE P (j, true))).rel_head? hz

end FaceWalkChain

/-- **The boundary walk of a face of `Λ''` is a walk** in the 1-skeleton of `Λ''`: consecutive
vertices are adjacent, or equal. -/
theorem faceWalk_chain {G : Type u} [Group G] {V : Type u} [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool)) : (Work.ORDunwoody.Dunwoody.faceWalk D c w).IsChain (fun v v' => (Work.ORDunwoody.Dunwoody.graph (D := D)).Adj v v' ∨ v = v') := by
  rw [faceWalk_eq]
  exact FaceWalkChain.walkList_chain (D := D) c w

end Work.ORDunwoody

