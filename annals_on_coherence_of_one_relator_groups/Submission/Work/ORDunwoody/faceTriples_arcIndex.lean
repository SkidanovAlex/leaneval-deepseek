import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.Dunwoody.Pattern
import Submission.Work.ORDunwoody.Dunwoody.Piece

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley
open scoped Sym2

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-!
## The boundary walk as a concatenation of oriented steps

`faceAux D a w` is the concatenation of one *block* for each letter of `w`.  We package each block
as a list of *oriented steps* (`OStep`): a traversal of a cell (an old vertex, the pattern point at
the midpoint, the other old vertex) or a traversal of a collapsed generator edge (two old
vertices).  This decomposition is the input for the two facts this file needs:

* every pattern point of the walk is flanked, immediately before and after, by the two endpoints of
  its cell (in some order) — so the `Sym2`-pair of its neighbours is that of `src` and `tgt`;
* the number of pattern points strictly before a visited old vertex is its *arc index*, so the `p`-th
  visit sits between the arcs of indices `p` and `p + 1`.
-/

/-- An **oriented step** of the boundary walk: from `src` to `tgt`, passing through the pattern
point `mid` if the step traverses a cell. -/
inductive OStep (D : GeoData T t₀ P) : Type u where
  /-- The traversal of a cell: visits the pattern point at the midpoint. -/
  | cross (src : BaseV D) (m : MidV D) (tgt : BaseV D) : OStep D
  /-- The traversal of a collapsed generator edge: visits no pattern point. -/
  | jump (src : BaseV D) (tgt : BaseV D) : OStep D

namespace OStep

variable {D : GeoData T t₀ P}

/-- The starting old vertex of a step. -/
def src : OStep D → BaseV D
  | cross s _ _ => s
  | jump s _ => s

/-- The terminal old vertex of a step. -/
def tgt : OStep D → BaseV D
  | cross _ _ t => t
  | jump _ t => t

/-- The vertices of `Λ''` visited *after* the starting vertex of a step. -/
def vertices : OStep D → List (Vertex D)
  | cross _ m t => [Sum.inr m, Sum.inl t]
  | jump _ t => [Sum.inl t]

/-- The step is consistent: its two ends are the two ends of the cell of its pattern point. -/
def Compat : OStep D → Prop
  | cross s m t => (s = MidV.src m ∧ t = MidV.tgt m) ∨ (s = MidV.tgt m ∧ t = MidV.src m)
  | jump _ _ => True

/-- The increment of the arc index along a step: one for a step through a pattern point. -/
def inc : OStep D → ℕ
  | cross .. => 1
  | jump .. => 0

@[simp] theorem vertices_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    vertices (cross s m t) = ([Sum.inr m, Sum.inl t] : List (Vertex D)) := rfl

@[simp] theorem vertices_jump (s t : BaseV D) :
    vertices (jump s t) = ([Sum.inl t] : List (Vertex D)) := rfl

@[simp] theorem tgt_cross (s : BaseV D) (m : MidV D) (t : BaseV D) : tgt (cross s m t) = t := rfl

@[simp] theorem tgt_jump (s t : BaseV D) : tgt (jump s t) = t := rfl

@[simp] theorem src_cross (s : BaseV D) (m : MidV D) (t : BaseV D) : src (cross s m t) = s := rfl

@[simp] theorem src_jump (s t : BaseV D) : src (jump s t) = s := rfl

@[simp] theorem inc_cross (s : BaseV D) (m : MidV D) (t : BaseV D) : inc (cross s m t) = 1 := rfl

@[simp] theorem inc_jump (s t : BaseV D) : inc (jump s t) = 0 := rfl

end OStep

/-! ## The steps of the traversal of one letter -/

/-- The steps of the traversal of the positive letter `(j,true)` at the base point `a`. -/
def letterStepsPos (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (OStep D) :=
  if D.L (j, true) = 0 then
    [OStep.jump (a, Sum.inl ()) (a * CayV.genE P (j, true), Sum.inl ())]
  else
    (List.finRange (D.L (j, true))).map (fun k : Fin (D.L (j, true)) =>
      OStep.cross (pos D a j (k : ℕ)) ⟨a, ⟨j, k⟩⟩ (pos D a j ((k : ℕ) + 1)))

/-- The steps of the traversal of the negative letter `(j,false)` at the base point `a`. -/
def letterStepsNeg (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (OStep D) :=
  if D.L (j, true) = 0 then
    [OStep.jump (a, Sum.inl ()) (a * (CayV.genE P (j, true))⁻¹, Sum.inl ())]
  else
    ((List.finRange (D.L (j, true))).reverse).map (fun k : Fin (D.L (j, true)) =>
      OStep.cross (pos D (a * (CayV.genE P (j, true))⁻¹) j ((k : ℕ) + 1))
        ⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩
        (pos D (a * (CayV.genE P (j, true))⁻¹) j (k : ℕ)))

/-- The steps of the traversal of one letter at the base point `a`. -/
def letterSteps (D : GeoData T t₀ P) (a : G) : Fin P.n × Bool → List (OStep D)
  | (j, true) => letterStepsPos D a j
  | (j, false) => letterStepsNeg D a j

@[simp] theorem letterSteps_true (a : G) (j : Fin P.n) :
    letterSteps D a (j, true) = letterStepsPos D a j := rfl

@[simp] theorem letterSteps_false (a : G) (j : Fin P.n) :
    letterSteps D a (j, false) = letterStepsNeg D a j := rfl

theorem finRange_head?_of_pos {L : ℕ} (h : 0 < L) :
    (List.finRange L).head? = some (⟨0, h⟩ : Fin L) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
  rw [List.finRange_succ]
  simp

theorem finRange_getLast?_succ : ∀ n : ℕ,
    (List.finRange (n + 1)).getLast? = some (Fin.last n)
  | 0 => rfl
  | n + 1 => by
      rw [List.finRange_succ]
      rw [List.getLast?_cons_of_ne_nil (by simp)]
      rw [List.getLast?_map, finRange_getLast?_succ n]
      simp [Fin.succ_last]

theorem finRange_getLast?_of_pos {L : ℕ} (h : 0 < L) :
    (List.finRange L).getLast? = some (⟨L - 1, by omega⟩ : Fin L) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
  rw [finRange_getLast?_succ n]
  congr 1

/-- The last position of a nonempty generator edge is its far endpoint. -/
theorem pos_pred_succ (c : G) (j : Fin P.n) (h : 0 < D.L (j, true)) :
    pos D c j (D.L (j, true) - 1 + 1) = (c * CayV.genE P (j, true), Sum.inl ()) := by
  rw [pos_succ_of_not_lt D c j (i := D.L (j, true) - 1) (by omega)]

theorem letterSteps_flatMap_true (a : G) (j : Fin P.n) :
    (letterSteps D a (j, true)).flatMap OStep.vertices = edgeTailPos D a j := by
  rw [letterSteps_true]
  unfold letterStepsPos edgeTailPos
  split_ifs with h
  · rfl
  · rw [List.flatMap_map]
    rfl

theorem letterSteps_flatMap_false (a : G) (j : Fin P.n) :
    (letterSteps D a (j, false)).flatMap OStep.vertices = edgeTailNeg D a j := by
  rw [letterSteps_false]
  unfold letterStepsNeg edgeTailNeg
  split_ifs with h
  · rfl
  · rw [List.flatMap_map]
    rfl

theorem letterSteps_chain (a : G) (x : Fin P.n × Bool) :
    (letterSteps D a x).IsChain (fun s s' => OStep.tgt s = OStep.src s') := by
  rcases x with ⟨j, b⟩
  cases b with
  | true =>
      rw [letterSteps_true]
      unfold letterStepsPos
      split_ifs with h
      · exact List.isChain_singleton _
      · refine List.isChain_map_of_isChain
          (R := fun k k' : Fin (D.L (j, true)) => (k : ℕ) + 1 = (k' : ℕ))
          (f := fun k : Fin (D.L (j, true)) =>
            OStep.cross (pos D a j (k : ℕ)) ⟨a, ⟨j, k⟩⟩ (pos D a j ((k : ℕ) + 1))) ?_ ?_
        · intro k k' hkk
          simp only [OStep.tgt_cross, OStep.src_cross]
          rw [hkk]
        · rw [← List.ofFn_id (D.L (j, true)), List.isChain_ofFn]
          intro i hi
          rfl
  | false =>
      rw [letterSteps_false]
      unfold letterStepsNeg
      split_ifs with h
      · exact List.isChain_singleton _
      · refine List.isChain_map_of_isChain
          (R := fun k k' : Fin (D.L (j, true)) => (k : ℕ) = (k' : ℕ) + 1)
          (f := fun k : Fin (D.L (j, true)) =>
            OStep.cross (pos D (a * (CayV.genE P (j, true))⁻¹) j ((k : ℕ) + 1))
              ⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩
              (pos D (a * (CayV.genE P (j, true))⁻¹) j (k : ℕ))) ?_ ?_
        · intro k k' hkk
          simp only [OStep.tgt_cross, OStep.src_cross]
          rw [hkk]
        · rw [List.isChain_reverse, ← List.ofFn_id (D.L (j, true)), List.isChain_ofFn]
          intro i hi
          rfl

theorem letterSteps_head_src (a : G) (x : Fin P.n × Bool) :
    ∀ s ∈ (letterSteps D a x).head?, OStep.src s = (a, Sum.inl ()) := by
  rcases x with ⟨j, b⟩
  cases b with
  | true =>
      rw [letterSteps_true]
      unfold letterStepsPos
      split_ifs with h
      · intro s hs
        simp only [List.head?_singleton, Option.mem_some_iff] at hs
        subst hs; rfl
      · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
        intro s hs
        rw [List.head?_map, finRange_head?_of_pos hpos] at hs
        simp only [Option.map_some, Option.mem_some_iff] at hs
        subst hs
        simp [pos_zero]
  | false =>
      rw [letterSteps_false]
      unfold letterStepsNeg
      split_ifs with h
      · intro s hs
        simp only [List.head?_singleton, Option.mem_some_iff] at hs
        subst hs; rfl
      · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
        intro s hs
        rw [List.head?_map, List.head?_reverse, finRange_getLast?_of_pos hpos] at hs
        simp only [Option.map_some, Option.mem_some_iff] at hs
        subst hs
        simp only [OStep.src_cross]
        rw [pos_pred_succ (a * (CayV.genE P (j, true))⁻¹) j hpos, mul_assoc, inv_mul_cancel,
          mul_one]

theorem letterSteps_getLast_tgt (a : G) (x : Fin P.n × Bool) :
    ∀ s ∈ (letterSteps D a x).getLast?, OStep.tgt s = (a * CayV.genE P x, Sum.inl ()) := by
  rcases x with ⟨j, b⟩
  cases b with
  | true =>
      rw [letterSteps_true]
      unfold letterStepsPos
      split_ifs with h
      · intro s hs
        simp only [List.getLast?_singleton, Option.mem_some_iff] at hs
        subst hs; rfl
      · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
        intro s hs
        rw [List.getLast?_map, finRange_getLast?_of_pos hpos] at hs
        simp only [Option.map_some, Option.mem_some_iff] at hs
        subst hs
        simp only [OStep.tgt_cross]
        rw [pos_pred_succ a j hpos]
  | false =>
      rw [letterSteps_false, CayV.genE_false]
      unfold letterStepsNeg
      split_ifs with h
      · intro s hs
        simp only [List.getLast?_singleton, Option.mem_some_iff] at hs
        subst hs; rfl
      · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
        intro s hs
        rw [List.getLast?_map, List.getLast?_reverse, finRange_head?_of_pos hpos] at hs
        simp only [Option.map_some, Option.mem_some_iff] at hs
        subst hs
        simp only [OStep.tgt_cross, pos_zero]
        rfl

theorem letterSteps_ne_nil (a : G) (x : Fin P.n × Bool) : letterSteps D a x ≠ [] := by
  rcases x with ⟨j, b⟩
  cases b with
  | true =>
      rw [letterSteps_true]
      unfold letterStepsPos
      split_ifs with h
      · simp
      · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
        intro hc
        rw [List.map_eq_nil_iff] at hc
        have hmem : (⟨0, hpos⟩ : Fin (D.L (j, true))) ∈ List.finRange (D.L (j, true)) :=
          List.mem_finRange _
        rw [hc] at hmem
        exact absurd hmem (by simp)
  | false =>
      rw [letterSteps_false]
      unfold letterStepsNeg
      split_ifs with h
      · simp
      · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
        intro hc
        rw [List.map_eq_nil_iff, List.reverse_eq_nil_iff] at hc
        have hmem : (⟨0, hpos⟩ : Fin (D.L (j, true))) ∈ List.finRange (D.L (j, true)) :=
          List.mem_finRange _
        rw [hc] at hmem
        exact absurd hmem (by simp)

theorem letterStepsPos_compat (a : G) (j : Fin P.n) :
    ∀ s ∈ letterStepsPos D a j, OStep.Compat s := by
  unfold letterStepsPos
  split_ifs with h
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    trivial
  · intro s hs
    rw [List.mem_map] at hs
    obtain ⟨k, -, rfl⟩ := hs
    exact Or.inl ⟨rfl, rfl⟩

theorem letterStepsNeg_compat (a : G) (j : Fin P.n) :
    ∀ s ∈ letterStepsNeg D a j, OStep.Compat s := by
  unfold letterStepsNeg
  split_ifs with h
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    trivial
  · intro s hs
    rw [List.mem_map] at hs
    obtain ⟨k, -, rfl⟩ := hs
    exact Or.inr ⟨rfl, rfl⟩

theorem letterSteps_compat (a : G) (x : Fin P.n × Bool) :
    ∀ s ∈ letterSteps D a x, OStep.Compat s := by
  rcases x with ⟨j, b⟩
  cases b with
  | true => rw [letterSteps_true]; exact letterStepsPos_compat a j
  | false => rw [letterSteps_false]; exact letterStepsNeg_compat a j

/-! ## The steps of the whole word -/

/-- The steps of the boundary walk of the word `w` read at the base point `a`. -/
def wordSteps (D : GeoData T t₀ P) (a : G) : List (Fin P.n × Bool) → List (OStep D)
  | [] => []
  | x :: w => letterSteps D a x ++ wordSteps D (a * CayV.genE P x) w

@[simp] theorem wordSteps_nil (a : G) : wordSteps D a [] = [] := rfl

@[simp] theorem wordSteps_cons (a : G) (x : Fin P.n × Bool) (w : List (Fin P.n × Bool)) :
    wordSteps D a (x :: w) = letterSteps D a x ++ wordSteps D (a * CayV.genE P x) w := rfl

/-- **The boundary walk of a face is the concatenation of the vertices of its steps.** -/
theorem faceAux_eq_flatMap_wordSteps (a : G) (w : List (Fin P.n × Bool)) :
    faceAux D a w = (wordSteps D a w).flatMap OStep.vertices := by
  induction w generalizing a with
  | nil => rfl
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | true =>
          rw [faceAux_true, wordSteps_cons, List.flatMap_append, letterSteps_flatMap_true,
            ih (a * CayV.genE P (j, true))]
      | false =>
          rw [faceAux_false, wordSteps_cons, CayV.genE_false, List.flatMap_append,
            letterSteps_flatMap_false, ih (a * (CayV.genE P (j, true))⁻¹)]
          rfl

/-- The start of the first step of a word is the base point. -/
theorem wordSteps_head_src (a : G) (w : List (Fin P.n × Bool)) :
    ∀ s ∈ (wordSteps D a w).head?, OStep.src s = (a, Sum.inl ()) := by
  induction w generalizing a with
  | nil => intro s hs; simp [wordSteps] at hs
  | cons x w ih =>
      rw [wordSteps_cons]
      intro s hs
      rw [List.head?_append_of_ne_nil _ (letterSteps_ne_nil a x)] at hs
      exact letterSteps_head_src a x s hs

/-- The steps of a word form a chain: the end of each step is the start of the next. -/
theorem wordSteps_chain (a : G) (w : List (Fin P.n × Bool)) :
    (wordSteps D a w).IsChain (fun s s' => OStep.tgt s = OStep.src s') := by
  induction w generalizing a with
  | nil => exact List.isChain_nil
  | cons x w ih =>
      rw [wordSteps_cons]
      refine List.IsChain.append (letterSteps_chain a x) (ih (a * CayV.genE P x)) ?_
      intro s hs s' hs'
      rw [letterSteps_getLast_tgt a x s hs,
        wordSteps_head_src (a * CayV.genE P x) w s' hs']

/-- Every step of a word is consistent. -/
theorem wordSteps_compat (a : G) (w : List (Fin P.n × Bool)) :
    ∀ s ∈ wordSteps D a w, OStep.Compat s := by
  induction w generalizing a with
  | nil => intro s hs; simp [wordSteps] at hs
  | cons x w ih =>
      intro s hs
      rw [wordSteps_cons, List.mem_append] at hs
      rcases hs with hs | hs
      · exact letterSteps_compat a x s hs
      · exact ih (a * CayV.genE P x) s hs

/-! ## The combinatorial core: visits and arc indices along a step decomposition -/

theorem visitTriplesAux_vertices_cross (u : BaseV D) (s : BaseV D) (m : MidV D) (t : BaseV D)
    (W : List (Vertex D)) :
    visitTriplesAux u (OStep.vertices (OStep.cross s m t) ++ W)
      = (u, m, t) :: visitTriplesAux t W := by
  rw [OStep.vertices_cross, List.cons_append, List.singleton_append, visitTriplesAux_inr]

theorem visitTriplesAux_vertices_jump (u : BaseV D) (s t : BaseV D) (W : List (Vertex D)) :
    visitTriplesAux u (OStep.vertices (OStep.jump s t) ++ W) = visitTriplesAux t W := by
  rw [OStep.vertices_jump, List.singleton_append, visitTriplesAux_inl]

theorem arcIndexAux_vertices_append (s : OStep D) (W : List (Vertex D)) (k : ℕ) :
    arcIndexAux (OStep.vertices s ++ W) k
      = (OStep.tgt s, k + OStep.inc s) :: arcIndexAux W (k + OStep.inc s) := by
  cases s with
  | cross src m t => simp
  | jump src t => simp

/-- **The visits and the arc indices along a step decomposition.**  If `S` is a chain of
consistent steps (with the first step starting at `u`), then the `p`-th pattern point of the walk
`S.flatMap OStep.vertices` has the start of its step at arc index `k + p` and the end at arc index
`k + p + 1`, and its neighbours' `Sym2`-pair is the pair of the endpoints of its cell. -/
theorem steps_good (S : List (OStep D)) :
    ∀ (u : BaseV D) (k : ℕ),
      S.IsChain (fun s s' => OStep.tgt s = OStep.src s') →
      (∀ s ∈ S.head?, OStep.src s = u) → (∀ s ∈ S, OStep.Compat s) →
      ∀ (p : ℕ) (u' : BaseV D) (m : MidV D) (v' : BaseV D),
        (visitTriplesAux u (S.flatMap OStep.vertices))[p]? = some (u', m, v') →
        (u', k + p) ∈ (u, k) :: arcIndexAux (S.flatMap OStep.vertices) k ∧
        (v', k + p + 1) ∈ (u, k) :: arcIndexAux (S.flatMap OStep.vertices) k ∧
        s(u', v') = s(MidV.src m, MidV.tgt m) := by
  induction S with
  | nil =>
      intro u k hc hh hcp p u' m v' hp
      simp only [List.flatMap_nil, visitTriplesAux_nil, List.getElem?_nil] at hp
      exact absurd hp (by simp)
  | cons s S' ih =>
      intro u k hc hh hcp p u' m v' hp
      have hc' : S'.IsChain (fun s s' => OStep.tgt s = OStep.src s') := hc.tail
      have hh' : ∀ s' ∈ S'.head?, OStep.src s' = OStep.tgt s :=
        fun s' hs' => (hc.rel_head? hs').symm
      have hcp' : ∀ s' ∈ S', OStep.Compat s' := fun s' hs' => hcp s' (by simp [hs'])
      have hs : OStep.src s = u := hh s (by simp)
      cases s with
      | cross src mm tgt =>
          have hcs : OStep.Compat (OStep.cross src mm tgt) := hcp _ (by simp)
          simp only [OStep.Compat] at hcs
          rw [show OStep.src (OStep.cross src mm tgt) = src from rfl] at hs
          simp only [List.flatMap_cons] at hp ⊢
          rw [visitTriplesAux_vertices_cross] at hp
          rw [arcIndexAux_vertices_append]
          simp only [OStep.tgt_cross, OStep.inc_cross]
          cases p with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, rfl, rfl⟩ := hp
              rw [hs] at hcs
              exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
                Sym2.eq_iff.mpr hcs⟩
          | succ q =>
              simp only [List.getElem?_cons_succ] at hp
              obtain ⟨h1, h2, h3⟩ := ih tgt (k + 1) hc' hh' hcp' q u' m v' hp
              have e1 : k + (q + 1) = k + 1 + q := by omega
              have e2 : k + (q + 1) + 1 = k + 1 + q + 1 := by omega
              refine ⟨?_, ?_, h3⟩
              · rw [e1]; exact List.mem_cons_of_mem _ h1
              · rw [e2]; exact List.mem_cons_of_mem _ h2
      | jump src tgt =>
          simp only [List.flatMap_cons] at hp ⊢
          rw [visitTriplesAux_vertices_jump] at hp
          rw [arcIndexAux_vertices_append]
          simp only [OStep.inc_jump, Nat.add_zero]
          obtain ⟨h1, h2, h3⟩ := ih tgt k hc' hh' hcp' p u' m v' hp
          exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3⟩

end Work.ORDunwoody.Dunwoody

namespace Work.ORDunwoody

open scoped Sym2

/-- **The visits of a face and its arc indices agree.**  If the `p`-th pattern point of the
boundary walk of the face `(w, c)` has the old vertices `u` and `v` immediately before and after
it, then `u` lies in the arc of index `p`, `v` in the arc of index `p + 1`, and the `Sym2`-pair
`{u, v}` is the pair of endpoints of `v`'s cell. -/
theorem faceTriples_arcIndex {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool))
    {p : ℕ} {u v : Work.ORDunwoody.Dunwoody.BaseV D} {m : Work.ORDunwoody.Dunwoody.MidV D}
    (h : (Work.ORDunwoody.Dunwoody.faceTriples D c w)[p]? = some (u, m, v)) :
    (u, p) ∈ Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w) ∧
      (v, p + 1) ∈ Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w) ∧
      s(u, v) = s(Work.ORDunwoody.Dunwoody.MidV.src m, Work.ORDunwoody.Dunwoody.MidV.tgt m) := by
  have hflat : Work.ORDunwoody.Dunwoody.faceAux D c w
      = (Work.ORDunwoody.Dunwoody.wordSteps D c w).flatMap
          Work.ORDunwoody.Dunwoody.OStep.vertices :=
    Work.ORDunwoody.Dunwoody.faceAux_eq_flatMap_wordSteps c w
  have hface : Work.ORDunwoody.Dunwoody.faceTriples D c w
      = Work.ORDunwoody.Dunwoody.visitTriplesAux (c, Sum.inl ())
          ((Work.ORDunwoody.Dunwoody.wordSteps D c w).flatMap
            Work.ORDunwoody.Dunwoody.OStep.vertices) := by
    simp only [Work.ORDunwoody.Dunwoody.faceTriples, Work.ORDunwoody.Dunwoody.faceWalk_eq, hflat,
      Work.ORDunwoody.Dunwoody.visitTriples_inl]
  have hgood := Work.ORDunwoody.Dunwoody.steps_good (D := D)
      (Work.ORDunwoody.Dunwoody.wordSteps D c w) (c, Sum.inl ()) 0
      (Work.ORDunwoody.Dunwoody.wordSteps_chain c w)
      (Work.ORDunwoody.Dunwoody.wordSteps_head_src c w)
      (Work.ORDunwoody.Dunwoody.wordSteps_compat c w)
      p u m v (by rw [← hface]; exact h)
  obtain ⟨h1, h2, h3⟩ := hgood
  refine ⟨?_, ?_, h3⟩
  · simpa only [Work.ORDunwoody.Dunwoody.arcIndex, Work.ORDunwoody.Dunwoody.faceWalk_eq, hflat,
      Work.ORDunwoody.Dunwoody.arcIndexAux_inl, Nat.zero_add] using h1
  · simpa only [Work.ORDunwoody.Dunwoody.arcIndex, Work.ORDunwoody.Dunwoody.faceWalk_eq, hflat,
      Work.ORDunwoody.Dunwoody.arcIndexAux_inl, Nat.zero_add] using h2

end Work.ORDunwoody
