import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Pattern

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-! ## The shape of the boundary walk tails

`faceWalk D c w = Sum.inl (c, inl ()) :: faceAux D c w`, and `faceVisits` records, for each
pattern point of `faceWalk`, the two old vertices on either side (`visitTriples`) and then forgets
the old vertices, leaving the pattern points in order.

The list `faceAux D c w` is built out of *blocks*: each traversal of a generator edge contributes
either a single old vertex (a collapsed generator, `L (j,true) = 0`) or a list of two-element blocks
`[pattern point, old vertex]`.  Consequently `faceAux D c w` is a concatenation of blocks of the
forms `[inl _]` and `[inr _ , inl _]`: no two consecutive pattern points, and never ending in a
pattern point.

The predicate `Good` records exactly this shape, and `extract` shows that for such a list the
"middle projection" of `visitTriplesAux` is the same as dropping the old vertices outright. -/

namespace FaceVisitsAux

/-- A list of vertices of `Λ''` is *good* if it is a concatenation of blocks of the forms
`[inl _]` (a collapsed generator step) and `[inr _, inl _]` (a cell traversal): equivalently, no
two consecutive pattern points and no trailing pattern point. -/
def Good : List (Vertex D) → Prop
  | [] => True
  | Sum.inl _ :: rest => Good rest
  | Sum.inr _ :: Sum.inl _ :: rest => Good rest
  | _ => False

/-- The concatenation of two good lists is good. -/
theorem good_append : ∀ {l₁ l₂ : List (Vertex D)}, Good l₁ → Good l₂ → Good (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h₂; exact h₂
  | cons hd tl ih =>
      intro l₂ h₁ h₂
      cases hd with
      | inl v =>
          simp only [List.cons_append]
          exact ih h₁ h₂
      | inr m =>
          cases tl with
          | nil => exact h₁.elim
          | cons hd' tl' =>
              cases hd' with
              | inr m' => exact h₁.elim
              | inl w =>
                  simp only [List.cons_append]
                  exact ih h₁ h₂

/-- A `flatMap` of good lists (over any index list) is good. -/
theorem good_flatMap {ι : Type} (l : List ι) (f : ι → List (Vertex D))
    (h : ∀ i ∈ l, Good (f i)) : Good (l.flatMap f) := by
  induction l with
  | nil => trivial
  | cons i l' ih =>
      rw [List.flatMap_cons]
      exact good_append (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- The traversal of a positive generator edge is good. -/
theorem good_edgeTailPos (a : G) (j : Fin P.n) : Good (edgeTailPos D a j) := by
  by_cases h : D.L (j, true) = 0
  · rw [edgeTailPos, if_pos h]; trivial
  · rw [edgeTailPos, if_neg h]
    apply good_flatMap
    intro k _
    trivial

/-- The traversal of a negative generator edge is good. -/
theorem good_edgeTailNeg (a : G) (j : Fin P.n) : Good (edgeTailNeg D a j) := by
  by_cases h : D.L (j, true) = 0
  · rw [edgeTailNeg, if_pos h]; trivial
  · rw [edgeTailNeg, if_neg h]
    apply good_flatMap
    intro k _
    trivial

/-- The tail of the boundary walk of a word is good. -/
theorem good_faceAux (a : G) (w : List (Fin P.n × Bool)) : Good (faceAux D a w) := by
  induction w generalizing a with
  | nil => trivial
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | false => rw [faceAux_false]; exact good_append (good_edgeTailNeg a j) (ih _)
      | true => rw [faceAux_true]; exact good_append (good_edgeTailPos a j) (ih _)

/-- For a *good* list, the pattern points extracted with their flanking old vertices
(`visitTriplesAux`) are exactly the pattern points of the list, in order. -/
theorem extract : ∀ (l : List (Vertex D)), Good l → ∀ u : BaseV D,
    (visitTriplesAux u l).map (fun t => t.2.1) = l.filterMap Vertex.midOf := by
  intro l
  induction l with
  | nil => intro _ u; rfl
  | cons hd tl ih =>
      intro hl u
      cases hd with
      | inl v =>
          simp only [visitTriplesAux_inl, List.filterMap_cons, Vertex.midOf_inl]
          exact ih hl v
      | inr m =>
          cases tl with
          | nil => exact hl.elim
          | cons hd' tl' =>
              cases hd' with
              | inr m' => exact hl.elim
              | inl w =>
                  have h := ih hl w
                  simp only [visitTriplesAux_inl, List.filterMap_cons, Vertex.midOf_inl] at h
                  simp only [visitTriplesAux_inr, List.map_cons, List.filterMap_cons,
                    Vertex.midOf_inr, Vertex.midOf_inl]
                  exact congrArg (List.cons m) h

end FaceVisitsAux

theorem faceVisits_eq_faceAux {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool)) :
    Work.ORDunwoody.Dunwoody.faceVisits D c w =
      (Work.ORDunwoody.Dunwoody.faceAux D c w).filterMap Work.ORDunwoody.Dunwoody.Vertex.midOf := by
  unfold Work.ORDunwoody.Dunwoody.faceVisits Work.ORDunwoody.Dunwoody.faceTriples
  rw [Work.ORDunwoody.Dunwoody.faceWalk_eq]
  simp only [Work.ORDunwoody.Dunwoody.visitTriples_inl]
  exact FaceVisitsAux.extract (faceAux D c w) (FaceVisitsAux.good_faceAux c w) (c, Sum.inl ())

end Work.ORDunwoody
