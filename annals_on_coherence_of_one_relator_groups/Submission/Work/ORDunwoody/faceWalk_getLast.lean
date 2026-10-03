import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk
import Submission.Work.ORDunwoody.finRange_flatMap_getLast_succ
import Submission.Work.ORDunwoody.finRange_reverse_flatMap_getLast_succ

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## Reading words and letters -/

/-- The letter `(j,false)` has the inverse of the letter `(j,true)` as its image in `G`. -/
theorem genE_false_eq (P : FinPresentation G) (j : Fin P.n) :
    CayV.genE P (j, false) = (CayV.genE P (j, true))⁻¹ := by
  rw [CayV.genE_false, CayV.genE_true]

/-- Reading the letter `(j,false)` at `a` and then the rest of the word is the same as reading the
rest of the word at the translated base point. -/
theorem endPt_false_eq (a : G) (j : Fin P.n) (w : List (Fin P.n × Bool)) :
    endPt P a ((j, false) :: w) = endPt P (a * (CayV.genE P (j, true))⁻¹) w := by
  rw [endPt_cons, genE_false_eq]

/-! ## Variants of the delegated list lemmas, indexed by an arbitrary length -/

/-- The last block of a `flatMap` over `finRange L`, for nonempty `L`, is the block at the last
index. -/
theorem finRange_flatMap_getLast_of_pos {β : Type*} {L : ℕ} (hL : 0 < L)
    (f : (k : Fin L) → List β) (hf : ∀ k, f k ≠ []) :
    ((List.finRange L).flatMap f).getLast? = (f ⟨L - 1, by omega⟩).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  rw [finRange_flatMap_getLast_succ n f hf]
  congr 1

/-- The last block of a `flatMap` over the reversal of `finRange L`, for nonempty `L`, is the block
at index `0`. -/
theorem finRange_reverse_flatMap_getLast_of_pos {β : Type*} {L : ℕ} (hL : 0 < L)
    (f : (k : Fin L) → List β) (hf : ∀ k, f k ≠ []) :
    (((List.finRange L).reverse).flatMap f).getLast? = (f ⟨0, by omega⟩).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  rw [finRange_reverse_flatMap_getLast_succ n f hf]

/-! ## The traversals of a generator edge -/

/-- The last vertex visited when traversing the positive generator edge `(j,true)` from `a` is the
terminal vertex of the edge. -/
theorem edgeTailPos_getLast (D : GeoData T t₀ P) (a : G) (j : Fin P.n) :
    (edgeTailPos D a j).getLast? =
      some (Sum.inl (a * CayV.genE P (j, true), Sum.inl ())) := by
  by_cases h0 : D.L (j, true) = 0
  · simp only [edgeTailPos, if_pos h0, List.getLast?_singleton]
  · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h0
    simp only [edgeTailPos, if_neg h0]
    rw [finRange_flatMap_getLast_of_pos hpos
      (fun k : Fin (D.L (j, true)) =>
        [Sum.inr (⟨a, ⟨j, k⟩⟩ : MidV D), Sum.inl (pos D a j (k + 1))])
      (fun k => by simp)]
    simp only [List.getLast?_cons_cons, List.getLast?_singleton]
    rw [pos_succ_of_not_lt D a j (i := D.L (j, true) - 1) (by omega)]

/-- The last vertex visited when traversing the reverse of the positive generator edge `(j,true)`
starting at `a` is the initial vertex of the edge. -/
theorem edgeTailNeg_getLast (D : GeoData T t₀ P) (a : G) (j : Fin P.n) :
    (edgeTailNeg D a j).getLast? =
      some (Sum.inl (a * (CayV.genE P (j, true))⁻¹, Sum.inl ())) := by
  by_cases h0 : D.L (j, true) = 0
  · simp only [edgeTailNeg, if_pos h0, List.getLast?_singleton]
  · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h0
    simp only [edgeTailNeg, if_neg h0]
    rw [finRange_reverse_flatMap_getLast_of_pos hpos
      (fun k : Fin (D.L (j, true)) =>
        [Sum.inr (⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩ : MidV D),
         Sum.inl (pos D (a * (CayV.genE P (j, true))⁻¹) j k)])
      (fun k => by simp)]
    simp only [List.getLast?_cons_cons, List.getLast?_singleton]
    rfl

/-! ## The tail of a boundary walk -/

/-- The last vertex of the tail of the boundary walk of `w` (read at `a`) is the current vertex
after reading `w`. -/
theorem faceAux_getLast (D : GeoData T t₀ P) (w : List (Fin P.n × Bool)) (hw : w ≠ [])
    (a : G) :
    (faceAux D a w).getLast? = some (Sum.inl (endPt P a w, Sum.inl ())) := by
  revert hw
  induction w generalizing a with
  | nil => intro hw; exact absurd rfl hw
  | cons x t ih =>
      intro hw
      obtain ⟨j, b⟩ := x
      cases b with
      | false =>
          rw [faceAux_false]
          cases t with
          | nil =>
              rw [faceAux_nil, List.append_nil, edgeTailNeg_getLast]
              simp only [endPt_false_eq, endPt_nil]
          | cons y u =>
              have hne : faceAux D (a * (CayV.genE P (j, true))⁻¹) (y :: u) ≠ [] := by
                have h' := ih (a * (CayV.genE P (j, true))⁻¹) (by simp)
                intro hnil
                rw [hnil] at h'
                exact absurd h' (by simp)
              rw [List.getLast?_append_of_ne_nil (edgeTailNeg D a j) hne,
                ih (a * (CayV.genE P (j, true))⁻¹) (by simp), endPt_false_eq]
      | true =>
          rw [faceAux_true]
          cases t with
          | nil =>
              rw [faceAux_nil, List.append_nil, edgeTailPos_getLast]
              simp only [endPt_cons, endPt_nil]
          | cons y u =>
              have hne : faceAux D (a * CayV.genE P (j, true)) (y :: u) ≠ [] := by
                have h' := ih (a * CayV.genE P (j, true)) (by simp)
                intro hnil
                rw [hnil] at h'
                exact absurd h' (by simp)
              rw [List.getLast?_append_of_ne_nil (edgeTailPos D a j) hne,
                ih (a * CayV.genE P (j, true)) (by simp)]
              simp only [endPt_cons]

/-! ## The boundary walk of a face -/

theorem faceWalk_getLast {G : Type u} [Group G] {V : Type u} [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool)) : (Work.ORDunwoody.Dunwoody.faceWalk D c w).getLast? = some (Sum.inl (Work.ORDunwoody.Dunwoody.endPt P c w, Sum.inl ())) := by
  cases w with
  | nil => simp only [faceWalk_eq, faceAux_nil, endPt_nil, List.getLast?_singleton]
  | cons x t =>
      simp only [faceWalk_eq]
      have hne : faceAux D c (x :: t) ≠ [] := by
        have h := faceAux_getLast D (x :: t) (by simp) c
        intro hnil
        rw [hnil] at h
        exact absurd h (by simp)
      rw [List.getLast?_cons_of_ne_nil hne]
      exact faceAux_getLast D (x :: t) (by simp) c

end Work.ORDunwoody
