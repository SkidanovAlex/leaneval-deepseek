import Submission.Work.Stems.HomAdd.PrismDefs

/-!
# The faces of the prisms

For a side index `i : Fin n`:

* `killMapPos i` fixes the `(castSucc i,0)`-face of the cube pointwise (it *is* the `(castSucc i,1)`
  face), kills the `(castSucc i,1)`-face, the bottom face and the other side faces (they land in
  `InSkel n`), and sends the top face to the coordinate movement `rhoPos i`;
* `killMapNeg i` is the mirror image, with `rhoNeg i` in the top face.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.HomAdd

noncomputable section

variable {n : ℕ}

/-- `killMapPos i` maps the `(castSucc i,0)`-face onto the `(castSucc i,1)`-face. -/
theorem killMapPos_face_zero (i : Fin n) (v : IC n) :
    killMapPos i (faceCM (Fin.castSucc i) 0 v) = faceCM (Fin.castSucc i) 1 v := by
  funext j
  rcases eq_or_ne j (Fin.castSucc i) with h | h
  · subst h
    simp only [killMapPos_apply_castSucc, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq h
    subst hm
    by_cases hml : (Fin.castSucc i).succAbove m = Fin.last n
    · rw [hml, killMapPos_apply_last]
      simp only [faceCM_apply, Work.RatHurewicz.faceFun_apply_same,
        unitInterval.symm_zero, mul_one, ← hml, Work.RatHurewicz.faceFun_apply_succAbove]
    · simp only [killMapPos_apply_of_ne i h hml, faceCM_apply,
        Work.RatHurewicz.faceFun_apply_succAbove]

/-- `killMapNeg i` maps the `(castSucc i,1)`-face onto the `(castSucc i,0)`-face. -/
theorem killMapNeg_face_one (i : Fin n) (v : IC n) :
    killMapNeg i (faceCM (Fin.castSucc i) 1 v) = faceCM (Fin.castSucc i) 0 v := by
  funext j
  rcases eq_or_ne j (Fin.castSucc i) with h | h
  · subst h
    simp only [killMapNeg_apply_castSucc, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq h
    subst hm
    by_cases hml : (Fin.castSucc i).succAbove m = Fin.last n
    · rw [hml, killMapNeg_apply_last]
      simp only [faceCM_apply, Work.RatHurewicz.faceFun_apply_same,
        mul_one, ← hml, Work.RatHurewicz.faceFun_apply_succAbove]
    · simp only [killMapNeg_apply_of_ne i h hml, faceCM_apply,
        Work.RatHurewicz.faceFun_apply_succAbove]

/-- The coordinate movement in the top face of the `killMapPos`-prism. -/
def rhoPos (i : Fin n) (v : IC n) : IC n :=
  fun m => killMapPos i (faceCM (Fin.last n) 1 v) ((Fin.castSucc i).succAbove m)

/-- The coordinate movement in the top face of the `killMapNeg`-prism. -/
def rhoNeg (i : Fin n) (v : IC n) : IC n :=
  fun m => killMapNeg i (faceCM (Fin.last n) 1 v) ((Fin.castSucc i).succAbove m)

/-- The top face of the `killMapPos`-prism is the side face read through `rhoPos`. -/
theorem killMapPos_face_last_one (i : Fin n) (v : IC n) :
    killMapPos i (faceCM (Fin.last n) 1 v) = faceCM (Fin.castSucc i) 1 (rhoPos i v) := by
  funext j
  rcases eq_or_ne j (Fin.castSucc i) with h | h
  · subst h
    simp only [killMapPos_apply_castSucc, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq h
    rw [← hm]
    show killMapPos i (faceCM (Fin.last n) 1 v) ((Fin.castSucc i).succAbove m)
      = faceFun (Fin.castSucc i) 1 (rhoPos i v) ((Fin.castSucc i).succAbove m)
    rw [Work.RatHurewicz.faceFun_apply_succAbove]
    rfl

/-- The top face of the `killMapNeg`-prism is the side face read through `rhoNeg`. -/
theorem killMapNeg_face_last_one (i : Fin n) (v : IC n) :
    killMapNeg i (faceCM (Fin.last n) 1 v) = faceCM (Fin.castSucc i) 0 (rhoNeg i v) := by
  funext j
  rcases eq_or_ne j (Fin.castSucc i) with h | h
  · subst h
    simp only [killMapNeg_apply_castSucc, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq h
    rw [← hm]
    show killMapNeg i (faceCM (Fin.last n) 1 v) ((Fin.castSucc i).succAbove m)
      = faceFun (Fin.castSucc i) 0 (rhoNeg i v) ((Fin.castSucc i).succAbove m)
    rw [Work.RatHurewicz.faceFun_apply_succAbove]
    rfl

/-! ## The killed faces land in the skeleton -/

theorem killMapPos_face_one_mem_InSkel (i : Fin n) (v : IC n) :
    Work.RatHurewicz.InSkel n (killMapPos i (faceCM (Fin.castSucc i) 1 v)) := by
  have h1 : killMapPos i (faceCM (Fin.castSucc i) 1 v) (Fin.castSucc i) = 1 := by
    simp [killMapPos_apply, castSucc_ne_last i]
  have h2 : killMapPos i (faceCM (Fin.castSucc i) 1 v) (Fin.last n) = 0 := by
    simp [killMapPos_apply, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  exact ⟨Fin.castSucc i, Fin.last n, castSucc_ne_last i, Or.inr h1, Or.inl h2⟩

theorem killMapNeg_face_zero_mem_InSkel (i : Fin n) (v : IC n) :
    Work.RatHurewicz.InSkel n (killMapNeg i (faceCM (Fin.castSucc i) 0 v)) := by
  have h1 : killMapNeg i (faceCM (Fin.castSucc i) 0 v) (Fin.castSucc i) = 0 := by
    simp [killMapNeg_apply, castSucc_ne_last i]
  have h2 : killMapNeg i (faceCM (Fin.castSucc i) 0 v) (Fin.last n) = 0 := by
    simp [killMapNeg_apply, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  exact ⟨Fin.castSucc i, Fin.last n, castSucc_ne_last i, Or.inl h1, Or.inl h2⟩

theorem killMapPos_face_side_mem_InSkel (i : Fin n) {j : Fin (n + 1)}
    (hji : j ≠ Fin.castSucc i) (hjl : j ≠ Fin.last n) {b : unitInterval}
    (hb : b = 0 ∨ b = 1) (v : IC n) :
    Work.RatHurewicz.InSkel n (killMapPos i (faceCM j b v)) := by
  have h1 : killMapPos i (faceCM j b v) (Fin.castSucc i) = 1 := by
    simp [killMapPos_apply, castSucc_ne_last i]
  have h2 : killMapPos i (faceCM j b v) j = b := by
    simp [killMapPos_apply, hjl, hji, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  exact ⟨Fin.castSucc i, j, (Ne.symm hji), Or.inr h1, by rw [h2]; exact hb⟩

theorem killMapNeg_face_side_mem_InSkel (i : Fin n) {j : Fin (n + 1)}
    (hji : j ≠ Fin.castSucc i) (hjl : j ≠ Fin.last n) {b : unitInterval}
    (hb : b = 0 ∨ b = 1) (v : IC n) :
    Work.RatHurewicz.InSkel n (killMapNeg i (faceCM j b v)) := by
  have h1 : killMapNeg i (faceCM j b v) (Fin.castSucc i) = 0 := by
    simp [killMapNeg_apply, castSucc_ne_last i]
  have h2 : killMapNeg i (faceCM j b v) j = b := by
    simp [killMapNeg_apply, hjl, hji, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  exact ⟨Fin.castSucc i, j, (Ne.symm hji), Or.inl h1, by rw [h2]; exact hb⟩

theorem killMapPos_face_last_zero_mem_InSkel (i : Fin n) (v : IC n) :
    Work.RatHurewicz.InSkel n (killMapPos i (faceCM (Fin.last n) 0 v)) := by
  have h1 : killMapPos i (faceCM (Fin.last n) 0 v) (Fin.castSucc i) = 1 := by
    simp [killMapPos_apply, castSucc_ne_last i]
  have h2 : killMapPos i (faceCM (Fin.last n) 0 v) (Fin.last n) = 0 := by
    simp [killMapPos_apply, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  exact ⟨Fin.castSucc i, Fin.last n, (castSucc_ne_last i), Or.inr h1, Or.inl h2⟩

theorem killMapNeg_face_last_zero_mem_InSkel (i : Fin n) (v : IC n) :
    Work.RatHurewicz.InSkel n (killMapNeg i (faceCM (Fin.last n) 0 v)) := by
  have h1 : killMapNeg i (faceCM (Fin.last n) 0 v) (Fin.castSucc i) = 0 := by
    simp [killMapNeg_apply, castSucc_ne_last i]
  have h2 : killMapNeg i (faceCM (Fin.last n) 0 v) (Fin.last n) = 0 := by
    simp [killMapNeg_apply, faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  exact ⟨Fin.castSucc i, Fin.last n, (castSucc_ne_last i), Or.inl h1, Or.inl h2⟩

end

end Work.Stems.HomAdd
