import Mathlib
import Submission.Work.RatHurewicz.cubePinchDefs
import Submission.Work.RatHurewicz.PsiKillsAux

/-!
# The prism maps of the general homotopy addition theorem (`PinchAll`)

Sets up the *prism* construction of the elementary proof of Hutchings' `(2.2b)`
(`Work.RatHurewicz.PinchAll`).

The cube is `I^{n+1}`, whose coordinates are indexed by `Fin (n+1)`; the *side* coordinates are
those of `Fin n` (embedded by `Fin.castSucc`) and the last coordinate is `Fin.last n`.

For a side index `i : Fin n`, the two *kill maps* are the self-maps of the cube

* `killMapPos i z = z` with `z (castSucc i) := 1` and `z last := z last * (1 - z (castSucc i))`,
* `killMapNeg i z = z` with `z (castSucc i) := 0` and `z last := z last * z (castSucc i)`.

Both send `InSkel n` into `InSkel n`, so the composites `g ∘ killMap` are again cubes that are `y`
on the skeleton.  Their faces are computed here; the top face involves the *coordinate movement*
`rhoPos`/`rhoNeg` (the coordinate `castSucc i` moves into the last slot, with a reflection in the
case `Pos`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.HomAdd

noncomputable section

variable {n : ℕ}

/-- The prism map killing the `(castSucc i,1)`-face:
`z ↦ (z with z (castSucc i) := 1, z last := z last * (1 - z (castSucc i)))`. -/
def killMapPos (i : Fin n) (z : IC (n + 1)) : IC (n + 1) :=
  Function.update (Function.update z (Fin.castSucc i) 1) (Fin.last n)
    (z (Fin.last n) * unitInterval.symm (z (Fin.castSucc i)))

/-- The prism map killing the `(castSucc i,0)`-face:
`z ↦ (z with z (castSucc i) := 0, z last := z last * z (castSucc i))`. -/
def killMapNeg (i : Fin n) (z : IC (n + 1)) : IC (n + 1) :=
  Function.update (Function.update z (Fin.castSucc i) 0) (Fin.last n)
    (z (Fin.last n) * z (Fin.castSucc i))

theorem castSucc_ne_last (i : Fin n) : Fin.castSucc i ≠ Fin.last n :=
  ne_of_lt (Fin.castSucc_lt_last i)

theorem last_ne_castSucc (i : Fin n) : Fin.last n ≠ Fin.castSucc i :=
  (castSucc_ne_last i).symm

@[simp] theorem killMapPos_apply (i : Fin n) (z : IC (n + 1)) (j : Fin (n + 1)) :
    killMapPos i z j
      = if j = Fin.last n then z (Fin.last n) * unitInterval.symm (z (Fin.castSucc i))
        else if j = Fin.castSucc i then 1 else z j := by
  simp only [killMapPos, Function.update_apply]

@[simp] theorem killMapNeg_apply (i : Fin n) (z : IC (n + 1)) (j : Fin (n + 1)) :
    killMapNeg i z j
      = if j = Fin.last n then z (Fin.last n) * z (Fin.castSucc i)
        else if j = Fin.castSucc i then 0 else z j := by
  simp only [killMapNeg, Function.update_apply]

theorem killMapPos_apply_castSucc (i : Fin n) (z : IC (n + 1)) :
    killMapPos i z (Fin.castSucc i) = 1 := by
  simp [killMapPos_apply, castSucc_ne_last i]

theorem killMapPos_apply_last (i : Fin n) (z : IC (n + 1)) :
    killMapPos i z (Fin.last n)
      = z (Fin.last n) * unitInterval.symm (z (Fin.castSucc i)) := by
  simp [killMapPos_apply]

theorem killMapPos_apply_of_ne (i : Fin n) {j : Fin (n + 1)} (hji : j ≠ Fin.castSucc i)
    (hjl : j ≠ Fin.last n) (z : IC (n + 1)) : killMapPos i z j = z j := by
  simp [killMapPos_apply, hji, hjl]

theorem killMapNeg_apply_castSucc (i : Fin n) (z : IC (n + 1)) :
    killMapNeg i z (Fin.castSucc i) = 0 := by
  simp [killMapNeg_apply, castSucc_ne_last i]

theorem killMapNeg_apply_last (i : Fin n) (z : IC (n + 1)) :
    killMapNeg i z (Fin.last n) = z (Fin.last n) * z (Fin.castSucc i) := by
  simp [killMapNeg_apply]

theorem killMapNeg_apply_of_ne (i : Fin n) {j : Fin (n + 1)} (hji : j ≠ Fin.castSucc i)
    (hjl : j ≠ Fin.last n) (z : IC (n + 1)) : killMapNeg i z j = z j := by
  simp [killMapNeg_apply, hji, hjl]

theorem continuous_killMapPos (i : Fin n) : Continuous (killMapPos i) := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = Fin.last n
  · subst hj
    have hfun : (fun z : IC (n + 1) => killMapPos i z (Fin.last n))
        = fun z => z (Fin.last n) * unitInterval.symm (z (Fin.castSucc i)) := by
      funext z; rw [killMapPos_apply, if_pos rfl]
    rw [hfun]
    exact (continuous_apply (Fin.last n)).mul
      (unitInterval.continuous_symm.comp (continuous_apply (Fin.castSucc i)))
  · by_cases hji : j = Fin.castSucc i
    · subst hji
      have hfun : (fun z : IC (n + 1) => killMapPos i z (Fin.castSucc i))
          = fun _ => (1 : unitInterval) := by
        funext z; rw [killMapPos_apply, if_neg hj, if_pos rfl]
      rw [hfun]; exact continuous_const
    · have hfun : (fun z : IC (n + 1) => killMapPos i z j) = fun z => z j := by
        funext z; rw [killMapPos_apply, if_neg hj, if_neg hji]
      rw [hfun]; exact continuous_apply j

theorem continuous_killMapNeg (i : Fin n) : Continuous (killMapNeg i) := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = Fin.last n
  · subst hj
    have hfun : (fun z : IC (n + 1) => killMapNeg i z (Fin.last n))
        = fun z => z (Fin.last n) * z (Fin.castSucc i) := by
      funext z; rw [killMapNeg_apply, if_pos rfl]
    rw [hfun]
    exact (continuous_apply (Fin.last n)).mul (continuous_apply (Fin.castSucc i))
  · by_cases hji : j = Fin.castSucc i
    · subst hji
      have hfun : (fun z : IC (n + 1) => killMapNeg i z (Fin.castSucc i))
          = fun _ => (0 : unitInterval) := by
        funext z; rw [killMapNeg_apply, if_neg hj, if_pos rfl]
      rw [hfun]; exact continuous_const
    · have hfun : (fun z : IC (n + 1) => killMapNeg i z j) = fun z => z j := by
        funext z; rw [killMapNeg_apply, if_neg hj, if_neg hji]
      rw [hfun]; exact continuous_apply j

/-- The prism map as a continuous map. -/
def killCMpos (i : Fin n) : C(IC (n + 1), IC (n + 1)) :=
  ⟨killMapPos i, continuous_killMapPos i⟩

/-- The prism map as a continuous map. -/
def killCMneg (i : Fin n) : C(IC (n + 1), IC (n + 1)) :=
  ⟨killMapNeg i, continuous_killMapNeg i⟩

@[simp] theorem killCMpos_apply (i : Fin n) (z : IC (n + 1)) :
    killCMpos i z = killMapPos i z := rfl

@[simp] theorem killCMneg_apply (i : Fin n) (z : IC (n + 1)) :
    killCMneg i z = killMapNeg i z := rfl

/-- A product of two unit-interval elements is extreme when one factor is `0`, or both are `1`. -/
theorem mul_extreme' {a b : unitInterval} (h : a = 0 ∨ b = 0 ∨ (a = 1 ∧ b = 1)) :
    a * b = 0 ∨ a * b = 1 := by
  rcases h with h | h | ⟨h1, h2⟩
  · left; rw [h, zero_mul]
  · left; rw [h, mul_zero]
  · right; rw [h1, h2, mul_one]

/-- A product `a * (1 - b)` is extreme when `a = 0`, or `a = 1` and `b` is extreme. -/
theorem mul_symm_extreme {a b : unitInterval} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * unitInterval.symm b = 0 ∨ a * unitInterval.symm b = 1 := by
  rcases ha with h | h
  · left; rw [h, zero_mul]
  · rcases hb with h' | h'
    · right; rw [h, h', unitInterval.symm_zero, mul_one]
    · left; rw [h, h', unitInterval.symm_one, mul_zero]

/-- If `z` is extreme at `j` away from the moved coordinate, then `killMapPos i z` is extreme at
`j` as soon as either `j` is not the last coordinate or `z` is extreme at the moved coordinate. -/
theorem killMapPos_extreme (i : Fin n) {z : IC (n + 1)} {j : Fin (n + 1)}
    (hji : j ≠ Fin.castSucc i) (hj : z j = 0 ∨ z j = 1)
    (hl : j ≠ Fin.last n ∨ z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1) :
    (killMapPos i z) j = 0 ∨ (killMapPos i z) j = 1 := by
  by_cases hjl : j = Fin.last n
  · subst hjl
    rw [killMapPos_apply, if_pos rfl]
    rcases hl with hl | hl | hl
    · exact absurd rfl hl
    · exact mul_symm_extreme hj (Or.inl hl)
    · exact mul_symm_extreme hj (Or.inr hl)
  · rw [killMapPos_apply, if_neg hjl, if_neg hji]
    exact hj

/-- If `z` is extreme at `j` away from the moved coordinate, then `killMapNeg i z` is extreme at
`j` as soon as either `j` is not the last coordinate or `z` is extreme at the moved coordinate. -/
theorem killMapNeg_extreme (i : Fin n) {z : IC (n + 1)} {j : Fin (n + 1)}
    (hji : j ≠ Fin.castSucc i) (hj : z j = 0 ∨ z j = 1)
    (hl : j ≠ Fin.last n ∨ z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1) :
    (killMapNeg i z) j = 0 ∨ (killMapNeg i z) j = 1 := by
  by_cases hjl : j = Fin.last n
  · subst hjl
    rw [killMapNeg_apply, if_pos rfl]
    rcases hl with hl | hl | hl
    · exact absurd rfl hl
    · exact mul_extreme' (Or.inr (Or.inl hl))
    · rcases hj with hj0 | hj1
      · exact mul_extreme' (Or.inl hj0)
      · exact mul_extreme' (Or.inr (Or.inr ⟨hj1, hl⟩))
  · rw [killMapNeg_apply, if_neg hjl, if_neg hji]
    exact hj

/-- `killMapPos` sends a point of `InSkel n` into `InSkel n`. -/
theorem killMapPos_mem_InSkel (i : Fin n) {z : IC (n + 1)}
    (hz : Work.RatHurewicz.InSkel n z) : Work.RatHurewicz.InSkel n (killMapPos i z) := by
  obtain ⟨j, j', hjj, hj, hj'⟩ := hz
  have hself : (killMapPos i z) (Fin.castSucc i) = 1 := by
    rw [killMapPos_apply, if_neg (castSucc_ne_last i), if_pos rfl]
  rcases eq_or_ne j (Fin.castSucc i) with hji | hji
  · have hj'i : j' ≠ Fin.castSucc i := fun h => hjj (hji.trans h.symm)
    have hzi : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1 := by rw [← hji]; exact hj
    exact ⟨Fin.castSucc i, j', Ne.symm hj'i, Or.inr hself,
      killMapPos_extreme i hj'i hj' (Or.inr hzi)⟩
  · by_cases hjl : j = Fin.last n
    · by_cases hzi : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1
      · exact ⟨Fin.castSucc i, j, Ne.symm hji, Or.inr hself,
          killMapPos_extreme i hji hj (Or.inr hzi)⟩
      · have hj'i : j' ≠ Fin.castSucc i := fun h => hzi (h ▸ hj')
        have hj'l : j' ≠ Fin.last n := fun h => hjj (hjl.trans h.symm)
        exact ⟨Fin.castSucc i, j', Ne.symm hj'i, Or.inr hself,
          killMapPos_extreme i hj'i hj' (Or.inl hj'l)⟩
    · exact ⟨Fin.castSucc i, j, Ne.symm hji, Or.inr hself,
        killMapPos_extreme i hji hj (Or.inl hjl)⟩

/-- `killMapNeg` sends a point of `InSkel n` into `InSkel n`. -/
theorem killMapNeg_mem_InSkel (i : Fin n) {z : IC (n + 1)}
    (hz : Work.RatHurewicz.InSkel n z) : Work.RatHurewicz.InSkel n (killMapNeg i z) := by
  obtain ⟨j, j', hjj, hj, hj'⟩ := hz
  have hself : (killMapNeg i z) (Fin.castSucc i) = 0 := by
    rw [killMapNeg_apply, if_neg (castSucc_ne_last i), if_pos rfl]
  rcases eq_or_ne j (Fin.castSucc i) with hji | hji
  · have hj'i : j' ≠ Fin.castSucc i := fun h => hjj (hji.trans h.symm)
    have hzi : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1 := by rw [← hji]; exact hj
    exact ⟨Fin.castSucc i, j', Ne.symm hj'i, Or.inl hself,
      killMapNeg_extreme i hj'i hj' (Or.inr hzi)⟩
  · by_cases hjl : j = Fin.last n
    · by_cases hzi : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1
      · exact ⟨Fin.castSucc i, j, Ne.symm hji, Or.inl hself,
          killMapNeg_extreme i hji hj (Or.inr hzi)⟩
      · have hj'i : j' ≠ Fin.castSucc i := fun h => hzi (h ▸ hj')
        have hj'l : j' ≠ Fin.last n := fun h => hjj (hjl.trans h.symm)
        exact ⟨Fin.castSucc i, j', Ne.symm hj'i, Or.inl hself,
          killMapNeg_extreme i hj'i hj' (Or.inl hj'l)⟩
    · exact ⟨Fin.castSucc i, j, Ne.symm hji, Or.inl hself,
        killMapNeg_extreme i hji hj (Or.inl hjl)⟩

end

end Work.Stems.HomAdd
