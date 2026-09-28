import Mathlib
import Submission.Work.Stems.Cubical.CubeFace

/-!
# Face algebra for the cubical `K`-operator

`faceCM i b : I^n → I^{n+1}` freezes the `i`-th coordinate at `b`; it is `Fin.insertNth i b`.
This file collects the elementary identities used by the construction of the filling family
`Work.RatHurewicz.exists_fillingFamily`.  Everything is stated with explicit lambdas and
`@Fin.insertNth` so that the (unavoidably dependent) type family does not have to be inferred.

* `initC` — the "space part" of a cube point (the last coordinate dropped);
* the last face is `Fin.snoc`;
* a face in a "space" direction preserves the last (time) coordinate and acts as `Fin.insertNth`
  on the space part;
* the deletion/insertion round trip along `Fin.succAbove`.
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz

open Work.Stems.Cubical

/-- The "space part" of a point of `I^{n+1}`: the last coordinate is dropped. -/
def initC (n : ℕ) (z : IC (n + 1)) : IC n := fun k => z k.castSucc

@[simp] theorem initC_apply {n : ℕ} (z : IC (n + 1)) (k : Fin n) : initC n z k = z k.castSucc := rfl

/-- `faceCM i b` is `Fin.insertNth i b`. -/
theorem faceCM_eq_insertNth {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (u : IC n) :
    faceCM i b u = i.insertNth b u := rfl

/-- The last face of a cube is `Fin.snoc`. -/
theorem faceCM_last {n : ℕ} (b : unitInterval) (u : IC n) :
    faceCM (Fin.last n) b u = Fin.snoc u b := by
  funext i
  rw [faceCM_eq_insertNth]
  cases i using Fin.lastCases with
  | last => rw [Fin.insertNth_apply_same, Fin.snoc_last]
  | cast j =>
      have h1 : (Fin.last n).succAbove j = j.castSucc := by rw [Fin.succAbove_last]
      rw [← h1, Fin.insertNth_apply_succAbove, h1, Fin.snoc_castSucc]

/-- A face in a space direction preserves the last (time) coordinate. -/
theorem last_faceCM_castSucc {n : ℕ} (j : Fin (n + 1)) (b : unitInterval) (z : IC (n + 1)) :
    (faceCM (Fin.castSucc j) b z) (Fin.last (n + 1)) = z (Fin.last n) := by
  rw [faceCM_eq_insertNth]
  have hlast : Fin.last (n + 1) = (Fin.last n).succ := Fin.ext (by simp)
  rw [hlast, show (Fin.last n).succ = j.castSucc.succAbove (Fin.last n) from by
    rw [Fin.succAbove_castSucc_of_le j (Fin.last n) (Fin.le_last j)]]
  rw [Fin.insertNth_apply_succAbove]

/-- `j.succAbove` composed with `castSucc` is `(castSucc j).succAbove` applied to `castSucc`. -/
theorem succAbove_castSucc_eq {n : ℕ} (j : Fin (n + 1)) (k : Fin n) :
    (j.succAbove k).castSucc = (Fin.castSucc j).succAbove (Fin.castSucc k) := by
  rw [Fin.succAbove, Fin.succAbove]
  by_cases h : (k.castSucc : Fin (n + 1)) < j
  · rw [if_pos h, if_pos (by simpa using h)]
  · rw [if_neg h, if_neg (by simpa using h)]
    apply Fin.ext
    simp

/-- The face `{z j = z j}` of a cube is `z` itself. -/
theorem insertNth_succAbove_self {n : ℕ} (j : Fin (n + 1)) (u : IC (n + 1)) :
    @Fin.insertNth n (fun _ => unitInterval) j (u j) (fun k => u (j.succAbove k)) = u := by
  funext i
  rcases eq_or_ne i j with h | h
  · subst h; exact Fin.insertNth_apply_same _ _ _
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    rw [← hk, Fin.insertNth_apply_succAbove]

/-- **Space-face dictionary**: on the space part, the face `faceCM (castSucc j) b` inserts `b` at
the `j`-th coordinate. -/
theorem initC_insertNth_castSucc {n : ℕ} (j : Fin (n + 1)) (b : unitInterval)
    (z : IC (n + 1)) :
    initC (n + 1) ((Fin.castSucc j).insertNth b z : IC (n + 2)) =
      @Fin.insertNth n (fun _ => unitInterval) j b (initC n z) := by
  funext i
  change (((Fin.castSucc j).insertNth b z : IC (n + 2)) i.castSucc) = _
  rcases eq_or_ne i j with h | h
  · subst h
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    rw [show (@Fin.insertNth n (fun _ => unitInterval) j b (initC n z)) i = (initC n z) k from by
      rw [← hk]; exact Fin.insertNth_apply_succAbove _ _ _ k]
    rw [show i.castSucc = (Fin.castSucc j).succAbove (Fin.castSucc k) from by
      rw [← succAbove_castSucc_eq, hk]]
    rw [Fin.insertNth_apply_succAbove]
    rfl

/-- The **space-face dictionary** in terms of `faceCM`: the space part of a space face is the
insertion of `b` at the `j`-th coordinate. -/
theorem initC_faceCM_castSucc {n : ℕ} (j : Fin (n + 1)) (b : unitInterval) (z : IC (n + 1)) :
    initC (n + 1) (faceCM (Fin.castSucc j) b z) =
      @Fin.insertNth n (fun _ => unitInterval) j b (initC n z) :=
  initC_insertNth_castSucc j b z

end Work.RatHurewicz
