import Mathlib
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Norm.HomoStruct

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

/-- Deleting, from the tuple `dup z b` (which repeats the entry `z b` at the positions `b` and
`b + 1`), any position `c` lying in the constant block `[b, m]` of `z`, gives back `z`.

Maths: `dup z b` agrees with `z` above position `b`, and inserting a repeat at `b` shifts the
entries `b+1, …,` one step up.  Deleting a position `c ≥ b` undoes that shift everywhere except
on the interval `(b, c)`, where one compares `z (j - 1)` with `z j`; both lie in the block
`[b, m]` on which `z` is constant by `hblock`.  The two extreme cases `c = b` and `c = b + 1`
remove one of the two copies of `z b`. -/
lemma del_dup_eq_self {L : ℕ} {ι : Type*} (z : Fin (L + 1) → ι) (b : Fin (L + 1)) (m : ℕ)
    (hblock : ∀ i : Fin L, (b : ℕ) ≤ (i : ℕ) → (i : ℕ) + 2 ≤ m → z i.castSucc = z i.succ)
    (c : Fin (L + 2)) (h1 : (b : ℕ) ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ m) :
    Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup z b) c = z := by
  funext j
  simp only [del_apply, dup_apply]
  by_cases hjc : (j : ℕ) < (c : ℕ)
  · -- `j < c`: the index `j` is not moved by the deletion of `c`
    have hsa : c.succAbove j = (j.castSucc : Fin (L + 2)) :=
      Fin.succAbove_of_castSucc_lt c j (by rw [Fin.lt_def]; simpa using hjc)
    rw [hsa]
    by_cases hbj : (b : ℕ) < (j : ℕ)
    · -- `b < j < c`: here the duplication at `b` still shifts `j` down by one
      have hbcast : b < j := by rw [Fin.lt_def]; simpa using hbj
      have hjne : j ≠ 0 := by
        intro h
        rw [h] at hbj
        simp at hbj
      let i : Fin L := j.pred hjne
      have hival : (i : ℕ) = (j : ℕ) - 1 := Fin.val_pred j hjne
      have hisucc : i.succ = j := Fin.succ_pred j hjne
      have hkey : b.predAbove (j.castSucc : Fin (L + 2)) = i.castSucc := by
        rw [Fin.predAbove_castSucc_of_lt b j hbcast]
        apply Fin.ext
        simp only [Fin.val_pred, Fin.val_castSucc, hival]
      rw [hkey]
      have hb1 : (b : ℕ) ≤ (i : ℕ) := by omega
      have hb2 : (i : ℕ) + 2 ≤ m := by omega
      simpa only [hisucc] using hblock i hb1 hb2
    · -- `j ≤ b`: below the duplicated block nothing is shifted
      have hle : j ≤ b := Fin.le_iff_val_le_val.mpr (not_lt.mp hbj)
      rw [Fin.predAbove_castSucc_of_le b j hle]
  · -- `c ≤ j`: the entry read at `j` comes from position `j + 1`, which is past the block
    have hle_cj : (c : ℕ) ≤ (j : ℕ) := not_lt.mp hjc
    have hsa : c.succAbove j = j.succ :=
      Fin.succAbove_of_le_castSucc c j (by rw [Fin.le_def]; simpa using hle_cj)
    rw [hsa]
    have hle : b ≤ j := Fin.le_iff_val_le_val.mpr (le_trans h1 hle_cj)
    rw [Fin.predAbove_succ_of_le b j hle]

end Work.DSCOH.Struct
