import Mathlib
import Submission.Work.Resample.axKit
import Submission.Work.Resample.fx
import Submission.Work.Resample.fxTensorErr

/-!
# Reading `axisFx1Gen` at a flat index

`axisFx1Gen s t B Ψ u` applies `Ψ` along the first axis of a flat `s × B` array.  At the flat index
`g * B + i` (`g < t`, `i < B`) this reads the `i`-th column, i.e. the slice
`j ↦ u (j * B + i)`, at position `g`.
-/

set_option autoImplicit false

namespace Work.Resample

theorem axisFx1Gen_getD (s t B : ℕ) (Ψ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ))
    (v : Fin (s * B) → ℤ × ℤ) (ht : 0 < t) (hB : 0 < B) (g i : ℕ) (hg : g < t) (hi : i < B) :
    Work.Resample.axisFx1Gen s t B Ψ v ⟨g * B + i, Work.Resample.mul_add_lt_mul hg hi⟩ =
      Ψ (fun j : Fin s => v ⟨(j : ℕ) * B + i, Work.Resample.mul_add_lt_mul j.isLt hi⟩)
        ⟨g, hg⟩ := by
  rw [axisFx1Gen]
  have hdiv : (g * B + i) / B = g := by
    rw [Nat.mul_comm g B, Nat.mul_add_div hB g i, Nat.div_eq_of_lt hi, Nat.add_zero]
  have hmod : (g * B + i) % B = i := by
    rw [Nat.mul_comm g B, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hi]
  have hcond : (⟨g * B + i, mul_add_lt_mul hg hi⟩ : Fin (t * B)).val / B < t := by
    simp only; rw [hdiv]; exact hg
  rw [dite_eq_left hcond]
  have hf : (fun j : Fin s => zget v ((j : ℕ) * B + (g * B + i) % B))
      = (fun j : Fin s => v ⟨(j : ℕ) * B + i, mul_add_lt_mul j.isLt hi⟩) := by
    funext j
    simp only [zget, hmod]
    rw [dite_eq_left (mul_add_lt_mul j.isLt hi)]
  rw [hf]
  rw [show (⟨(g * B + i) / B, hcond⟩ : Fin t) = ⟨g, hg⟩ from Fin.ext hdiv]

end Work.Resample
