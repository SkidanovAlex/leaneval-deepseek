import Mathlib

namespace Work.MainP

/-- A list of length `S` is the list of its entries indexed by `Fin S`, read with `getD`. -/
theorem permOfGetD_ofFn_getD {α : Type} {l : List α} {S : ℕ} (d : α) (h : l.length = S) :
    List.ofFn (fun i : Fin S => l.getD (i : ℕ) d) = l := by
  apply List.ext_getElem
  · simp [List.length_ofFn, h]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem l d h2

theorem permOfGetD {α : Type} {S : ℕ} {l l' : List α} (σ : Equiv.Perm (Fin S)) (d : α)
    (hl : l.length = S) (hl' : l'.length = S)
    (h : ∀ i : Fin S, l.getD (i : ℕ) d = l'.getD ((σ i : Fin S) : ℕ) d) : l.Perm l' := by
  rw [← permOfGetD_ofFn_getD (l := l) d hl, ← permOfGetD_ofFn_getD (l := l') d hl']
  have hof : (fun i : Fin S => l.getD (i : ℕ) d)
      = ((fun j : Fin S => l'.getD (j : ℕ) d) ∘ σ) := by
    funext i
    exact h i
  rw [hof]
  exact Equiv.Perm.ofFn_comp_perm σ (fun j : Fin S => l'.getD (j : ℕ) d)

end Work.MainP
