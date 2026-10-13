import Mathlib

namespace Work.WilG4c

theorem CardFinFilterIco {m lo t : ℕ} (h : lo + t ≤ m) :
    (Finset.univ.filter (fun j : Fin m => lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + t)).card = t := by
  have hbij : (Finset.univ : Finset (Fin t)).card =
      (Finset.univ.filter (fun j : Fin m => lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + t)).card := by
    refine Finset.card_bij (fun i _ => (⟨lo + (i : ℕ), ?_⟩ : Fin m)) ?_ ?_ ?_
    · have := i.isLt; omega
    · intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := i.isLt; omega
    · intro i1 _ i2 _ heq
      apply Fin.ext
      have := congrArg Fin.val heq
      simp only at this
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨⟨(b : ℕ) - lo, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only
      omega
  rw [← hbij, Finset.card_fin]

end Work.WilG4c
