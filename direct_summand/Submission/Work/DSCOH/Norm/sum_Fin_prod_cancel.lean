import Mathlib

namespace Work.DSCOH.Norm

theorem sum_Fin_prod_cancel {M : Type*} [AddCommGroup M] {m : ℕ} (G : Fin (m+2) × Fin (m+1) → M)
    (hG : ∀ p : Fin (m+2) × Fin (m+1),
      G (p.1.succAbove p.2, p.2.predAbove p.1) = - G p) :
    ∑ p : Fin (m+2) × Fin (m+1), G p = 0 := by
  classical
  -- The map `σ` is a fixed-point-free involution pairing each term with its negative.
  refine Finset.sum_ninvolution
    (fun p : Fin (m+2) × Fin (m+1) => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩
    rw [hG (i, j)]
    simp
  · rintro ⟨i, j⟩ _
    intro h
    exact Fin.succAbove_ne i j (congrArg Prod.fst h)
  · intro a
    exact Finset.mem_univ _
  · rintro ⟨i, j⟩
    exact Prod.ext (Fin.succAbove_succAbove_predAbove i j) (Fin.predAbove_predAbove_succAbove i j)

end Work.DSCOH.Norm
