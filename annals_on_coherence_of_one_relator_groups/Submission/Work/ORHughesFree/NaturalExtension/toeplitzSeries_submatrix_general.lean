import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.exists_powerSeriesToeplitz
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.NaturalExtension

theorem toeplitzSeries_submatrix_general {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    (p : Work.ORHughesFree.SkewLaurentSeries U) (i : ℤ) (a : U) (hi : p.1 i = a)
    (hlo : ∀ k : ℤ, k < i → p.1 k = 0) (N pp q : ℕ)
    (hdiff : ((q : ℕ) : ℤ) - ((pp : ℕ) : ℤ) = i) (hN : pp + q < N) :
    (∀ c d : Fin (N - (pp + q)), (d : ℕ) < (c : ℕ) →
      (Work.ORHughesFree.NaturalExtension.toeplitzSeries N p).submatrix
        (fun c : Fin (N - (pp + q)) => (⟨pp + c.1, by omega⟩ : Fin N))
        (fun d : Fin (N - (pp + q)) => (⟨q + d.1, by omega⟩ : Fin N)) c d = 0) ∧
    (∀ c : Fin (N - (pp + q)),
      (Work.ORHughesFree.NaturalExtension.toeplitzSeries N p).submatrix
        (fun c : Fin (N - (pp + q)) => (⟨pp + c.1, by omega⟩ : Fin N))
        (fun d : Fin (N - (pp + q)) => (⟨q + d.1, by omega⟩ : Fin N)) c c
      = (Multiplicative.ofAdd ((pp + c.1 : ℕ) : ℤ)) • a) := by
  constructor
  · intro c d hcd
    simp only [Matrix.submatrix_apply, toeplitzSeries_apply]
    have hlt : (((q + d.1 : ℕ) : ℤ) - ((pp + c.1 : ℕ) : ℤ)) < i := by
      have hcast : ((q + d.1 : ℕ) : ℤ) - ((pp + c.1 : ℕ) : ℤ)
          = i + ((d.1 : ℤ) - (c.1 : ℤ)) := by omega
      rw [hcast]
      have hdc : (d.1 : ℤ) - (c.1 : ℤ) < 0 := by omega
      linarith
    rw [hlo _ hlt, smul_zero]
  · intro c
    simp only [Matrix.submatrix_apply, toeplitzSeries_apply]
    have hidx : (((q + c.1 : ℕ) : ℤ) - ((pp + c.1 : ℕ) : ℤ)) = i := by omega
    rw [hidx, hi]

end Work.ORHughesFree.NaturalExtension
