import Mathlib

namespace Work.LT

/-- Kronecker products of two linearly independent families of words are linearly independent:
if `u : ι → (Fin Δ → ZMod 2)` and `v : κ → (Fin Δ → ZMod 2)` are linearly independent families over
finite index types, then so is `p ↦ (i,j) ↦ u p.1 i * v p.2 j`. -/
lemma linearIndependent_kronecker {Δ : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    {u : ι → (Fin Δ → ZMod 2)} {v : κ → (Fin Δ → ZMod 2)}
    (hu : LinearIndependent (ZMod 2) u) (hv : LinearIndependent (ZMod 2) v) :
    LinearIndependent (ZMod 2)
      (fun p : ι × κ => (fun ij : Fin Δ × Fin Δ => u p.1 ij.1 * v p.2 ij.2)) := by
  rw [Fintype.linearIndependent_iff] at hu hv ⊢
  intro G hG
  -- Evaluating the vanishing linear combination at `(a, b)`: `∑ p, G p * (u p.1 a * v p.2 b) = 0`.
  have hpoint : ∀ a b : Fin Δ, ∑ p : ι × κ, G p * (u p.1 a * v p.2 b) = 0 := by
    intro a b
    have h := congr_fun hG (a, b)
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  -- Fixing the second coordinate `b`, independence of `u` forces every coefficient
  -- `∑ j, G (i, j) * v j b` to vanish.
  have hcoef : ∀ (b : Fin Δ) (i : ι), ∑ j : κ, G (i, j) * v j b = 0 := by
    intro b i
    apply hu (fun i' => ∑ j : κ, G (i', j) * v j b)
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hpoint a b]
    rw [Fintype.sum_prod_type (f := fun p : ι × κ => G p * (u p.1 a * v p.2 b))]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  -- Those vanishing row-combinations, in turn, force `G` to vanish by independence of `v`.
  intro p
  obtain ⟨i, j⟩ := p
  have hrow : (∑ j' : κ, G (i, j') • v j') = 0 := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hcoef b i
  exact hv (fun j' => G (i, j')) hrow j

end Work.LT
