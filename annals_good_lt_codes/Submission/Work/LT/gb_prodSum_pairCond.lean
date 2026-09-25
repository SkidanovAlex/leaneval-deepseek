import Mathlib
import Submission.Work.LT.good_base_defs

namespace Work.LT

open scoped BigOperators

namespace GB

/-- If every column of `a` is orthogonal to `H1 k`, then `a` pairs to zero with `H1 k`
against any right factor: `dot (H1 k) (matVec a w) = 0`. -/
lemma dot_matVec_col_eq_zero {D r : ℕ} (H1 : Fin r → Fin D → ZMod 2) (k : Fin r)
    (a : Fin D × Fin D → ZMod 2) (ha : ∀ j, dot (H1 k) (col a j) = 0)
    (w : Fin D → ZMod 2) : dot (H1 k) (matVec a w) = 0 := by
  simp only [dot, matVec, col] at ha ⊢
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h1 : (∑ i, H1 k i * (a (i, j) * w j)) = (∑ i, H1 k i * a (i, j)) * w j := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, ha j, zero_mul]

/-- If every row of `b` is orthogonal to `H2 l`, then `b` pairs to zero with `H1 k`
against the right factor `H2 l`: `dot (H1 k) (matVec b (H2 l)) = 0`. -/
lemma dot_matVec_row_eq_zero {D r : ℕ} (H1 : Fin r → Fin D → ZMod 2) (k : Fin r)
    (H2 : Fin r → Fin D → ZMod 2) (l : Fin r)
    (b : Fin D × Fin D → ZMod 2) (hb : ∀ i, dot (H2 l) (row b i) = 0) :
    dot (H1 k) (matVec b (H2 l)) = 0 := by
  simp only [dot, matVec, row] at hb ⊢
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h : (∑ j, b (i, j) * H2 l j) = (∑ j, H2 l j * b (i, j)) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [h, hb i, mul_zero]

/-- Additivity of the pairing `x ↦ dot (H1 k) (matVec x w)`. -/
lemma dot_matVec_add {D r : ℕ} (H1 : Fin r → Fin D → ZMod 2) (k : Fin r)
    (a b : Fin D × Fin D → ZMod 2) (w : Fin D → ZMod 2) :
    dot (H1 k) (matVec (a + b) w) = dot (H1 k) (matVec a w) + dot (H1 k) (matVec b w) := by
  simp only [dot, matVec, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

end GB

/-- If `x` lies in the sum of the two parity-check codes `ker H₁` and `ker H₂` (column-wise for the first, row-wise for the second), then `H₁ x H₂ᵀ = 0` in coordinates, i.e. `pairCond H₁ H₂ x`.  This is the easy containment `C₁ ⊗ 𝔽 + 𝔽 ⊗ C₂ ⊆ (C₁^⊥ ⊗ C₂^⊥)^⊥`. -/
theorem gb_prodSum_pairCond {D r : ℕ} (H1 H2 : Fin r → Fin D → ZMod 2)
    (x : Fin D × Fin D → ZMod 2) (hx : x ∈ GB.prodSum (GB.kerCode H1) (GB.kerCode H2)) :
    GB.pairCond H1 H2 x := by
  intro k l
  rw [GB.mem_prodSum] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [GB.mem_colCode] at ha
  rw [GB.mem_rowCode] at hb
  have ha' : ∀ j, GB.dot (H1 k) (GB.col a j) = 0 := fun j => (GB.mem_kerCode.mp (ha j)) k
  have hb' : ∀ i, GB.dot (H2 l) (GB.row b i) = 0 := fun i => (GB.mem_kerCode.mp (hb i)) l
  rw [GB.dot_matVec_add H1 k a b (H2 l), GB.dot_matVec_col_eq_zero H1 k a ha' (H2 l),
    GB.dot_matVec_row_eq_zero H1 k H2 l b hb', add_zero]

end Work.LT
