import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenPsi

namespace Work.Idx

open Matrix

noncomputable section

variable {A : Type*} [CommRing A]

/-- **Entry computation of `wRow * wProj`.**

The `(a, (i,β))`-entry of the block-row-by-block-matrix product `wRow n D c * wProj n D c Ψ`
equals the `(a,β)`-entry of the matrix `∑_k c_k * (∑_{j>i} Ψ_{k+j-1-i} * c_j)`: the block index
`k` and the inner index of the row are combined into the single matrix product `c_k * _`. -/
lemma wRow_mul_wProj_apply (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A)
    (Ψ : ℤ → Matrix (Fin n) (Fin n) A) (a : Fin n) (i : Fin (D + 1)) (β : Fin n) :
    (wRow n D c * wProj n D c Ψ) a (i, β)
      = (∑ k : Fin (D + 1), c k * (∑ j ∈ Finset.univ.filter (fun j : Fin (D + 1) => i < j),
            Ψ ((k : ℤ) + (j : ℤ) - 1 - (i : ℤ)) * c j)) a β := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [wRow, wProj]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply]

/-- **The block row annihilates the block projection.**

Under the Fourier relation `hΨ : ∑_k c_k * Ψ_{k+p} = 0` for every `p ≠ -1`, the block product
`∑_k c_k * (∑_{j>i} Ψ_{k+j-1-i} * c_j)` vanishes: interchange the `k`- and `j`-sums and use that
`j > i` forces `j - 1 - i ≠ -1`. -/
lemma wRowB_mul_wProjB_zero (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A)
    (Ψ : ℤ → Matrix (Fin n) (Fin n) A)
    (hΨ : ∀ p : ℤ, p ≠ -1 → ∑ k : Fin (D + 1), c k * Ψ ((k : ℤ) + p) = 0)
    (i : Fin (D + 1)) :
    (∑ k : Fin (D + 1), c k * (∑ j ∈ Finset.univ.filter (fun j : Fin (D + 1) => i < j),
        Ψ ((k : ℤ) + (j : ℤ) - 1 - (i : ℤ)) * c j)) = 0 := by
  simp_rw [Matrix.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Matrix.mul_assoc, ← Finset.sum_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : i < j := (Finset.mem_filter.mp hj).2
  have hp : ((j : ℤ) - 1 - (i : ℤ)) ≠ -1 := by
    have hlt : (i : ℤ) < (j : ℤ) := by exact_mod_cast hj'
    omega
  have hpe : (∑ k : Fin (D + 1), c k * Ψ ((k : ℤ) + (j : ℤ) - 1 - (i : ℤ)))
      = ∑ k : Fin (D + 1), c k * Ψ ((k : ℤ) + ((j : ℤ) - 1 - (i : ℤ))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 2
    ring
  rw [hpe, hΨ ((j : ℤ) - 1 - (i : ℤ)) hp, zero_mul]

/-- **The coefficient row annihilates the projection.**

`wRow n D c : Matrix (Fin n) (Fin (D+1) × Fin n)` is the block row whose `k`-th block is `c_k`,
`wProj n D c Ψ` is the block matrix with block `(k,i)` equal to `∑_{j > i} Ψ_{k+j-1-i} * c_j`, and
`wPsi X n D c` is the Fourier data `(2πi)⁻¹ ∮_{|z|=1} z^m • (wQ n D c z)⁻¹ dz` of the polynomial
matrix `wQ n D c z = ∑_j z^j • c_j`, which satisfies the Fourier relation
`Work.Idx.wRow_wPsi : ∑_k c_k * Ψ_{k+p} = if p = -1 then 1 else 0` (for `hQ`, i.e. `wQ` invertible
on the unit circle).

Claim: `wRow n D c * wProj n D c (wPsi X n D c) = 0`.

Proof: compute entries (`wRow_mul_wProj_apply`); the `(a,β)` entry of the projected block is
`∑_{j > i} (∑_k c_k * Ψ_{k+j-1-i}) * c_j`, and `∑_k c_k * Ψ_{k+j-1-i} = 0` by `wRow_wPsi` at
`p = j - 1 - i`, because `j > i` forces `j - 1 - i ≥ 0 ≠ -1` (`wRowB_mul_wProjB_zero`). -/
theorem wRow_mul_wProj_zero {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n D c z)) :
    wRow n D c * wProj n D c (wPsi X n D c) = 0 := by
  apply Matrix.ext
  intro a b
  obtain ⟨i, β⟩ := b
  simp only [Matrix.zero_apply]
  have hzero := wRowB_mul_wProjB_zero n D c (wPsi X n D c)
      (fun p hp => by rw [wRow_wPsi X n D c hQ p, if_neg hp]) i
  rw [wRow_mul_wProj_apply, hzero]
  simp

end

end Work.Idx
