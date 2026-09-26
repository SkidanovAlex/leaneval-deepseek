import Mathlib
import Submission.Work.SG.SellingDefs

namespace Work.SG

open scoped Matrix

/-- The four coordinate vectors of the superbase sum to zero. -/
private theorem coordVec_sum : (∑ n : Fin 4, coordVec n) = (0 : IVec) := by
  rw [Fin.sum_univ_succ]
  funext k
  simp only [Pi.add_apply, Pi.zero_apply, coordVec_zero, Finset.sum_apply]
  have hsucc : (∑ i : Fin 3, coordVec i.succ k) =
      ∑ i : Fin 3, (if k = i then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [coordVec_succ]
  rw [hsucc, Finset.sum_ite_eq]
  simp

/-- The relabelling matrix `permMat σ` sends the coordinate vector of `m` to the coordinate
vector of `σ m`. -/
private theorem permMat_mulVec_coordVec (σ : Equiv.Perm (Fin 4)) (m : Fin 4) :
    (permMat σ).mulVec (coordVec m) = coordVec (σ m) := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
  · -- `m = 0`: sum the `i`-th columns, which are `coordVec (σ i.succ)`, using that
    -- `∑ n, coordVec n = 0` and `σ` is a bijection.
    funext k
    simp only [permMat, Matrix.mulVec, dotProduct, coordVec_zero]
    simp only [mul_neg, mul_one, Finset.sum_neg_distrib]
    have hsplit : (∑ j : Fin 3, coordVec (σ j.succ) k) = - coordVec (σ 0) k := by
      have h1 : (∑ j : Fin 4, coordVec j k) =
          coordVec (σ 0) k + ∑ j : Fin 3, coordVec (σ j.succ) k := by
        rw [← Equiv.sum_comp σ (fun n => coordVec n k), Fin.sum_univ_succ]
      have h2 : (∑ j : Fin 4, coordVec j k) = 0 := by
        have := congrFun coordVec_sum k
        simpa using this
      linarith
    rw [hsplit]
    ring
  · -- `m = i.succ`: the corresponding entry of `permMat σ` is the `i`-th column.
    funext k
    simp only [permMat, Matrix.mulVec, dotProduct, coordVec_succ]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro b _ hb; simp [hb]

/-- Relabelling the superbase by `σ` is multiplication of the basis matrix by `permMat σ` on
the right.

Route: `sb (W * permMat σ) m = (W * permMat σ).mulVec (coordVec m)` (`mulVec_coordVec`) `=
W.mulVec ((permMat σ).mulVec (coordVec m))` (`Matrix.mulVec_mulVec`), and
`(permMat σ).mulVec (coordVec m) = coordVec (σ m)`: for `m = i.succ` it is the `i`-th column of
`permMat σ`; for `m = 0` it is `-∑_{i:Fin 3} coordVec (σ i.succ) = coordVec (σ 0)` because
`∑ m, coordVec m = 0` and `σ` is a bijection. -/
theorem sb_permMat (W : IMat) (σ : Equiv.Perm (Fin 4)) (m : Fin 4) :
    sb (W * permMat σ) m = sb W (σ m) := by
  rw [← mulVec_coordVec (W * permMat σ) m, ← mulVec_coordVec W (σ m)]
  rw [← Matrix.mulVec_mulVec]
  rw [permMat_mulVec_coordVec σ m]

end Work.SG
