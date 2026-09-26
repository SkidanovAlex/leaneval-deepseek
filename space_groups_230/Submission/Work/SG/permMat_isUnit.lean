import Mathlib
import Submission.Work.SG.SellingDefs

namespace Work.SG

open scoped Matrix

/-! ### Relabelling matrices of superbase permutations

`permMat σ` is the `3 × 3` matrix whose `j`-th column is the coordinate vector of the
relabelled superbase vector `v_{σ(j.succ)}` in the column basis.  The key observation is that
it acts on the four coordinate vectors `coordVec m` exactly by `σ`:

`(permMat σ).mulVec (coordVec m) = coordVec (σ m)`

(`coordVec m` is the coordinate vector of the `m`-th superbase vector in the column basis, see
`SellingDefs.mulVec_coordVec`).  This forces `permMat σ * permMat σ⁻¹ = 1`, so `permMat σ` is
unimodular. -/

/-- The coordinate vector of the `j.succ`-th superbase vector is the `j`-th standard basis
vector. -/
theorem coordVec_succ_eq_single (j : Fin 3) : coordVec j.succ = Pi.single j (1 : ℤ) := by
  funext k
  rw [coordVec_succ, Pi.single_apply]

/-- The four coordinate vectors of a superbase sum to zero (they are the coordinates of four
vectors summing to zero). -/
theorem sum_coordVec : ∑ m : Fin 4, coordVec m = (0 : Fin 3 → ℤ) := by decide

/-- Permuting the superbase only permutes the summands, so the three coordinate vectors
`coordVec (σ j.succ)` sum to `- coordVec (σ 0)`. -/
theorem sum_coordVec_perm (σ : Equiv.Perm (Fin 4)) :
    ∑ j : Fin 3, coordVec (σ j.succ) = - coordVec (σ 0) := by
  have h1 : ∑ m : Fin 4, coordVec (σ m) = ∑ m : Fin 4, coordVec m :=
    Equiv.sum_comp σ (fun m => coordVec m)
  rw [sum_coordVec] at h1
  have h2 : ∑ m : Fin 4, coordVec (σ m) = coordVec (σ 0) + ∑ j : Fin 3, coordVec (σ j.succ) :=
    Fin.sum_univ_succ (fun m => coordVec (σ m))
  rw [h2] at h1
  exact eq_neg_of_add_eq_zero_right h1

/-- `permMat σ` sends the coordinate vector of the `m`-th superbase vector to the coordinate
vector of the `σ m`-th one.  For `m = j.succ` this is column membership; for `m = 0` it follows
from `∑ m, coordVec m = 0` together with `sum_coordVec_perm`. -/
theorem permMat_mulVec_coordVec (σ : Equiv.Perm (Fin 4)) (m : Fin 4) :
    (permMat σ).mulVec (coordVec m) = coordVec (σ m) := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨j, rfl⟩
  · funext i
    have hσi : ∑ x : Fin 3, coordVec (σ x.succ) i = - coordVec (σ 0) i := by
      have h := congrFun (sum_coordVec_perm σ) i
      rwa [Finset.sum_apply] at h
    simp only [Matrix.mulVec, dotProduct, permMat, coordVec_zero]
    rw [show (∑ x : Fin 3, coordVec (σ x.succ) i * (-1))
        = - ∑ x : Fin 3, coordVec (σ x.succ) i by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)]
    rw [hσi, neg_neg]
  · rw [coordVec_succ_eq_single j, Matrix.mulVec_single_one]
    funext i
    rw [Matrix.col_apply]
    rfl

/-- `permMat` is multiplicative: `permMat σ` is `σ` acting in the superbase coordinates, so
`permMat σ * permMat σ⁻¹ = 1`. -/
theorem permMat_mul_inv (σ : Equiv.Perm (Fin 4)) : permMat σ * permMat σ⁻¹ = 1 := by
  have h : ∀ i : Fin 3, (permMat σ * permMat σ⁻¹).mulVec (Pi.single i (1:ℤ)) =
      (1 : IMat).mulVec (Pi.single i (1:ℤ)) := by
    intro i
    rw [← Matrix.mulVec_mulVec (Pi.single i (1:ℤ)) (permMat σ) (permMat σ⁻¹),
        ← coordVec_succ_eq_single i, permMat_mulVec_coordVec, permMat_mulVec_coordVec,
        Matrix.one_mulVec]
    exact congrArg coordVec (Equiv.apply_symm_apply σ i.succ)
  apply Matrix.ext
  intro i j
  have h2 := congrFun (h j) i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
  simpa [Matrix.col_apply] using h2

/-- The relabelling matrix `permMat σ` of a superbase permutation is unimodular.

Route: `(permMat σ).mulVec (coordVec m) = coordVec (σ m)` for all `m : Fin 4` (for `m = i.succ`
this is column membership, for `m = 0` use `∑ m, coordVec m = 0`).  Hence
`permMat σ * permMat σ⁻¹ = 1` (columns of `permMat σ⁻¹` are `coordVec (σ⁻¹ j.succ)`), so
`(permMat σ).det * (permMat σ⁻¹).det = 1`, hence `IsUnit (permMat σ).det` (`Int.isUnit_iff`).
A finite `decide`-style case split over `Equiv.Perm (Fin 4)` is also acceptable — but note
`native_decide` is forbidden, only kernel `decide`/`rfl`. -/
theorem permMat_isUnit (σ : Equiv.Perm (Fin 4)) : IsUnit (permMat σ).det := by
  have h1 : (permMat σ).det * (permMat σ⁻¹).det = 1 := by
    have h := congrArg Matrix.det (permMat_mul_inv σ)
    rwa [Matrix.det_mul, Matrix.det_one] at h
  have h2 : (permMat σ⁻¹).det * (permMat σ).det = 1 := by
    have h := permMat_mul_inv σ⁻¹
    rw [inv_inv] at h
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_one] at this
  rw [isUnit_iff_exists]
  exact ⟨(permMat σ⁻¹).det, h1, h2⟩

end Work.SG
