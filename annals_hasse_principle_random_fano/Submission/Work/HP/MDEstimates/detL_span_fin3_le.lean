import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_span_gram
import Submission.Work.HP.numaux.det_le_prod_diag

/-!
# Hadamard's inequality for the covolume of the lattice spanned by three independent vectors

`Work.HP.detL L` is the covolume of the integral lattice `L ⊆ ℤ^ι`, i.e. the square root of the
determinant of the Gram matrix of a `ℤ`-basis of `L`.  For the rank-`3` lattice spanned by a
`ℤ`-linearly independent family `v 0, v 1, v 2`, Hadamard's determinant inequality gives

`detL (ℤ v 0 + ℤ v 1 + ℤ v 2) ≤ ‖v 0‖ ‖v 1‖ ‖v 2‖`.

The proof is the classical one.  By `Work.HP.Lat.detL_span_gram` the left-hand side is `√det G`,
where `G i j = ∑ a, vᵢ(a) vⱼ(a)` is the Gram matrix of the three vectors.  Writing `G = B Bᵀ` for
the coordinate matrix `B i a = vᵢ(a)`, the matrix `G` is positive semidefinite, so Hadamard's
inequality for positive semidefinite matrices (`Work.HP.numaux.det_le_prod_diag`) gives
`det G ≤ ∏ i, G i i = ∏ i, ∑ a, vᵢ(a)² = ∏ i, ‖vᵢ‖²`, and taking square roots yields the claim.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

/-- The Gram matrix `(i,j) ↦ ∑ a, f i a * f j a` of a finite family of real functions is positive
semidefinite: it is `B Bᵀ` for the coordinate matrix `B i a = f i a`. -/
private lemma gram_posSemidef {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin r → ι → ℝ) :
    (Matrix.of fun i j => ∑ a, f i a * f j a).PosSemidef := by
  let B : Matrix (Fin r) ι ℝ := Matrix.of f
  have h : (Matrix.of fun i j => ∑ a, f i a * f j a) = B * B.conjTranspose := by
    ext i j
    simp only [B, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- **Hadamard's inequality for a Gram determinant**: the determinant of the Gram matrix of a
finite family of real vectors is at most the product of the squared norms of the vectors. -/
private lemma det_gram_le_prod_sq {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin r → ι → ℝ) :
    Matrix.det (Matrix.of fun i j => ∑ a, f i a * f j a) ≤ ∏ i, ∑ a, (f i a) ^ 2 := by
  refine (Work.HP.numaux.det_le_prod_diag (gram_posSemidef f)).trans (le_of_eq ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Hadamard's inequality in rank three.**  The covolume of the lattice spanned by three
`ℤ`-linearly independent integer vectors is at most the product of their Euclidean norms. -/
theorem detL_span_fin3_le {ι : Type*} [Fintype ι] (v : Fin 3 → (ι → ℤ))
    (hv : LinearIndependent ℤ v) :
    Work.HP.detL (Submodule.span ℤ (Set.range v)) ≤
      Work.HP.eNorm (v 0) * Work.HP.eNorm (v 1) * Work.HP.eNorm (v 2) := by
  classical
  -- Hadamard for the Gram determinant of the real vectors underlying `v`
  have h2 : (Matrix.of fun i j : Fin 3 => ∑ a, (v i a : ℝ) * (v j a : ℝ)).det
      ≤ ∏ i : Fin 3, (Work.HP.eNorm (v i)) ^ 2 := by
    refine (det_gram_le_prod_sq (fun i a => (v i a : ℝ))).trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Work.HP.eNorm, Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]
  -- the covolume of the span is the square root of that Gram determinant
  rw [Work.HP.Lat.detL_span_gram 3 v hv, ← Fin.prod_univ_three (fun i => Work.HP.eNorm (v i))]
  refine Real.sqrt_le_iff.mpr ⟨Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _, ?_⟩
  rw [← Finset.prod_pow Finset.univ 2 (fun j => Work.HP.eNorm (v j))]
  exact h2

end Work.HP.MDEstimates
