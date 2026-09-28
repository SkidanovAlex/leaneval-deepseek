import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_span_gram
import Submission.Work.HP.numaux.det_le_prod_diag

/-!
# Hadamard's inequality for `detL` of a lattice spanned by an independent family

`Work.HP.detL L` is the covolume of an integral lattice `L ⊆ ℤ^ι`, i.e. the square root of the
determinant of the Gram matrix of a `ℤ`-basis of `L`.  Hadamard's determinant inequality says
that the covolume of the lattice spanned by `ℤ`-linearly independent vectors `b j` is at most the
product of the Euclidean norms of the `b j`:

`detL (span ℤ (range b)) ≤ ∏ j, ‖b j‖`.

The proof is the classical one.  By `Work.HP.Lat.detL_span_gram`, the left-hand side is
`√ det G` where `G i j = ∑ a, bᵢ(a) bⱼ(a)` is the Gram matrix of the vectors.  Writing
`G = B Bᵀ` for the coordinate matrix `B i a = b i a`, the matrix `G` is positive semidefinite,
and Hadamard's inequality for positive semidefinite matrices
(`Work.HP.numaux.det_le_prod_diag`) gives
`det G ≤ ∏ i, G i i = ∏ i, ∑ a, bᵢ(a)² = ∏ i, ‖bᵢ‖²`.
Taking square roots yields the claim.
-/

set_option autoImplicit false

open scoped Matrix

namespace Work.HP.numaux

/-- The Gram matrix `(i,j) ↦ ∑ a, f i a * f j a` of a finite family of real functions is
positive semidefinite: it is `B Bᵀ` for the coordinate matrix `B i a = f i a`. -/
lemma posSemidef_gram_of_fn {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin r → ι → ℝ) :
    (Matrix.of fun i j => ∑ a, f i a * f j a).PosSemidef := by
  have h : (Matrix.of fun i j => ∑ a, f i a * f j a) = (Matrix.of f) * (Matrix.of f)ᴴ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- **Hadamard's inequality for a Gram determinant**: the determinant of the Gram matrix of a
finite family of real vectors is at most the product of the squared norms of the vectors. -/
lemma det_gram_le_prod_sq {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin r → ι → ℝ) :
    Matrix.det (Matrix.of fun i j => ∑ a, f i a * f j a) ≤ ∏ i, ∑ a, (f i a) ^ 2 := by
  refine (det_le_prod_diag (posSemidef_gram_of_fn f)).trans (le_of_eq ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Hadamard's inequality for the covolume of a lattice spanned by an independent family.**
The determinant of the lattice `ℤb₁ + ⋯ + ℤb_r` is at most the product of the Euclidean norms of
the generators `b j`. -/
theorem detL_span_le_prod {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} {b : Fin r → (ι → ℤ)}
    (hb : LinearIndependent ℤ b) :
    detL (Submodule.span ℤ (Set.range b)) ≤ ∏ j : Fin r, eNorm (b j) := by
  classical
  -- Hadamard for the Gram determinant of the real vectors underlying `b`
  have h2 : Matrix.det (Matrix.of fun i j => ∑ a, (b i a : ℝ) * (b j a : ℝ))
      ≤ ∏ i, (eNorm (b i)) ^ 2 := by
    refine (det_gram_le_prod_sq (fun i a => (b i a : ℝ))).trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]
  -- `detL` of the span is the square root of that Gram determinant
  rw [Work.HP.Lat.detL_span_gram r b hb]
  refine Real.sqrt_le_iff.mpr ⟨Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _, ?_⟩
  rw [← Finset.prod_pow Finset.univ 2 (fun j => eNorm (b j))]
  exact h2

end Work.HP.numaux
