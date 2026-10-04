import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace Work.Diff.STE.B3

/-- For a symmetric real matrix `A` whose quadratic form is sandwiched between `c` and `K` times the
Euclidean square norm, the determinant is sandwiched between `c ^ n` and `K ^ n` (product of the
eigenvalues, each of which lies in `[c, K]`). -/
lemma det_bounds_of_quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ a b, A a b = A b a) {c K : ℝ} (hc : 0 ≤ c)
    (hl : ∀ ξ : Fin n → ℝ, c * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, A a b * ξ a * ξ b)
    (hu : ∀ ξ : Fin n → ℝ, ∑ a, ∑ b, A a b * ξ a * ξ b ≤ K * ∑ i, (ξ i) ^ 2) :
    c ^ n ≤ A.det ∧ A.det ≤ K ^ n := by
  classical
  have hH : A.IsHermitian := Matrix.IsHermitian.ext (fun i j => by
    rw [star_trivial]; exact hsym j i)
  have hdet : A.det = ∏ i, hH.eigenvalues i := by
    simpa using hH.det_eq_prod_eigenvalues (𝕜 := ℝ)
  -- the eigenvectors of a Hermitian matrix are unit vectors
  have hnorm : ∀ i : Fin n, ∑ j, ((hH.eigenvectorBasis i).ofLp j) ^ 2 = 1 := by
    intro i
    have hinner : inner ℝ (hH.eigenvectorBasis i) (hH.eigenvectorBasis i) = 1 := by
      have h := (orthonormal_iff_ite.mp (hH.eigenvectorBasis).orthonormal) i i
      simpa using h
    have h2 := EuclideanSpace.inner_eq_star_dotProduct (hH.eigenvectorBasis i)
      (hH.eigenvectorBasis i)
    rw [hinner] at h2
    rw [h2]
    simp only [dotProduct, Pi.star_def, star_trivial]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- the quadratic form on an eigenvector is the eigenvalue
  have hev : ∀ i : Fin n, hH.eigenvalues i
      = ∑ a, ∑ b, A a b * ((hH.eigenvectorBasis i).ofLp a) * ((hH.eigenvectorBasis i).ofLp b) := by
    intro i
    have heq := hH.eigenvalues_eq i
    have hstar : star ((hH.eigenvectorBasis i).ofLp) = (hH.eigenvectorBasis i).ofLp := by
      funext j; rw [Pi.star_apply, star_trivial]
    rw [heq, hstar, RCLike.re_to_real]
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- the eigenvalue sandwich
  have hlev : ∀ i : Fin n, c ≤ hH.eigenvalues i := by
    intro i
    have h := hl ((hH.eigenvectorBasis i).ofLp)
    rw [hnorm i, mul_one, ← hev i] at h
    exact h
  have hhev : ∀ i : Fin n, hH.eigenvalues i ≤ K := by
    intro i
    have h := hu ((hH.eigenvectorBasis i).ofLp)
    rw [hnorm i, mul_one, ← hev i] at h
    exact h
  have hprod : ∀ x : ℝ, (∏ _i : Fin n, x) = x ^ n := by
    intro x
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  constructor
  · rw [hdet, ← hprod c]
    exact Finset.prod_le_prod₀ (fun i _ => hc) (fun i _ => hlev i)
  · rw [hdet, ← hprod K]
    exact Finset.prod_le_prod₀ (fun i _ => le_trans hc (hlev i)) (fun i _ => hhev i)

end Work.Diff.STE.B3
