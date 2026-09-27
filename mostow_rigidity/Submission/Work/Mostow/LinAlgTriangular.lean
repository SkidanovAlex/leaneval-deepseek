import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.psdHadamard
import Submission.Work.Mostow.normDet_adjoint

/-!
# A triangular (determinant) linear-algebra inequality

Let `E` be a finite dimensional real inner product space of dimension `n`, let `L H : E →ₗ[ℝ] E`
with `H` self-adjoint and positive semidefinite, and let `c ≥ 0`.  If

`⟪L v, w⟫ ≤ c * √⟪H w, w⟫ * ‖v‖`   for all `v w`,

then

`|det L| ≤ c ^ n * √(det H)`.

This is the linear-algebraic input to the algebraic form of Mostow rigidity (an `L` whose
"`H`-norm" is bounded by `c` has determinant bounded by `c ^ n √(det H)`), cf. G. Prasad,
*Strong rigidity of ℚ-rank 1 lattices*, Invent. Math. 21 (1973).

## Proof outline

Taking `v = L^* w` (the Hilbert adjoint) turns the hypothesis into the pointwise bound
`‖L^* w‖ ≤ c √⟪H w, w⟫`.  In an orthonormal basis of `E` consisting of eigenvectors of `H`
(with eigenvalues `λ i ≥ 0`), the square of the norm determinant of `L^*` is the determinant of
the Gram matrix `G i j = ⟪L^* (b i), L^* (b j)⟫`; its diagonal entries satisfy
`G i i = ‖L^* (b i)‖ ^ 2 ≤ c ^ 2 * λ i`.  Hadamard's inequality for positive semidefinite matrices
(`Matrix.PosSemidef.det ≤ ∏ diagonal`) then gives
`(det L) ^ 2 = (det L^*) ^ 2 = det G ≤ ∏ i, c ^ 2 * λ i = c ^ (2n) * det H`,
and taking square roots finishes.
-/

namespace Work.Mostow

theorem LinAlgTriangular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = n) (L H : E →ₗ[ℝ] E)
    (hHsym : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y)) (hHpos : ∀ x, 0 ≤ inner ℝ (H x) x)
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v w : E, inner ℝ (L v) w ≤ c * Real.sqrt (inner ℝ (H w) w) * ‖v‖) :
    |L.det| ≤ c ^ n * Real.sqrt H.det := by
  have hsym : H.IsSymmetric := hHsym
  -- The determinant bound for a map bounded by `c √⟪H ·, ·⟫`.
  have hmain : ∀ (f : E →ₗ[ℝ] E), (∀ w, ‖f w‖ ≤ c * Real.sqrt (inner ℝ (H w) w)) →
      f.normDet ≤ c ^ n * Real.sqrt H.det := by
    intro f hf
    have hsq : f.normDet ^ 2
        = (Matrix.gram ℝ (fun i => f ((hsym.eigenvectorBasis hn) i))).det := by
      simpa using f.normDet_sq_eq_det_gram (hsym.eigenvectorBasis hn)
    have hGpsd : (Matrix.gram ℝ (fun i => f ((hsym.eigenvectorBasis hn) i))).PosSemidef :=
      Matrix.posSemidef_gram ℝ _
    have hhad := psdHadamard _ hGpsd
    -- the eigenvalues of `H` are nonnegative
    have hlam : ∀ i, 0 ≤ hsym.eigenvalues hn i := by
      intro i
      have h1 := hHpos ((hsym.eigenvectorBasis hn) i)
      rwa [hsym.apply_eigenvectorBasis hn i, real_inner_smul_left,
        (hsym.eigenvectorBasis hn).inner_eq_ite i i, ite_eq_left rfl, mul_one] at h1
    -- diagonal entries of the Gram matrix are bounded by `c ^ 2 * λ i`
    have hdiag : ∀ i, (Matrix.gram ℝ (fun i => f ((hsym.eigenvectorBasis hn) i))) i i
        ≤ c ^ 2 * hsym.eigenvalues hn i := by
      intro i
      rw [Matrix.gram_apply, real_inner_self_eq_norm_sq]
      have h1 : ‖f ((hsym.eigenvectorBasis hn) i)‖
          ≤ c * Real.sqrt (inner ℝ (H ((hsym.eigenvectorBasis hn) i))
              ((hsym.eigenvectorBasis hn) i)) := hf _
      have h2 : inner ℝ (H ((hsym.eigenvectorBasis hn) i)) ((hsym.eigenvectorBasis hn) i)
          = hsym.eigenvalues hn i := by
        rw [hsym.apply_eigenvectorBasis hn i, real_inner_smul_left,
          (hsym.eigenvectorBasis hn).inner_eq_ite i i, ite_eq_left rfl, mul_one]
        simp
      rw [h2] at h1
      calc ‖f ((hsym.eigenvectorBasis hn) i)‖ ^ 2
          ≤ (c * Real.sqrt (hsym.eigenvalues hn i)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = c ^ 2 * hsym.eigenvalues hn i := by
            rw [mul_pow, Real.sq_sqrt (hlam i)]
    -- Hadamard plus the diagonal bound
    have hprod : (Matrix.gram ℝ (fun i => f ((hsym.eigenvectorBasis hn) i))).det
        ≤ ∏ i, c ^ 2 * hsym.eigenvalues hn i := by
      refine le_trans hhad (Finset.prod_le_prod₀ ?_ ?_)
      · intro i _
        rw [Matrix.gram_apply, real_inner_self_eq_norm_sq]; positivity
      · intro i _
        exact hdiag i
    have hdetprod : (∏ i, hsym.eigenvalues hn i) = H.det := by
      simpa using (hsym.det_eq_prod_eigenvalues hn).symm
    have hdet : (∏ i, c ^ 2 * hsym.eigenvalues hn i) = c ^ (2 * n) * H.det := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdetprod,
        ← pow_mul]
    have hdetnn : 0 ≤ H.det := by
      rw [← hdetprod]
      exact Finset.prod_nonneg (fun i _ => hlam i)
    have hfinal : f.normDet ^ 2 ≤ (c ^ n * Real.sqrt H.det) ^ 2 := by
      calc f.normDet ^ 2
          = (Matrix.gram ℝ (fun i => f ((hsym.eigenvectorBasis hn) i))).det := hsq
        _ ≤ ∏ i, c ^ 2 * hsym.eigenvalues hn i := hprod
        _ = c ^ (2 * n) * H.det := hdet
        _ = (c ^ n * Real.sqrt H.det) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hdetnn, ← pow_mul, Nat.mul_comm 2 n]
    exact le_of_sq_le_sq hfinal (mul_nonneg (pow_nonneg hc n) (Real.sqrt_nonneg _))
  -- The hypothesis bounds the adjoint pointwise.
  have hbnd : ∀ w, ‖LinearMap.adjoint L w‖ ≤ c * Real.sqrt (inner ℝ (H w) w) := by
    intro w
    have key : ‖LinearMap.adjoint L w‖ ^ 2
        ≤ c * Real.sqrt (inner ℝ (H w) w) * ‖LinearMap.adjoint L w‖ := by
      have h0 := h (LinearMap.adjoint L w) w
      rw [← LinearMap.adjoint_inner_right L (LinearMap.adjoint L w) w,
        real_inner_self_eq_norm_sq] at h0
      exact h0
    rcases eq_or_lt_of_le (norm_nonneg (LinearMap.adjoint L w)) with hz | hz
    · rw [← hz]; exact mul_nonneg hc (Real.sqrt_nonneg _)
    · have h2 : ‖LinearMap.adjoint L w‖ * ‖LinearMap.adjoint L w‖
          ≤ (c * Real.sqrt (inner ℝ (H w) w)) * ‖LinearMap.adjoint L w‖ := by
        simpa [pow_two] using key
      exact le_of_mul_le_mul_right h2 hz
  have h1 := hmain (LinearMap.adjoint L) hbnd
  rwa [normDet_adjoint L, LinearMap.normDet_eq_abs_det L] at h1

end Work.Mostow
