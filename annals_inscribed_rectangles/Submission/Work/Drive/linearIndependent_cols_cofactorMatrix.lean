import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-!
# The columns of `cofactorMatrix T` are linearly independent when `T` is surjective

Let `T : ℝ^{m+1} → ℝ^m` be a surjective linear map.  Its matrix in the standard bases has
entries `M i j = (T e_j).ofLp i` (`i : Fin m`, `j : Fin (m+1)`); the `j`-th standard basis vector
is `EuclideanSpace.single j 1`.  The `i`-th row of `M` is the coordinate vector of the linear
functional `y ↦ (y.ofLp i)` composed with `T`, and `cofactorMatrix T` is `Mᵀ`, so its columns are
the rows of `M`.

Surjectivity of `T` says that these `m` functionals (which form a basis of the dual of `ℝ^m`)
pull back to linearly independent elements of the dual of `ℝ^{m+1}`; reading those off in the
standard basis gives exactly the rows of `M`.  Concretely we prove `M.vecMul` is injective: if
`M.vecMul z = 0` then the functional `Z w = ∑ i, z i * w.ofLp i` vanishes on `T e_j` for every
`j`, hence `Z ∘ T = 0`, hence `Z = 0` because `T` is onto, hence `z = 0`.
-/

namespace Work.Drive

theorem linearIndependent_cols_cofactorMatrix {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m)
    (hT : Function.Surjective T) :
    LinearIndependent ℝ (Work.Drive.cofactorMatrix T).col := by
  classical
  -- The matrix of `T` in the standard bases (rows indexed by the target coordinates).
  let M : Matrix (Fin m) (Fin (m + 1)) ℝ := fun i j => (T (EuclideanSpace.single j 1)).ofLp i
  have hA : cofactorMatrix T = M.transpose := by
    ext j i
    rfl
  rw [hA, Matrix.col_transpose, ← Matrix.vecMul_injective_iff]
  intro x y hxy
  -- Injectivity of `M.vecMul` via the "dot product with `z`" functional.
  have hinj : Function.Injective M.vecMulLinear := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    -- `hz` says that for each `j` the pairing of `z` with `T e_j` vanishes.
    have hz' : ∀ j, ∑ i, z i * M i j = 0 := by
      intro j
      have := congrFun hz j
      simpa [Matrix.vecMulLinear_apply, Matrix.vecMul_apply, dotProduct, Matrix.col_apply] using this
    -- The functional `Z w = ∑ i, z i * w.ofLp i`.
    let φ : (Fin m → ℝ) →ₗ[ℝ] ℝ := ∑ i : Fin m, z i • (LinearMap.proj i : (Fin m → ℝ) →ₗ[ℝ] ℝ)
    let Z : Tgt m →ₗ[ℝ] ℝ := φ.comp (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap
    have hZapply : ∀ w : Tgt m, Z w = ∑ i, z i * w.ofLp i := by
      intro w
      simp [φ, Z, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
    -- `Z` vanishes on the images of the standard basis, hence `Z ∘ T = 0`.
    have hZT : Z.comp T.toLinearMap = 0 := by
      apply Module.Basis.ext (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
      intro j
      rw [LinearMap.comp_apply, LinearMap.zero_apply, hZapply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
      exact hz' j
    -- Surjectivity of `T` forces `Z = 0`.
    have hZ : Z = 0 := by
      ext w
      obtain ⟨v, rfl⟩ := hT w
      have h2 := LinearMap.congr_fun hZT v
      simpa using h2
    -- And then `z = 0` by testing `Z` against the standard basis of the target.
    funext i
    have hzi : z i = Z (EuclideanSpace.single i 1) := by
      rw [hZapply, Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hzi, hZ]
    rfl
  exact hinj (by simpa [Matrix.coe_vecMulLinear] using hxy)

end Work.Drive
