import Mathlib

/-!
# Determinant of the Gram matrix is unchanged by a unimodular change of lattice basis

Let `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι` be a real linear map and let
`b : Fin R → (Fin R → ℤ)` be such that `x ↦ ∑ j, x j • b j` is a bijection of
`ℤ^R`, i.e. the rows of `b` form a `ℤ`-basis of `ℤ^R`.  Then the Gram matrix of
the images under `Φ` of the standard basis and the Gram matrix of the images of
the rows of `b` have the same determinant.

The proof has two ingredients:

* `det_int_sq_eq_one` : a bijection of `ℤ^R` given by an integer matrix forces
  the determinant of that matrix to be a unit of `ℤ`, hence `±1`; consequently
  the determinant of the associated real matrix squares to `1`.
* `gram_mulVec` : replacing the vectors `v k` by `∑ k, B i k • v k` changes the
  Gram matrix by a congruence `G ↦ B * G * Bᵀ`.

Taking determinants in the second and using `(det B) ^ 2 = 1` from the first
gives the result.
-/

namespace Work.EEupper

/-- If the `ℤ`-linear map encoded by the integer matrix `(b i j)` is a bijection
of `ℤ^R`, then the determinant of the corresponding real matrix is `±1`; in
particular its square is `1`. -/
theorem det_int_sq_eq_one {R : ℕ} (b : Fin R → (Fin R → ℤ))
    (hb : Function.Bijective (fun x : Fin R → ℤ => ∑ j, x j • b j)) :
    (Matrix.det (Matrix.of (fun i j : Fin R => (b i j : ℝ)))) ^ 2 = 1 := by
  -- The transpose `C` of `(b i j)` describes `x ↦ ∑ j, x j • b j` as a matrix
  -- acting on column vectors, and `hb.2` produces a right inverse for it.
  set C : Matrix (Fin R) (Fin R) ℤ := Matrix.of (fun i j => b j i) with hC
  choose u hu using fun k : Fin R => hb.2 (Pi.basisFun ℤ (Fin R) k)
  let D : Matrix (Fin R) (Fin R) ℤ := Matrix.of (fun j k => u k j)
  have hCD : C * D = 1 := by
    ext i k
    have hsum : (C * D) i k = (∑ j, u k j • b j) i := by
      rw [Matrix.mul_apply]
      simp [C, D, Matrix.of_apply, Finset.sum_apply, mul_comm]
    have hK : (∑ j, u k j • b j) = (Pi.basisFun ℤ (Fin R)) k := hu k
    rw [hsum, hK]
    rw [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply]
  have h1 : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCD
  have h2 : IsUnit (Matrix.det (Matrix.of (fun i j : Fin R => b i j) : Matrix (Fin R) (Fin R) ℤ)) := by
    rw [← Matrix.det_transpose (Matrix.of (fun i j : Fin R => b i j) : Matrix (Fin R) (Fin R) ℤ)]
    exact h1
  have h4 : (Matrix.det (Matrix.of (fun i j : Fin R => b i j) : Matrix (Fin R) (Fin R) ℤ)) ^ 2 = 1 :=
    Int.isUnit_sq h2
  have hcast : (Matrix.det (Matrix.of (fun i j : Fin R => (b i j : ℝ))))
      = ((Matrix.det (Matrix.of (fun i j : Fin R => b i j) : Matrix (Fin R) (Fin R) ℤ) : ℤ) : ℝ) := by
    rw [Int.cast_det]
    rfl
  rw [hcast, ← Int.cast_pow, h4, Int.cast_one]

/-- Congruence formula for Gram matrices under a change of generating family. -/
theorem gram_mulVec {R : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix (Fin R) (Fin R) ℝ) (v : Fin R → EuclideanSpace ℝ ι) :
    Matrix.gram ℝ (fun i => ∑ k, B i k • v k)
      = B * Matrix.gram ℝ v * Matrix.transpose B := by
  ext i j
  rw [Matrix.gram_apply]
  rw [← Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) (v := v) (x := fun k => B i k)
    (y := fun k => B j k)]
  have hstar : star (fun k : Fin R => B i k) = (fun k => B i k) := by
    funext k; simp
  rw [hstar]
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, mul_assoc]

set_option maxHeartbeats 1000000 in
theorem det_gram_unimodular {R : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι) (b : Fin R → (Fin R → ℤ))
    (hb : Function.Bijective (fun x : Fin R → ℤ => ∑ j, x j • b j)) :
    (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det
      = (Matrix.gram ℝ (fun i : Fin R => Φ (fun k => (b i k : ℝ)))).det := by
  have hBdet : (Matrix.det (Matrix.of (fun i j : Fin R => (b i j : ℝ)))) ^ 2 = 1 :=
    det_int_sq_eq_one b hb
  set B : Matrix (Fin R) (Fin R) ℝ := Matrix.of (fun i j => (b i j : ℝ)) with hBs
  set v : Fin R → EuclideanSpace ℝ ι := fun i => Φ (Pi.basisFun ℝ (Fin R) i) with hvs
  -- the vectors `fun k => (b i k : ℝ)` are the vectors `∑ k, B i k • v k`
  have hΦ : ∀ i, Φ (fun k => (b i k : ℝ)) = ∑ k, B i k • v k := by
    intro i
    have h1 : (fun k => (b i k : ℝ))
        = ∑ k, (b i k : ℝ) • (Pi.basisFun ℝ (Fin R) k) := by
      simpa using ((Pi.basisFun ℝ (Fin R)).sum_repr (fun k => (b i k : ℝ))).symm
    rw [h1, map_sum]
    simp only [map_smul, hvs, hBs, Matrix.of_apply]
  have hw : (fun i : Fin R => Φ (fun k => (b i k : ℝ))) = fun i => ∑ k, B i k • v k :=
    funext hΦ
  rw [hw, gram_mulVec B v]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hsq : (Matrix.det B) ^ 2 = 1 := by simpa [hBs] using hBdet
  have key : B.det * (Matrix.gram ℝ v).det * B.det = (Matrix.gram ℝ v).det := by
    calc B.det * (Matrix.gram ℝ v).det * B.det
        = (Matrix.det B) ^ 2 * (Matrix.gram ℝ v).det := by ring
      _ = (Matrix.gram ℝ v).det := by rw [hsq, one_mul]
  rw [key]

end Work.EEupper
