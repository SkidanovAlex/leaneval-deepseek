import Mathlib
import Submission.Work.HP.Sig2.LatStepDefs

namespace Work.HP.Sig2

open Matrix

/-- The Gram matrix of a family obtained from another one by a matrix of scalars:
if `wᵢ = ∑ⱼ Cᵢⱼ • vⱼ` then `gram w = C * gram v * Cᵀ`. -/
lemma gram_sum_smul {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : Type*} [Fintype n] (C : Matrix n n ℝ) (v : n → E) :
    Matrix.gram ℝ (fun i => ∑ j, C i j • v j) = C * Matrix.gram ℝ v * Cᵀ := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro x1 _
  rw [starRingEnd_apply]
  simp only [star_trivial]
  ring

/-- If `b` is a `ℤ`-basis of `ℤ^R` (i.e. the map `x ↦ ∑ j, x j • b j` is bijective), then the
Gram determinant of the images under a linear map `Φ` of the standard basis of `ℝ^R` and of the
realified vectors `b i` agree.  Indeed the matrix of `b` is unimodular, so the two families are
related by a change of basis of determinant `±1`, which changes the Gram determinant by `1`. -/
theorem det_gram_of_int_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (b : Fin R → (Fin R → ℤ))
    (hb : Function.Bijective (fun x : Fin R → ℤ => ∑ j, x j • b j))
    (Φ : Work.HP.LatMap (ι := ι) R) :
    (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det
      = (Matrix.gram ℝ (fun i : Fin R => Φ (fun k => (b i k : ℝ)))).det := by
  -- `Matrix.vecMul · (Matrix.of b)` is the map `x ↦ ∑ j, x j • b j`.
  have vecMul_of : ∀ x : Fin R → ℤ, Matrix.vecMul x (Matrix.of b) = ∑ j, x j • b j := by
    intro x; funext k
    simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply]
  have hsurj : Function.Surjective (fun x : Fin R → ℤ => Matrix.vecMul x (Matrix.of b)) := by
    intro y
    obtain ⟨x, hx⟩ := hb.surjective y
    exact ⟨x, (vecMul_of x).trans hx⟩
  -- The integer matrix of `b` is invertible, hence its determinant is `±1`.
  have hunit : IsUnit ((Matrix.of b).det) :=
    (Matrix.isUnit_iff_isUnit_det (Matrix.of b)).mp
      (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)
  have hdet2 : (((Matrix.of b).det : ℤ) : ℝ) * (((Matrix.of b).det : ℤ) : ℝ) = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
  -- `BR` is the realification of the matrix of `b`, and it has determinant `±1`.
  set BR : Matrix (Fin R) (Fin R) ℝ := (Matrix.of b).map (fun z : ℤ => (z : ℝ)) with hBR
  have hBRdet : BR.det = (((Matrix.of b).det : ℤ) : ℝ) := by
    have h := RingHom.map_det (Int.castRingHom ℝ) (Matrix.of b)
    rw [RingHom.mapMatrix_apply] at h
    exact h.symm
  have hBRsquare : BR.det * BR.det = 1 := by rw [hBRdet]; exact hdet2
  -- The two families are related by `BR`.
  have hfam : (fun i : Fin R => Φ (fun k => (b i k : ℝ)))
      = (fun i : Fin R => ∑ j, BR i j • Φ (Pi.basisFun ℝ (Fin R) j)) := by
    funext i
    rw [show (∑ j, BR i j • Φ (Pi.basisFun ℝ (Fin R) j))
        = Φ (∑ j, BR i j • Pi.basisFun ℝ (Fin R) j) from by
      rw [map_sum]; simp [map_smul]]
    congr 1
    rw [hBR]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply, Matrix.map_apply,
      Matrix.of_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne (Ne.symm hx)]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hgram : Matrix.gram ℝ (fun i : Fin R => Φ (fun k => (b i k : ℝ)))
      = BR * Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i)) * BRᵀ := by
    rw [hfam]
    exact gram_sum_smul BR (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hfin : BR.det * (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det * BR.det
      = (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det := by
    calc BR.det * (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det * BR.det
        = (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det * (BR.det * BR.det) := by
          ring
      _ = (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det * 1 := by rw [hBRsquare]
      _ = (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det := by ring
  exact hfin.symm

end Work.HP.Sig2
