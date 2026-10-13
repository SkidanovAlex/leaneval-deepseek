/-
  annals_wilkies_conjecture, AREA E3, `Realify`: the realification of a non-singular complex
  matrix is non-singular.

  `reifyMat A` is the matrix of the `ℂ`-linear map `z ↦ A *ᵥ z` on `ℂ^k ≅ ℝ^{2k}` under the
  identification `z = u + i v ↦ (u, v)`; in block form it is `[[Re A, -Im A], [Im A, Re A]]`.
  A real vector `(u, v)` in the kernel of `reifyMat A` is the same thing as a complex vector
  `u + i v` in the kernel of `A`, so `reifyMat A` is non-singular as soon as `A` is.
  (In fact `det (reifyMat A) = |det A|²`, but only the non-vanishing is needed.)

  Used in `Work.WilE3.Realify.Jac`: it is what makes a nondegenerate complex zero of the
  complexified EA system realify to a nondegenerate zero of the realified (separable) system.
-/
import Mathlib
import Submission.Work.WilE3.Realify.Defs

set_option autoImplicit false

namespace Work.WilE3.Realify

open Matrix

/-! ## §1. The entries of the realification -/

theorem reifyDet_apply_ll {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    reifyMat A (Fin.castAdd k i) (Fin.castAdd k j) = (A i j).re := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_left]

theorem reifyDet_apply_lr {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    reifyMat A (Fin.castAdd k i) (Fin.natAdd k j) = -(A i j).im := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]

theorem reifyDet_apply_rl {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    reifyMat A (Fin.natAdd k i) (Fin.castAdd k j) = (A i j).im := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_right, Fin.addCases_left]

theorem reifyDet_apply_rr {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    reifyMat A (Fin.natAdd k i) (Fin.natAdd k j) = (A i j).re := by
  simp only [reifyMat, Matrix.of_apply, Fin.addCases_right]

/-! ## §2. The rows of the realification

The `i`-th row (`i : Fin k`) of `reifyMat A` applied to a real vector `v = (u, w)` is the real
part of the `i`-th entry of `A *ᵥ (u + i w)`, and the `(k + i)`-th row is its imaginary part. -/

theorem reifyDet_mulVec_castAdd {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (v : Fin (k + k) → ℝ)
    (i : Fin k) :
    ((reifyMat A) *ᵥ v) (Fin.castAdd k i) =
      (∑ j : Fin k, (A i j).re * v (Fin.castAdd k j)) -
        ∑ j : Fin k, (A i j).im * v (Fin.natAdd k j) := by
  change (∑ j : Fin (k + k), reifyMat A (Fin.castAdd k i) j * v j) =
    (∑ j : Fin k, (A i j).re * v (Fin.castAdd k j)) -
      ∑ j : Fin k, (A i j).im * v (Fin.natAdd k j)
  rw [Fin.sum_univ_add]
  simp only [reifyDet_apply_ll, reifyDet_apply_lr, neg_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg]

theorem reifyDet_mulVec_natAdd {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (v : Fin (k + k) → ℝ)
    (i : Fin k) :
    ((reifyMat A) *ᵥ v) (Fin.natAdd k i) =
      (∑ j : Fin k, (A i j).im * v (Fin.castAdd k j)) +
        ∑ j : Fin k, (A i j).re * v (Fin.natAdd k j) := by
  change (∑ j : Fin (k + k), reifyMat A (Fin.natAdd k i) j * v j) =
    (∑ j : Fin k, (A i j).im * v (Fin.castAdd k j)) +
      ∑ j : Fin k, (A i j).re * v (Fin.natAdd k j)
  rw [Fin.sum_univ_add]
  simp only [reifyDet_apply_rl, reifyDet_apply_rr]

/-! ## §3. The complexification step -/

/-- The coercion `ℝ → ℂ` commutes with finite sums. -/
theorem reifyDet_ofReal_sum {k : ℕ} (f : Fin k → ℝ) :
    ((∑ j, f j : ℝ) : ℂ) = ∑ j, (f j : ℂ) := by
  simpa using map_sum Complex.ofRealHom f Finset.univ

/-- **The key identity.** Reading a real vector `v : Fin (k + k) → ℝ`, whose first half is a real
vector `u` and whose second half is a real vector `w`, as the complex vector `u + i w : ℂ^k`:
the `i`-th entry of `A *ᵥ (u + i w)` is the `i`-th entry of `reifyMat A *ᵥ v` (which is the real
part), plus `i` times the `(k + i)`-th entry of `reifyMat A *ᵥ v` (which is the imaginary part). -/
theorem mulVec_reifyVec {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (v : Fin (k + k) → ℝ)
    (i : Fin k) :
    (A *ᵥ (fun a => (v (Fin.castAdd k a) : ℂ) + (v (Fin.natAdd k a) : ℂ) * Complex.I)) i =
      (((∑ j : Fin k,
          ((A i j).re * v (Fin.castAdd k j) - (A i j).im * v (Fin.natAdd k j)) : ℝ)) : ℂ) +
        (((∑ j : Fin k,
          ((A i j).im * v (Fin.castAdd k j) + (A i j).re * v (Fin.natAdd k j)) : ℝ)) : ℂ) *
          Complex.I := by
  change (∑ j : Fin k,
      A i j * ((v (Fin.castAdd k j) : ℂ) + (v (Fin.natAdd k j) : ℂ) * Complex.I)) =
    (((∑ j : Fin k,
        ((A i j).re * v (Fin.castAdd k j) - (A i j).im * v (Fin.natAdd k j)) : ℝ)) : ℂ) +
      (((∑ j : Fin k,
        ((A i j).im * v (Fin.castAdd k j) + (A i j).re * v (Fin.natAdd k j)) : ℝ)) : ℂ) *
        Complex.I
  have hterm : ∀ j : Fin k,
      A i j * ((v (Fin.castAdd k j) : ℂ) + (v (Fin.natAdd k j) : ℂ) * Complex.I) =
        (((A i j).re * v (Fin.castAdd k j) - (A i j).im * v (Fin.natAdd k j) : ℝ) : ℂ) +
          (((A i j).im * v (Fin.castAdd k j) + (A i j).re * v (Fin.natAdd k j) : ℝ) : ℂ) *
            Complex.I := by
    intro j
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  have hsum : (∑ j : Fin k,
      A i j * ((v (Fin.castAdd k j) : ℂ) + (v (Fin.natAdd k j) : ℂ) * Complex.I)) =
      ∑ j : Fin k,
        ((((A i j).re * v (Fin.castAdd k j) - (A i j).im * v (Fin.natAdd k j) : ℝ) : ℂ) +
          (((A i j).im * v (Fin.castAdd k j) + (A i j).re * v (Fin.natAdd k j) : ℝ) : ℂ) *
            Complex.I) :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [← reifyDet_ofReal_sum (fun j : Fin k =>
        (A i j).re * v (Fin.castAdd k j) - (A i j).im * v (Fin.natAdd k j)),
      ← reifyDet_ofReal_sum (fun j : Fin k =>
        (A i j).im * v (Fin.castAdd k j) + (A i j).re * v (Fin.natAdd k j))]

/-! ## §4. Non-singularity of the realification -/

theorem reifyMat_det_ne_zero {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : A.det ≠ 0) :
    (Work.WilE3.Realify.reifyMat A).det ≠ 0 := by
  intro hdet
  have hiff : (∃ w : Fin (k + k) → ℝ, w ≠ 0 ∧ (reifyMat A) *ᵥ w = 0) ↔
      (reifyMat A).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff
  obtain ⟨v, hvne, hv⟩ := hiff.mpr hdet
  -- the complex vector `u + i w` is a kernel vector of `A`
  have hmem : A *ᵥ (fun a => (v (Fin.castAdd k a) : ℂ) + (v (Fin.natAdd k a) : ℂ) * Complex.I) =
      0 := by
    funext i
    have h1 : (∑ j : Fin k,
        ((A i j).re * v (Fin.castAdd k j) - (A i j).im * v (Fin.natAdd k j))) = 0 := by
      rw [Finset.sum_sub_distrib]
      exact (reifyDet_mulVec_castAdd (A := A) (v := v) (i := i)).symm.trans
        (congrFun hv (Fin.castAdd k i))
    have h2 : (∑ j : Fin k,
        ((A i j).im * v (Fin.castAdd k j) + (A i j).re * v (Fin.natAdd k j))) = 0 := by
      rw [Finset.sum_add_distrib]
      exact (reifyDet_mulVec_natAdd (A := A) (v := v) (i := i)).symm.trans
        (congrFun hv (Fin.natAdd k i))
    rw [mulVec_reifyVec, h1, h2]
    simp
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hA hmem
  -- hence `u = 0` and `w = 0`
  apply hvne
  funext j
  refine Fin.addCases (motive := fun j : Fin (k + k) => v j = 0) (fun i => ?_) (fun i => ?_) j
  · have h := congrFun hz i
    have hre := congrArg Complex.re h
    simpa [Complex.mul_re, Complex.mul_im] using hre
  · have h := congrFun hz i
    have him := congrArg Complex.im h
    simpa [Complex.mul_re, Complex.mul_im] using him

end Work.WilE3.Realify
