import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.tangentField_exists
import Submission.Work.WilE2.RegSol
import Submission.Work.WilE2.linearIndependent_tangGrad

set_option autoImplicit false

namespace Work.WilE2

/-!
# Closedness of the set of non-submersion (critical) values of the lifted system

`KhoSubmersion S F y` says that every point `z` of the level set `{liftSystem S F = y}` is a
point where the `n` derivative functionals `∂_a (liftSystem S F)` are linearly independent
(equivalently: `y` is a regular value of the rectangular map `liftSystem S F : ℝⁿ⁺¹ → ℝⁿ`).

Hence

  `{y | ¬ KhoSubmersion S F y} = (liftSystem S F) '' {z | ¬ LinIndep (∂_a(liftSystem S F) z)}`

is the image of the *critical set*.  The critical set is the zero set of the generalised
cross-product field `crossField V` of the `n` gradients of the components of `V = liftSystem S F`
(these `n` vectors in `ℝⁿ⁺¹` are dependent exactly when their cross product vanishes), and it is
therefore closed as soon as the cross product field is continuous.  Properness of the lifted map
turns this into closedness of its image.

The two linear-algebra facts used are proved here:

* `linearIndependent_tangGrad_iff_crossField_ne_zero`: the gradients of the components of `V` at
  `z` are linearly independent iff the generalised cross product `crossField V z` does not vanish;
* `linearIndependent_fderiv_iff_tangGrad`: the derivative functionals `∂_a V(z)` are linearly
  independent iff the corresponding gradient vectors are.
-/

/-- Reverse direction of `linearIndependent_tangGrad`: if the gradient vectors of the components
of `V` at `z` are linearly independent, then so are the derivative functionals.  Both families
are the images of one another under the injective linear map sending a continuous linear
functional to the vector of its values on the standard basis. -/
theorem linearIndependent_fderiv_of_tangGrad {m : ℕ}
    (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ)
    (h : LinearIndependent ℝ (tangGrad V z)) :
    LinearIndependent ℝ (fun a => fderiv ℝ (fun w => V w a) z) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  apply h g
  funext i
  have h2 := congrArg (fun L : (Fin (m + 1) → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) hg
  simpa [tangGrad] using h2

/-- The derivative functionals `∂_a V(z)` of the components of `V` at `z` are linearly
independent if and only if the corresponding gradient vectors `i ↦ ∂_a V(z)(e_i)` are. -/
theorem linearIndependent_fderiv_iff_tangGrad {m : ℕ}
    (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ) :
    LinearIndependent ℝ (fun a => fderiv ℝ (fun w => V w a) z) ↔
      LinearIndependent ℝ (tangGrad V z) :=
  ⟨fun h => linearIndependent_tangGrad V z h, fun h => linearIndependent_fderiv_of_tangGrad V z h⟩

/-- If the generalised cross product of the gradients of the components of `V` is nonzero at `z`,
then those gradients are linearly independent: `crossField V z k ≠ 0` exhibits the `k`-th
`(m+1) × (m+1)` minor of the Jacobian as the determinant of an invertible matrix, so the `m`
gradients are the first `m` columns of an invertible matrix. -/
theorem linearIndependent_tangGrad_of_crossField_ne_zero {m : ℕ}
    (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ)
    (h : crossField V z ≠ 0) :
    LinearIndependent ℝ (tangGrad V z) := by
  obtain ⟨k, hk⟩ : ∃ k, crossField V z k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  have hdet : (tangMatrix V z (Pi.single k (1 : ℝ))).det ≠ 0 := by
    rw [← linDet_apply, linDet_single]
    exact hk
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hcol : (fun a : Fin m => (tangMatrix V z (Pi.single k (1 : ℝ))).col (Fin.castSucc a))
      = tangGrad V z := by
    funext a i
    rw [Matrix.col_apply, tangMatrix_apply_castSucc]
    rfl
  rw [← hcol]
  simpa [Function.comp_def] using hli.comp Fin.castSucc (Fin.castSucc_injective m)

/-- The gradients of the components of `V` at `z` are linearly independent if and only if the
generalised cross product `crossField V z` is nonzero. -/
theorem linearIndependent_tangGrad_iff_crossField_ne_zero {m : ℕ}
    (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ) :
    LinearIndependent ℝ (tangGrad V z) ↔ crossField V z ≠ 0 :=
  ⟨fun h => crossField_ne_zero_of_li V z h,
    fun h => linearIndependent_tangGrad_of_crossField_ne_zero V z h⟩

/-- `z` is a critical point of `V` (the derivative functionals of the components are linearly
dependent) if and only if the generalised cross product of the gradients vanishes at `z`. -/
theorem not_linearIndependent_iff_crossField_eq_zero {m : ℕ}
    (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ) :
    ¬ LinearIndependent ℝ (fun a => fderiv ℝ (fun w => V w a) z) ↔ crossField V z = 0 := by
  rw [linearIndependent_fderiv_iff_tangGrad, linearIndependent_tangGrad_iff_crossField_ne_zero,
    not_ne_iff]

theorem khoSubm_bad_closed {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (hproper : IsProperMap (liftSystem S F)) (hcont : Continuous (crossField (liftSystem S F))) :
    IsClosed {y : Fin n → ℝ | ¬ KhoSubmersion S F y} := by
  have hC : IsClosed {z : Fin (n + 1) → ℝ | crossField (liftSystem S F) z = 0} :=
    isClosed_eq hcont continuous_const
  have himg : IsClosed
      (liftSystem S F '' {z : Fin (n + 1) → ℝ | crossField (liftSystem S F) z = 0}) :=
    hproper.isClosedMap _ hC
  convert himg using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hsub
    rw [KhoSubmersion] at hsub
    push Not at hsub
    obtain ⟨z, hz, hzli⟩ := hsub
    exact ⟨z, (not_linearIndependent_iff_crossField_eq_zero (liftSystem S F) z).mp hzli, hz⟩
  · rintro ⟨z, hz, rfl⟩ hsub
    exact (not_linearIndependent_iff_crossField_eq_zero (liftSystem S F) z).mpr hz (hsub z rfl)

end Work.WilE2
