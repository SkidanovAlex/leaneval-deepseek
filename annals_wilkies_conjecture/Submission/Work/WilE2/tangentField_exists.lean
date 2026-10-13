import Mathlib
import Submission.Work.WilE2.contDiff_det
import Submission.Work.WilE2.contDiff_fderiv_component
import Submission.Work.WilE2.linearIndependent_tangGrad

/-!
# Existence of the tangent (cross-product) field

Let `V : ℝ^{m+1} → ℝ^m` be `C²` and suppose that at every zero of `V` the differentials of the
components of `V` are linearly independent (so that `V` has no critical zero, i.e. `0` is a
regular value).  We construct a `C¹` vector field `X` on `ℝ^{m+1}` which at every zero of `V`
is nonzero and tangent to the level set `V = 0`, given by the generalised cross product of the
gradients of the components of `V`.

Concretely, for `z, v : ℝ^{m+1}` let `M(z,v)` be the `(m+1) × (m+1)` matrix whose `j`-th column
(`j < m`) is the gradient of the `j`-th component of `V` at `z`, and whose last column is `v`.
The determinant `det M(z,v)` is linear in `v`, so there is a unique vector `X z ∈ ℝ^{m+1}` with

  `det M(z,v) = ∑ i, X z i * v i  for all v`,

namely the vector of cofactors `X z i = det M(z, e_i)` (this is the generalised cross product of
the gradients `∇V_0, …, ∇V_{m-1}`).  We prove that this `X` has the three required properties:

* it is `C¹` (the matrix entries `z ↦ ∂_i V_j(z)` are `C¹`, and `det` is a polynomial);
* at a zero of `V` it is nonzero: were it zero, all the determinants `det M(z,v)` would vanish, so
  the gradients `∇V_0, …, ∇V_{m-1}` would be linearly dependent (extend them to a basis otherwise);
* at a zero of `V` it is tangent: `∂_i V_a (X z) = ∑_i X z i * ∂_i V_a`, and the matrix `M(z, ∇V_a)`
  has two equal columns (the `a`-th and the last), hence determinant zero.
-/

set_option autoImplicit false

open Classical

noncomputable section

namespace Work.WilE2

/-- The `(m+1) × (m+1)` matrix whose `j`-th column (`j < m`) is the gradient of the `j`-th
component of `V` at `z`, and whose last column is `v`. -/
def tangMatrix {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z v : Fin (m + 1) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => if h : (j : ℕ) < m then
      fderiv ℝ (fun w => V w ⟨(j : ℕ), h⟩) z (Pi.single i (1 : ℝ))
    else v i

/-- The gradient vector of the `a`-th component of `V` at `z`, i.e. the vector of its partial
derivatives, as an element of `ℝ^{m+1}`. -/
def tangGrad {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ) :
    Fin m → (Fin (m + 1) → ℝ) :=
  fun a i => fderiv ℝ (fun w => V w a) z (Pi.single i (1 : ℝ))

/-- The generalised cross product of the gradients: `crossField V z i` is the determinant of the
matrix whose first `m` columns are the gradients of the components of `V` at `z` and whose last
column is the `i`-th standard basis vector.  Equivalently, the cofactor of the last column. -/
def crossField {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ) :
    Fin (m + 1) → ℝ :=
  fun i => (tangMatrix V z (Pi.single i (1 : ℝ))).det

lemma tangMatrix_apply_castSucc {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) (a : Fin m) :
    tangMatrix V z v k (Fin.castSucc a) = fderiv ℝ (fun w => V w a) z (Pi.single k (1 : ℝ)) := by
  rw [tangMatrix, Matrix.of_apply, dif_pos (by simpa using a.isLt)]
  congr 2

lemma tangMatrix_apply_last {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    tangMatrix V z v k (Fin.last m) = v k := by
  rw [tangMatrix, Matrix.of_apply, dif_neg (by simp [Fin.val_last])]

lemma tangMatrix_eq_snoc {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z v : Fin (m + 1) → ℝ) :
    tangMatrix V z v
      = fun i j => (Fin.snoc (tangGrad V z) v : Fin (m + 1) → (Fin (m + 1) → ℝ)) j i := by
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) j
  · rw [tangMatrix_apply_last, Fin.snoc_last]
  · rw [tangMatrix_apply_castSucc, Fin.snoc_castSucc]
    rfl

lemma tangMatrix_updateCol {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z v : Fin (m + 1) → ℝ) :
    tangMatrix V z v = (tangMatrix V z 0).updateCol (Fin.last m) v := by
  ext i j
  simp only [tangMatrix, Matrix.of_apply, Matrix.updateCol_apply]
  by_cases h : (j : ℕ) < m
  · have hj : j ≠ Fin.last m := by
      intro hh; rw [hh] at h; simp [Fin.val_last] at h
    rw [dif_pos h, ite_eq_right hj, dif_pos h]
  · have hj : j = Fin.last m := by
      apply Fin.ext
      have hle : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
      exact le_antisymm hle (Nat.le_of_not_lt h)
    rw [dif_neg h, ite_eq_left hj]

/-- `det (tangMatrix V z ·)` as a linear functional of the last column. -/
def linDet {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ) :
    (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ((tangMatrix V z 0).updateCol (Fin.last m) v).det
  map_add' u v := Matrix.det_updateCol_add (tangMatrix V z 0) (Fin.last m) u v
  map_smul' c u := Matrix.det_updateCol_smul (tangMatrix V z 0) (Fin.last m) c u

lemma linDet_apply {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z v : Fin (m + 1) → ℝ) :
    linDet V z v = (tangMatrix V z v).det := by
  show ((tangMatrix V z 0).updateCol (Fin.last m) v).det = (tangMatrix V z v).det
  conv_rhs => rw [tangMatrix_updateCol]

lemma linDet_single {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) :
    linDet V z (Pi.single i (1 : ℝ)) = crossField V z i := by
  rw [linDet_apply]; simp only [crossField]

lemma singl_sum {n : ℕ} (v : Fin n → ℝ) :
    v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  funext r
  rw [Finset.sum_apply, Finset.sum_eq_single r]
  · simp
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (i := b) (i' := r) hb.symm, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- The determinant identity: `X z` is the vector of cofactors of the last column, hence
`det (tangMatrix V z v) = ∑ i, crossField V z i * v i` for every `v`. -/
theorem crossField_det {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z v : Fin (m + 1) → ℝ) :
    (∑ i, crossField V z i * v i) = (tangMatrix V z v).det := by
  rw [← linDet_apply]
  conv_rhs => rw [singl_sum v]
  rw [map_sum]
  rw [show (∑ i, linDet V z (v i • (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ)))
      = ∑ i, crossField V z i * v i from by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, linDet_single, mul_comm]]

/-- Expansion of a continuous linear functional on `Fin n → ℝ` in the standard basis. -/
lemma clm_eq_sum_single {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (X : Fin n → ℝ) :
    L X = ∑ i, X i * L (Pi.single i (1 : ℝ)) := by
  conv_lhs => rw [singl_sum X]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]

/-- **Tangency.** If `z` is a zero of `V`, the cross-product field is annihilated by every
`∂_a V` (`a : Fin m`): the matrix `M(z, ∇V_a)` has two equal columns. -/
lemma tangGrad_apply_crossField {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z : Fin (m + 1) → ℝ) (a : Fin m) :
    fderiv ℝ (fun w => V w a) z (crossField V z) = 0 := by
  have hsum : fderiv ℝ (fun w => V w a) z (crossField V z)
      = ∑ i, crossField V z i * (tangGrad V z a) i := by
    rw [clm_eq_sum_single]
    rfl
  rw [hsum, crossField_det]
  refine Matrix.det_zero_of_column_eq (Fin.castSucc_ne_last a) (fun k => ?_)
  rw [tangMatrix_apply_castSucc, tangMatrix_apply_last]
  simp only [tangGrad]

/-- The entries of `tangMatrix V z v` are `C¹` functions of `z` (`V` being `C²`), hence so is the
matrix, and so is its determinant. -/
lemma contDiff_tangMatrix {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (hV : ContDiff ℝ 2 V) (v : Fin (m + 1) → ℝ) :
    ContDiff ℝ 1 (fun z : Fin (m + 1) → ℝ =>
      (fun (i j : Fin (m + 1)) => tangMatrix V z v i j)) := by
  rw [contDiff_pi]
  intro r
  rw [contDiff_pi]
  intro c
  by_cases hc : (c : ℕ) < m
  · rw [show (fun z : Fin (m + 1) → ℝ => (fun (i j : Fin (m + 1)) => tangMatrix V z v i j) r c)
        = (fun z => fderiv ℝ (fun w => V w ⟨(c : ℕ), hc⟩) z (Pi.single r (1 : ℝ))) from by
      funext z; simp only [tangMatrix, Matrix.of_apply, dif_pos hc]]
    exact contDiff_fderiv_component V hV ⟨(c : ℕ), hc⟩ r
  · rw [show (fun z : Fin (m + 1) → ℝ => (fun (i j : Fin (m + 1)) => tangMatrix V z v i j) r c)
        = (fun _ => v r) from by
      funext z; simp only [tangMatrix, Matrix.of_apply, dif_neg hc]]
    exact contDiff_const

/-- The cross-product field is `C¹`. -/
lemma contDiff_crossField {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (hV : ContDiff ℝ 2 V) : ContDiff ℝ 1 (crossField V) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_det.comp (contDiff_tangMatrix V hV (Pi.single i (1 : ℝ)))

/-- An independent family of `m` vectors in `ℝ^{m+1}` can be extended to a basis: concretely there
is `v` such that the `(m+1) × (m+1)` matrix with columns `G 0, …, G (m-1), v` has nonzero
determinant. -/
lemma exists_det_snoc_ne_zero {m : ℕ} (G : Fin m → (Fin (m + 1) → ℝ))
    (hG : LinearIndependent ℝ G) :
    ∃ v : Fin (m + 1) → ℝ,
      Matrix.det (fun i j => (Fin.snoc G v : Fin (m + 1) → (Fin (m + 1) → ℝ)) j i) ≠ 0 := by
  have hfin : m < Module.finrank ℝ (Fin (m + 1) → ℝ) := by
    rw [Module.finrank_fin_fun]; exact Nat.lt_succ_self m
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Fin (m + 1) → ℝ) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hG hfin
  have hspan := LinearIndependent.span_eq_top_of_card_eq_finrank hx hcard
  have hunit := (Module.Basis.is_basis_iff_det (Pi.basisFun ℝ (Fin (m + 1)))).mp ⟨hx, hspan⟩
  have hne : Matrix.det ((Pi.basisFun ℝ (Fin (m + 1))).toMatrix (Fin.snoc G x)) ≠ 0 := by
    have h := hunit.ne_zero
    rwa [Module.Basis.det_apply] at h
  have hmat : (Pi.basisFun ℝ (Fin (m + 1))).toMatrix (Fin.snoc G x)
      = Matrix.of (fun i j => (Fin.snoc G x : Fin (m + 1) → (Fin (m + 1) → ℝ)) j i) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.of_apply]
  rw [hmat] at hne
  exact ⟨x, hne⟩

/-- **Nonvanishing.** If the gradients `∇V_a` (`a : Fin m`) are linearly independent at `z`, then
the cross-product field is nonzero there: `crossField V z = 0` would force all determinants
`det M(z,v)` to vanish, contradicting the existence of a `v` completing the independent family to
a basis. -/
lemma crossField_ne_zero_of_li {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (z : Fin (m + 1) → ℝ) (hLI : LinearIndependent ℝ (tangGrad V z)) :
    crossField V z ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_det_snoc_ne_zero (tangGrad V z) hLI
  have hx' : (tangMatrix V z x).det ≠ 0 := by
    rwa [← tangMatrix_eq_snoc] at hx
  intro hz
  apply hx'
  rw [← crossField_det]
  simp [hz]

theorem tangentField_exists {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 2 V)
    (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => V w a) z)) :
    ∃ X : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ), ContDiff ℝ 1 X ∧
      (∀ z v : Fin (m + 1) → ℝ, (∑ i, X z i * v i) =
        (Matrix.of (fun (i : Fin (m + 1)) (j : Fin (m + 1)) =>
          if h : (j : ℕ) < m then fderiv ℝ (fun w => V w ⟨(j : ℕ), h⟩) z (Pi.single i (1 : ℝ))
          else v i)).det) ∧
      (∀ z, V z = 0 → X z ≠ 0) ∧
      (∀ z, V z = 0 → ∀ a, fderiv ℝ (fun w => V w a) z (X z) = 0) := by
  refine ⟨crossField V, contDiff_crossField V hV, ?_, ?_, ?_⟩
  · intro z v
    exact crossField_det V z v
  · intro z hz
    exact crossField_ne_zero_of_li V z (linearIndependent_tangGrad V z (hgrad z hz))
  · intro z hz a
    exact tangGrad_apply_crossField V z a

end Work.WilE2
