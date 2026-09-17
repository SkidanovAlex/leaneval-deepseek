import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial

namespace Commons.LinearAlgebra.Matrix.Cartan

open scoped BigOperators

/-!
# The sign character of the Weyl group of `E₈` is well defined

Words `L : List (Fin 8)` of simple reflections act on weights `Fin 8 → ℤ` by
`wact L v = L.foldl (fun w i => sref i w) v`, where `sref i v = v - vᵢ αᵢ`.  The main result of
this file,

* `E8_wact_sign`: if `wact L₁ = wact L₂` as functions, then `(-1)^{L₁.length} = (-1)^{L₂.length}`,

says that the parity of the length of a word depends only on the Weyl group element it defines: the
sign `(-1)^{length}` is a well-defined character of `W(E₈)`.

The proof computes `wact L` as a matrix `wactMat L` in the standard basis of `ℤ⁸`, proves
`(wactMat L).det = (-1)^{L.length}` by inducting on `L`, and observes that `wact L₁ = wact L₂`
forces `wactMat L₁ = wactMat L₂`.  The only input about the individual reflection is
`(srefMat i).det = -1`, which is the rank-one determinant identity
`det (1 + u * vᵀ) = 1 + v ⬝ u` applied to the reflection `sref i`.
-/

/-- The matrix of the simple reflection `sref i` in the standard basis of `ℤ⁸`, written as
`1 + u * vᵀ` with `u a = -(E8m i a)` and `v = Pi.single i 1`. -/
def srefMat (i : Fin 8) : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.replicateCol (Fin 1) (fun a : Fin 8 => -(E8m i a)) *
      Matrix.replicateRow (Fin 1) (Pi.single i (1 : ℤ) : Fin 8 → ℤ)

/-- The entries of `srefMat i` are the values of the reflection `sref i` on the standard basis. -/
lemma srefMat_apply (i a b : Fin 8) : srefMat i a b = sref i (Pi.single b 1) a := by
  simp only [srefMat, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, Fin.sum_univ_one, Pi.single_apply,
    sref_apply]
  have hcomm : (if b = i then (1 : ℤ) else 0) = (if i = b then 1 else 0) := by
    by_cases h : i = b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hcomm]; ring

/-- The determinant of a rank-one perturbation of the identity: `det (1 + u * vᵀ) = 1 + v ⬝ u`. -/
lemma det_one_add_rankOne (u v : Fin 8 → ℤ) :
    (1 + Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v).det = 1 + v ⬝ᵥ u :=
  Matrix.det_one_add_replicateCol_mul_replicateRow u v

/-- The reflection `sref i` has determinant `-1`. -/
lemma srefMat_det (i : Fin 8) : (srefMat i).det = -1 := by
  have h := det_one_add_rankOne (fun a : Fin 8 => -(E8m i a))
    (Pi.single i (1 : ℤ) : Fin 8 → ℤ)
  refine h.trans ?_
  simp only [dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
  rw [if_pos rfl, one_mul, E8m_diag]
  norm_num

/-- Expansion of a vector of `ℤ⁸` in the standard basis `Pi.single k 1`. -/
lemma eq_sum_smul_single (v : Fin 8 → ℤ) :
    v = ∑ k, v k • (Pi.single k (1 : ℤ) : Fin 8 → ℤ) := by
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    rw [if_neg (Ne.symm hba), mul_zero]
  · intro ha; exact absurd (Finset.mem_univ a) ha

/-- The matrix of the linear map `wact L` in the standard basis of `ℤ⁸`. -/
def wactMat (L : List (Fin 8)) : Matrix (Fin 8) (Fin 8) ℤ := fun a b => wact L (Pi.single b 1) a

lemma wactMat_nil : wactMat ([] : List (Fin 8)) = 1 := by
  ext a b
  simp [wactMat, Matrix.one_apply, Pi.single_apply]

/-- The matrices of the Weyl-group action multiply along concatenation with a simple reflection. -/
lemma wactMat_cons (i : Fin 8) (L : List (Fin 8)) : wactMat (i :: L) = wactMat L * srefMat i := by
  ext a b
  rw [Matrix.mul_apply]
  show wact (i :: L) (Pi.single b 1) a = ∑ k, wactMat L a k * srefMat i k b
  rw [wact_cons, eq_sum_smul_single (sref i (Pi.single b 1)), wact_sum_smul]
  simp only [wactMat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, srefMat_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The determinant of the matrix of `wact L` is `(-1)^{L.length}`. -/
lemma wactMat_det (L : List (Fin 8)) : (wactMat L).det = (-1 : ℤ) ^ L.length := by
  induction L with
  | nil => rw [List.length_nil, pow_zero, wactMat_nil, Matrix.det_one]
  | cons i L ih =>
      rw [List.length_cons, wactMat_cons, Matrix.det_mul, ih, srefMat_det, pow_succ]

theorem E8_wact_sign {L₁ L₂ : List (Fin 8)} (h : ∀ v : Fin 8 → ℤ, Commons.LinearAlgebra.Matrix.Cartan.wact L₁ v = Commons.LinearAlgebra.Matrix.Cartan.wact L₂ v) : (-1 : ℤ) ^ L₁.length = (-1 : ℤ) ^ L₂.length := by
  have hm : wactMat L₁ = wactMat L₂ := by
    ext a b
    exact congrFun (h (Pi.single b 1)) a
  calc (-1 : ℤ) ^ L₁.length = (wactMat L₁).det := (wactMat_det L₁).symm
    _ = (wactMat L₂).det := by rw [hm]
    _ = (-1 : ℤ) ^ L₂.length := wactMat_det L₂

end Commons.LinearAlgebra.Matrix.Cartan
