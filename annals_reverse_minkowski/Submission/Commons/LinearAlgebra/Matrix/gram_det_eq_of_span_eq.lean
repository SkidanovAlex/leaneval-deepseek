import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

/-- Change of basis for "raw" Gram determinants over ℝ: if the columns of `U` are the columns
of `V` multiplied by `P` (i.e. `U = V * P`), the Gram determinant changes by `(det P)^2`. -/
private lemma det_gram_eq_of_mul_right {r n : ℕ} (U V : Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin r) ℝ) (hU : U = V * P) :
    (U.transpose * U).det = P.det ^ 2 * (V.transpose * V).det := by
  calc
    (U.transpose * U).det = ((V * P).transpose * (V * P)).det := by rw [hU]
    _ = (P.transpose * (V.transpose * V) * P).det := by
      rw [Matrix.transpose_mul]
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V.transpose V P]
    _ = P.det ^ 2 * (V.transpose * V).det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring

/-- Two `ℤ`-bases `u` and `v` of the same submodule `M ≤ ℤ^n` are related by an integer matrix
`P` of determinant `±1` (so `(det P)^2 = 1`). More precisely, the `j`-th vector `u j` is the
`ℤ`-linear combination `∑ k, P k j • v k` of the vectors `v k`. -/
private lemma change_matrix_of_basis_eq {n r : ℕ} (M : Submodule ℤ (Fin n → ℤ))
    (u v : Fin r → Fin n → ℤ)
    (hu_mem : ∀ i : Fin r, u i ∈ M)
    (hu_span : M ≤ Submodule.span ℤ (Set.range u))
    (hu_lin : LinearIndependent ℤ u)
    (hv_mem : ∀ i : Fin r, v i ∈ M)
    (hv_span : M ≤ Submodule.span ℤ (Set.range v))
    (hv_lin : LinearIndependent ℤ v) :
    ∃ P : Matrix (Fin r) (Fin r) ℤ,
      P.det ^ 2 = 1 ∧
      (∀ j : Fin r, ∀ i : Fin n,
        ((u j i : ℤ) : ℝ) = ∑ k : Fin r, ((P k j : ℤ) : ℝ) * (((v k i : ℤ) : ℝ))) := by
  classical
  let E := Fin n → ℤ
  let SU : Submodule ℤ E := Submodule.span ℤ (Set.range u)
  let SV : Submodule ℤ E := Submodule.span ℤ (Set.range v)
  have hSU_le_M : SU ≤ M := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact hu_mem j
  have hSV_le_M : SV ≤ M := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact hv_mem j
  have hSU : SU = M := le_antisymm hSU_le_M hu_span
  have hSV : SV = M := le_antisymm hSV_le_M hv_span
  let bU : Module.Basis (Fin r) ℤ M :=
    (Module.Basis.span hu_lin).map (LinearEquiv.ofEq SU M hSU)
  let bV : Module.Basis (Fin r) ℤ M :=
    (Module.Basis.span hv_lin).map (LinearEquiv.ofEq SV M hSV)
  let P : Matrix (Fin r) (Fin r) ℤ := bV.toMatrix (fun j : Fin r => bU j)
  have hbUval (j : Fin r) : (bU j : E) = u j := by
    simp [bU]
  have hbVval (j : Fin r) : (bV j : E) = v j := by
    simp [bV]
  have hcolM (j : Fin r) : (∑ k : Fin r, P k j • bV k : M) = bU j := by
    simp [P, bV.sum_toMatrix_smul_self]
  have hcolE (j : Fin r) : u j = ∑ k : Fin r, P k j • v k := by
    have h := congrArg (fun m : M => (m : E)) (hcolM j).symm
    -- h : (bU j : E) = (↑(∑ k : Fin r, P k j • bV k) : E)
    rw [hbUval] at h
    -- want : u j = ∑ k : Fin r, P k j • v k
    simpa [hbVval] using h
  have hdetP : P.det ^ 2 = 1 := by
    haveI : Invertible P := Module.Basis.invertibleToMatrix bV bU
    have h1 : P.det * (⅟P).det = 1 := by
      calc
        P.det * (⅟P).det = (P * ⅟P).det := (Matrix.det_mul P (⅟P)).symm
        _ = 1 := by simp
    have h2 : (⅟P).det * P.det = 1 := by
      calc
        (⅟P).det * P.det = (⅟P * P).det := (Matrix.det_mul (⅟P) P).symm
        _ = 1 := by simp
    let u : ℤˣ := ⟨P.det, (⅟P).det, h1, h2⟩
    have hPunit : IsUnit P.det := ⟨u, rfl⟩
    exact Int.isUnit_sq hPunit
  refine ⟨P, hdetP, ?_⟩
  intro j i
  have hcolj := congr_fun (hcolE j) i
  -- hcolj : u j i = (∑ k : Fin r, P k j • v k) i
  rw [hcolj]
  -- now simplify the sum of Pi-smul at coordinate i, and cast both sides to ℝ
  simp [Finset.sum_apply, Int.cast_sum]
theorem gram_det_eq_of_span_eq
    {n r : ℕ} (M : Submodule ℤ (Fin n → ℤ))
    (u v : Fin r → Fin n → ℤ)
    (hu_mem : ∀ i : Fin r, u i ∈ M)
    (hu_span : M ≤ Submodule.span ℤ (Set.range u))
    (hu_lin : LinearIndependent ℤ u)
    (hv_mem : ∀ i : Fin r, v i ∈ M)
    (hv_span : M ≤ Submodule.span ℤ (Set.range v))
    (hv_lin : LinearIndependent ℤ v) :
    (((Matrix.of (fun i : Fin n => fun j : Fin r => u j i)).map (fun z : ℤ => (z : ℝ))).transpose *
        ((Matrix.of (fun i : Fin n => fun j : Fin r => u j i)).map (fun z : ℤ => (z : ℝ)))).det =
      (((Matrix.of (fun i : Fin n => fun j : Fin r => v j i)).map (fun z : ℤ => (z : ℝ))).transpose *
        ((Matrix.of (fun i : Fin n => fun j : Fin r => v j i)).map (fun z : ℤ => (z : ℝ)))).det := by
  classical
  let UR : Matrix (Fin n) (Fin r) ℝ :=
    (Matrix.of (fun i : Fin n => fun j : Fin r => u j i)).map (fun z : ℤ => (z : ℝ))
  let VR : Matrix (Fin n) (Fin r) ℝ :=
    (Matrix.of (fun i : Fin n => fun j : Fin r => v j i)).map (fun z : ℤ => (z : ℝ))
  change (UR.transpose * UR).det = (VR.transpose * VR).det
  obtain ⟨P, hPdet, hcol⟩ := change_matrix_of_basis_eq M u v hu_mem hu_span hu_lin hv_mem hv_span hv_lin
  let PR : Matrix (Fin r) (Fin r) ℝ := P.map (fun z : ℤ => (z : ℝ))
  have hUmat : UR = VR * PR := by
    ext i j
    simp [UR, VR, PR, Matrix.mul_apply]
    rw [hcol j i]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hPRsq : PR.det ^ 2 = 1 := by
    rw [show PR.det = ((P.det : ℤ) : ℝ) from (Int.cast_det P).symm]
    rw [← Int.cast_pow]
    exact_mod_cast hPdet
  calc
    (UR.transpose * UR).det = PR.det ^ 2 * (VR.transpose * VR).det :=
      det_gram_eq_of_mul_right UR VR PR hUmat
    _ = (VR.transpose * VR).det := by
      rw [hPRsq]
      ring

end Commons.LinearAlgebra.Matrix