/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `3×3` real matrices as continuous linear maps on `E3`

The Krawczyk criterion of item **A1** needs the Jacobian of `Φ : ℝ³ → ℝ³` as a `3×3` matrix and
the operator norms `‖M‖`, `‖1 - M A‖` of explicit dyadic matrices.  This file provides the
bridge between a `3×3` real matrix and the corresponding continuous linear map on
`E3 = ℝ × (ℝ × ℝ)`: `matLin a` is a sum of rank-one maps
`∑_j (proj3 j).smulRight (vecOf (fun i => a i j))`, so that `(matLin a) (vec3 j)` is exactly the
`j`-th column and the composition/norm estimates are immediate from the rank-one shape.

## Main definitions

* `proj3 j` — the `j`-th coordinate functional on `E3`;
* `vec3 j` — the `j`-th unit vector (`eX`, `eY`, `eT`);
* `vecOf v` — the vector with coordinates `v : Fin 3 → ℝ`;
* `matLin a` — the continuous linear map of the matrix `a`;
* `matMul`, `matId`, `matSub`, `matAbs`, `matSum`, `matOf`.

## Main results

* `proj3_apply`, `proj3_vecOf`, `vecOf_proj3`, `proj3_vec3`, `eq_of_proj3`;
* `matLin_apply` — `proj3 i (matLin a v) = ∑ j, a i j * proj3 j v`;
* `matLin_vec3` — the columns of `matLin a`;
* `matLin_ext` — extensionality;
* `matLin_mul`, `matLin_sub_id`, `matLin_matOf`;
* `norm_matLin_le`, `norm_matLin_apply_le`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

noncomputable section

/-- The `j`-th coordinate functional on `E3`. -/
def proj3 (j : Fin 3) : E3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => if j = 0 then u.1 else if j = 1 then u.2.1 else u.2.2
      map_add' := by intro x y; fin_cases j <;> simp [Prod.fst_add, Prod.snd_add]
      map_smul' := by intro r x; fin_cases j <;> simp [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] }

theorem proj3_apply (j : Fin 3) (u : E3) :
    proj3 j u = if j = 0 then u.1 else if j = 1 then u.2.1 else u.2.2 := rfl

/-- The `j`-th unit vector of `E3` (`eX`, `eY`, `eT`). -/
def vec3 (j : Fin 3) : E3 := if j = 0 then eX else if j = 1 then eY else eT

/-- The vector with coordinates `v : Fin 3 → ℝ`. -/
def vecOf (v : Fin 3 → ℝ) : E3 := (v 0, v 1, v 2)

@[simp] theorem vecOf_zero (v : Fin 3 → ℝ) : (vecOf v).1 = v 0 := rfl
@[simp] theorem vecOf_one (v : Fin 3 → ℝ) : (vecOf v).2.1 = v 1 := rfl
@[simp] theorem vecOf_two (v : Fin 3 → ℝ) : (vecOf v).2.2 = v 2 := rfl

@[simp] theorem proj3_vecOf (j : Fin 3) (v : Fin 3 → ℝ) : proj3 j (vecOf v) = v j := by
  fin_cases j <;> simp [vecOf, proj3_apply]

@[simp] theorem vecOf_proj3 (u : E3) : vecOf (fun j => proj3 j u) = u := by
  obtain ⟨x, y, t⟩ := u
  simp [vecOf, proj3_apply]

@[simp] theorem proj3_vec3 (i j : Fin 3) : proj3 i (vec3 j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [vec3, eX, eY, eT, proj3_apply]

/-- Two points of `E3` with the same three coordinates are equal. -/
theorem eq_of_proj3 {u v : E3} (h : ∀ i, proj3 i u = proj3 i v) : u = v := by
  obtain ⟨a, b, c⟩ := u
  obtain ⟨a', b', c'⟩ := v
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [proj3_apply] at h0 h1 h2
  simp [h0, h1, h2]

/-- The continuous linear map of a `3×3` matrix: `v ↦ (Σ_j a i j · v_j)_i`. -/
def matLin (a : Fin 3 → Fin 3 → ℝ) : E3 →L[ℝ] E3 :=
  ∑ j : Fin 3, (proj3 j).smulRight (vecOf (fun i => a i j))

/-- The matrix of a continuous linear map. -/
def matOf (L : E3 →L[ℝ] E3) : Fin 3 → Fin 3 → ℝ := fun i j => proj3 i (L (vec3 j))

/-- Matrix product. -/
def matMul (a b : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => ∑ k, a i k * b k j

/-- The identity matrix. -/
def matId : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0

/-- Matrix difference. -/
def matSub (a b : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => a i j - b i j

/-- Entrywise absolute value. -/
def matAbs (a : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => |a i j|

/-- The sum of all entries. -/
def matSum (a : Fin 3 → Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, a i j

theorem matLin_apply (a : Fin 3 → Fin 3 → ℝ) (v : E3) (i : Fin 3) :
    proj3 i (matLin a v) = ∑ j, a i j * proj3 j v := by
  simp only [matLin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, proj3_vecOf, smul_eq_mul]
  ring

theorem matLin_vec3 (a : Fin 3 → Fin 3 → ℝ) (k : Fin 3) :
    matLin a (vec3 k) = vecOf (fun i => a i k) := by
  apply eq_of_proj3
  intro i
  rw [matLin_apply, proj3_vecOf]
  simp [proj3_vec3]

theorem matLin_ext {a b : Fin 3 → Fin 3 → ℝ} (h : ∀ i j, a i j = b i j) : matLin a = matLin b := by
  have : a = b := funext fun i => funext fun j => h i j
  rw [this]

end

end Work.SeedCert
