import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `lorentzReflection v` is a Lorentz matrix

For a *spacelike* vector `v` of `ℝ^{1,4}` (`⟨v,v⟩ > 0`), the reflection
`lorentzReflection v = 1 − (2/⟨v,v⟩) • (v ⊗ Jv)` in the hyperplane `{x : ⟨x,v⟩ = 0}` is an
element of the Lorentz group preserving the upper sheet, i.e. `IsLorentzMat (lorentzReflection v)`.

The two ingredients are:

* `lorentzReflection_mulVec` — the reflection acts on a vector by
  `x ↦ x − 2⟨v,x⟩/⟨v,v⟩ · v`;
* `lorentz_refl_invariant` — consequently it preserves the Lorentz form,
  `⟨A x, A y⟩ = ⟨x,y⟩`, which is exactly the matrix identity `Aᵀ J A = J` tested on basis vectors.

The positivity of the last diagonal entry is elementary: `(lorentzReflection v) 4 4 = 1 + 2 v₄²/⟨v,v⟩ > 0`.

The auxiliary lemmas below are `private`: several teammates are proving closely related statements
about `lorentzReflection` in the same namespace, and nothing outside this file needs them.
-/

namespace Work.HypModel

open scoped Matrix InnerProductSpace

/-- `lorentz v x` is the Euclidean dot product of `x` with `J *ᵥ v`. -/
private theorem lorentz_eq_dotProduct_Jv (v x : V5) : lorentz v x = (J *ᵥ v) ⬝ᵥ x := by
  rw [lorentz_comm, lorentz_eq_dotProduct, dotProduct_comm]

/-- `MulOpposite` scalar multiplication of a vector of `V5` is ordinary multiplication. -/
private theorem op_smul_V5 (r : ℝ) (u : V5) : MulOpposite.op r • u = r • u := by
  ext i; simp [mul_comm]

/-- **The Lorentz reflection is a linear reflection:**
`(lorentzReflection v) *ᵥ x = x − 2⟨v,v⟩⁻¹⟨v,x⟩ · v`. -/
private theorem lorentzReflection_mulVec (v x : V5) :
    lorentzReflection v *ᵥ x = x - (2 * (lorentz v v)⁻¹ * lorentz v x) • v := by
  rw [lorentzReflection, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  rw [op_smul_V5, smul_smul]
  simp only [lorentz_eq_dotProduct_Jv]

/-- **A Lorentz reflection in a spacelike hyperplane preserves the Lorentz form.** -/
private theorem lorentz_refl_invariant {v : V5} (hv : 0 < lorentz v v) (x y : V5) :
    lorentz (lorentzReflection v *ᵥ x) (lorentzReflection v *ᵥ y) = lorentz x y := by
  rw [lorentzReflection_mulVec, lorentzReflection_mulVec]
  simp only [lorentz_sub_left, lorentz_sub_right, lorentz_smul_left, lorentz_smul_right]
  rw [lorentz_comm x v]
  field_simp
  ring

/-- The matrix identity `Aᵀ J A = J` for `A = lorentzReflection v`, `⟨v,v⟩ > 0`. -/
private theorem lorentzReflection_transpose_mul_self {v : V5} (hv : 0 < lorentz v v) :
    (lorentzReflection v)ᵀ * J * lorentzReflection v = J := by
  have key : ∀ x y : V5,
      x ⬝ᵥ (((lorentzReflection v)ᵀ * J * lorentzReflection v) *ᵥ y) = x ⬝ᵥ (J *ᵥ y) := by
    intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [← dotProduct_mulVec_transpose]
    rw [← lorentz_eq_dotProduct, lorentz_refl_invariant hv, lorentz_eq_dotProduct]
  ext i j
  have h := key (Pi.single i 1) (Pi.single j 1)
  simp only [single_one_dotProduct, Matrix.mulVec_single_one] at h
  exact h

theorem isLorentzMat_lorentzReflection {v : V5} (hv : 0 < lorentz v v) :
    IsLorentzMat (lorentzReflection v) := by
  refine ⟨lorentzReflection_transpose_mul_self hv, ?_⟩
  rw [lorentzReflection]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, J_mulVec,
    Matrix.one_apply_eq, ↓reduceIte, smul_eq_mul]
  have hq : 0 < (lorentz v v)⁻¹ := inv_pos.mpr hv
  nlinarith [sq_nonneg (v 4)]

end Work.HypModel
