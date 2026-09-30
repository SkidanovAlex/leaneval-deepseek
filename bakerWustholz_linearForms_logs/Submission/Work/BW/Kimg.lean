import Mathlib
import Submission.Work.BW.Est17Ext

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The image of `K` inside the Kummer extension

For `L = EL φ ρ = ℚ(φ(K), ρ₁,…,ρ_r)`, the map `inclE φ ρ : K →+* L` has image a copy of
`φ(K)`.  We record that image as an intermediate field `Kimg φ ρ`, the induced
`ℚ`-algebra isomorphism `KimgEquiv : K ≃ₐ[ℚ] Kimg φ ρ`, and the fact that `Kimg φ ρ` is a
number field.

These are the ingredients for `Work.BW.est17_height_ext`, which computes the height of a tuple
of `K` in the Kummer extension `L`.
-/

namespace Work.BW

open Complex

variable {K : Type*} [Field K] [NumberField K] {r : ℕ}

/-- The image of `K` in `L = EL φ ρ`, as an intermediate field `ℚ ⊆ Kimg ⊆ L`. -/
noncomputable def Kimg (φ : K →+* ℂ) (ρ : Fin r → ℂ) : IntermediateField ℚ (EL φ ρ) :=
  (inclE φ ρ).toRatAlgHom.fieldRange

theorem mem_Kimg {φ : K →+* ℂ} {ρ : Fin r → ℂ} {y : EL φ ρ} :
    y ∈ Kimg φ ρ ↔ ∃ x : K, inclE φ ρ x = y := by
  rw [Kimg, AlgHom.mem_fieldRange]
  simp

theorem inclE_mem_Kimg {φ : K →+* ℂ} {ρ : Fin r → ℂ} (x : K) :
    inclE φ ρ x ∈ Kimg φ ρ :=
  mem_Kimg.mpr ⟨x, rfl⟩

/-- The canonical `ℚ`-algebra isomorphism `K ≃ Kimg φ ρ`, induced by `inclE φ ρ`. -/
noncomputable def KimgEquiv (φ : K →+* ℂ) (ρ : Fin r → ℂ) : K ≃ₐ[ℚ] Kimg φ ρ :=
  AlgEquiv.ofInjective (inclE φ ρ).toRatAlgHom (inclE φ ρ).injective

@[simp]
theorem KimgEquiv_apply {φ : K →+* ℂ} {ρ : Fin r → ℂ} (x : K) :
    ((KimgEquiv φ ρ x : Kimg φ ρ) : EL φ ρ) = inclE φ ρ x :=
  AlgEquiv.ofInjective_apply _ _ x

/-- `Kimg φ ρ` is a number field (as a subfield of the number field `L`). -/
theorem Kimg_numberField (φ : K →+* ℂ) (ρ : Fin r → ℂ) [NumberField (EL φ ρ)] :
    NumberField (Kimg φ ρ) := by
  haveI : CharZero (Kimg φ ρ) := IntermediateField.charZero _
  exact NumberField.mk

end Work.BW
