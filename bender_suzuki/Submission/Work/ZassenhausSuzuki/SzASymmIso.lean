import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The explicit isomorphism `A(K,θ) ≃* A(K,θ⁻¹)`

`Work.ZassenhausSuzuki.szA_symm_equiv` gives an isomorphism `A(K,θ) ≃* A(K,θ⁻¹)` carrying
the torus `h_λ` to `h'_{θλ}`; here we record the *explicit* map and its values at the three
canonical elements, which the `θ ↦ θ⁻¹` case of `suzukiTitsOfFix` needs (`⟨1,0⟩ ↦ ⟨1,1⟩` is
the normalisation of the structure element).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs

variable {K : Type*} [Field K] [CharP K 2]

/-- The map `(a,b) ↦ (θa, b + a·θa)` is an isomorphism `A(K,θ) ≃* A(K,θ⁻¹)`. -/
def szASymm (θ : K ≃+* K) : SzA K θ ≃* SzA K θ.symm where
  toFun x := ⟨θ x.a, x.b + x.a * θ x.a⟩
  invFun y := ⟨θ.symm y.a, y.b + y.a * θ.symm y.a⟩
  left_inv := by
    intro x
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    ext <;> simp only [map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply,
      SzA.mul_a, SzA.mul_b] <;> ring_nf <;> simp [h2]
  right_inv := by
    intro y
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    ext <;> simp only [map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply,
      SzA.mul_a, SzA.mul_b] <;> ring_nf <;> simp [h2]
  map_mul' := by
    intro x y
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    ext <;> simp only [map_add, map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply,
      SzA.mul_a, SzA.mul_b] <;> ring_nf <;> simp [h2]

@[simp] theorem szASymm_a (θ : K ≃+* K) (x : SzA K θ) :
    (szASymm θ x).a = θ x.a := rfl

@[simp] theorem szASymm_b (θ : K ≃+* K) (x : SzA K θ) :
    (szASymm θ x).b = x.b + x.a * θ x.a := rfl

/-- `szASymm` carries the torus `h_λ` of `A(K,θ)` to `h'_{θλ}` of `A(K,θ⁻¹)`. -/
theorem szASymm_hLam (θ : K ≃+* K) (lam : K) (x : SzA K θ) :
    szASymm θ (SzA.hLam θ lam x) = SzA.hLam θ.symm (θ lam) (szASymm θ x) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext <;> simp only [szASymm_a, szASymm_b, SzA.hLam_a, SzA.hLam_b, SzA.mul_a, SzA.mul_b,
    map_add, map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] <;>
    (first | ring_nf | skip) <;> simp [h2] <;> ring_nf

/-- `szASymm θ ⟨1,0⟩ = ⟨1,1⟩`: this is the normalisation used in the `θ ↦ θ⁻¹` case. -/
theorem szASymm_one_zero (θ : K ≃+* K) :
    szASymm θ (⟨1, 0⟩ : SzA K θ) = (⟨1, 1⟩ : SzA K θ.symm) := by
  ext <;> simp

/-- `szASymm θ ⟨1,1⟩ = ⟨1,0⟩`. -/
theorem szASymm_one_one (θ : K ≃+* K) :
    szASymm θ (⟨1, 1⟩ : SzA K θ) = (⟨1, 0⟩ : SzA K θ.symm) := by
  ext <;> simp [CharTwo.add_self_eq_zero]

/-- `szASymm θ ⟨0,1⟩ = ⟨0,1⟩`: the centre is preserved. -/
theorem szASymm_zero_one (θ : K ≃+* K) :
    szASymm θ (⟨0, 1⟩ : SzA K θ) = (⟨0, 1⟩ : SzA K θ.symm) := by
  ext <;> simp

end Work.ZassenhausSuzuki
