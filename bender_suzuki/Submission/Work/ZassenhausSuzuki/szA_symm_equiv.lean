import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `A(K,θ) ≅ A(K,θ⁻¹)` (L5 of the lead's design note)

Higman's classification determines the field automorphism only up to `θ ↔ θ⁻¹`.  The
isomorphism is `φ (a,b) = (θ a, b + a·θ a)`, and it carries `h_λ` to `h_{θλ}`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem szA_symm_equiv {m : ℕ} (θ : GaloisField 2 m ≃+* GaloisField 2 m) :
    ∃ φ : SzA (GaloisField 2 m) θ ≃* SzA (GaloisField 2 m) θ.symm,
      ∀ (lam : GaloisField 2 m) (x : SzA (GaloisField 2 m) θ),
        φ (SzA.hLam θ lam x) = SzA.hLam θ.symm (θ lam) (φ x) := by
  have h2 : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero _ _
  refine ⟨{ toFun := fun x => ⟨θ x.a, x.b + x.a * θ x.a⟩
            invFun := fun y => ⟨θ.symm y.a, y.b + y.a * θ.symm y.a⟩
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_ }, ?_⟩
  · intro x
    ext <;> simp only [map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply,
      SzA.mul_a, SzA.mul_b] <;> ring_nf <;> simp [h2]
  · intro y
    ext <;> simp only [map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply,
      SzA.mul_a, SzA.mul_b] <;> ring_nf <;> simp [h2]
  · intro x y
    ext <;> simp only [map_add, map_mul, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply,
      SzA.mul_a, SzA.mul_b] <;> ring_nf <;> simp [h2]
  · intro lam x
    ext <;> simp only [SzA.hLam_a, SzA.hLam_b, SzA.mul_a, SzA.mul_b, map_add, map_mul,
      RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] <;>
      (first | ring_nf | skip) <;> simp [h2] <;> ring_nf

end Work.ZassenhausSuzuki
