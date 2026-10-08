/-
Copyright (c) 2024. All rights reserved.

# Higman's four families `A(n,θ)`, `B(n,θ,ε)`, `C(n,ε)`, `D(n,θ,ε)`

Column V of Higman's table (REFS/higman_suzuki2groups.md §4) gives the explicit multiplication of
the four families of Suzuki 2-groups.  Written in the "two-step" normal form of
`Submission.Work.Higman.Model` (`(x, z) * (y, w) = (x + y, z + w + b x y)`), the cocycles are

* `A`: `b α γ = α · θ γ`                                               (`A = F`, `Z = F`)
* `B`: `b (α,β) (γ,δ) = α·θγ + ε·α·θδ + β·θδ`                          (`A = F × F`, `Z = F`)
* `C`: `b (α,β) (γ,δ) = α·θγ + ε·α^{1/2}·θ(δ²) + β·δ`                   (`A = F × F`, `Z = F`)
* `D`: `b (α,β) (γ,δ) = α·θγ + ε·θ³α·θδ + β·θ²δ`                       (`A = F × F`, `Z = F`)

(Here `α^{1/2}` is the inverse Frobenius of the finite field, `θ²`/`θ³` are powers of `θ`.)
-/

import Submission.Work.Higman.Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman

/-! ## Square roots in a finite field of characteristic two -/

/-- The inverse of the Frobenius of a finite field of characteristic two. -/
def sqrtF (F : Type*) [Field F] [CharP F 2] [Finite F] (x : F) : F :=
  (frobeniusEquiv F 2).symm x

theorem sqrtF_sq (F : Type*) [Field F] [CharP F 2] [Finite F] (x : F) : sqrtF F x ^ 2 = x := by
  simpa [sqrtF] using frobeniusEquiv_symm_pow_p (R := F) (p := 2) x

theorem sqrtF_add (F : Type*) [Field F] [CharP F 2] [Finite F] (x y : F) :
    sqrtF F (x + y) = sqrtF F x + sqrtF F y :=
  (frobeniusEquiv F 2).symm.map_add x y

/-! ## The four cocycles -/

/-- The cocycle of the family `A(n,θ)`. -/
def aCocycle (F : Type*) [Mul F] (θ : F → F) : F → F → F := fun a c => a * θ c

/-- The cocycle of the family `B(n,θ,ε)`. -/
def bCocycle (F : Type*) [Mul F] [Add F] (θ : F → F) (ε : F) : F × F → F × F → F :=
  fun u v => u.1 * θ v.1 + ε * (u.1 * θ v.2) + u.2 * θ v.2

/-- The cocycle of the family `C(n,ε)`. -/
def cCocycle (F : Type*) [Field F] [CharP F 2] [Finite F] (θ : F → F) (ε : F) :
    F × F → F × F → F :=
  fun u v => u.1 * θ v.1 + ε * (sqrtF F u.1 * θ (v.2 * v.2)) + u.2 * v.2

/-- The cocycle of the family `D(n,θ,ε)`. -/
def dCocycle (F : Type*) [Mul F] [Add F] (θ : F → F) (ε : F) : F × F → F × F → F :=
  fun u v => u.1 * θ v.1 + ε * (θ (θ (θ u.1)) * θ v.2) + u.2 * θ (θ v.2)

variable (F : Type*) [Field F] [CharP F 2]

instance instBiaddACocycle (θ : F ≃+* F) : Biadd (aCocycle F θ) where
  add_left a a' c := by simp only [aCocycle]; rw [add_mul]
  add_right a c c' := by simp only [aCocycle]; rw [map_add, mul_add]

instance instBiaddBCocycle (θ : F ≃+* F) (ε : F) : Biadd (bCocycle F θ ε) where
  add_left u u' v := by
    simp only [bCocycle, Prod.fst_add, Prod.snd_add, add_mul]
    ring
  add_right u v v' := by
    simp only [bCocycle, Prod.fst_add, Prod.snd_add, map_add, mul_add]
    ring

variable [Finite F]

instance instBiaddCCocycle (θ : F ≃+* F) (ε : F) : Biadd (cCocycle F θ ε) where
  add_left u u' v := by
    simp only [cCocycle, Prod.fst_add, Prod.snd_add, add_mul, sqrtF_add, map_add]
    ring
  add_right u v v' := by
    have hs : (v.2 + v'.2) * (v.2 + v'.2) = v.2 * v.2 + v'.2 * v'.2 := by
      rw [← pow_two, ← pow_two, ← pow_two, CharTwo.add_sq]
    simp only [cCocycle, Prod.fst_add, Prod.snd_add, hs, map_add, mul_add]
    ring

instance instBiaddDCocycle (θ : F ≃+* F) (ε : F) : Biadd (dCocycle F θ ε) where
  add_left u u' v := by
    simp only [dCocycle, Prod.fst_add, Prod.snd_add, add_mul, map_add]
    ring
  add_right u v v' := by
    simp only [dCocycle, Prod.fst_add, Prod.snd_add, map_add, mul_add]
    ring

/-! ## The four families as groups -/

/-- `A(n,θ)`: the group with `A = F`, `Z = F` and cocycle `aCocycle`. -/
abbrev AType (θ : F ≃+* F) : Type _ := TwoStep F F (aCocycle F θ)

/-- `B(n,θ,ε)`. -/
abbrev BType (θ : F ≃+* F) (ε : F) : Type _ := TwoStep (F × F) F (bCocycle F θ ε)

/-- `C(n,ε)`. -/
abbrev CType (θ : F ≃+* F) (ε : F) : Type _ := TwoStep (F × F) F (cCocycle F θ ε)

/-- `D(n,θ,ε)`. -/
abbrev DType (θ : F ≃+* F) (ε : F) : Type _ := TwoStep (F × F) F (dCocycle F θ ε)

end Work.Higman
