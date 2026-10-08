import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.isSuzukiTwoGroup_of_mulEquiv
import Submission.Work.Higman.AType_isSuzukiTwoGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `A(n,θ)` is a Suzuki 2-group (Higman 1963, §4)

Higman's group `A(K,θ)` of this area is the two-step model `Work.Higman.AType K θ` in
characteristic two (the identity of coordinates); hence, whenever `θ ≠ 1` has odd order,
`A(n,θ)` is a Suzuki 2-group in the sense of `Submission.Blueprint.IsSuzukiTwoGroup`
(`Work.Higman.AType_isSuzukiTwoGroup`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki.SzA

variable {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)

/-- In characteristic two, the identity of coordinates is an isomorphism from this area's
Higman group `A(K,θ)` to the two-step model `Work.Higman.AType K θ`. -/
def equivAType : SzA K θ ≃* Work.Higman.AType K θ where
  toFun x := ⟨x.a, x.b⟩
  invFun y := ⟨y.fst, y.snd⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl
  map_mul' x y := by
    apply Work.Higman.TwoStep.ext_iff
    · rw [Work.Higman.TwoStep.fst_mul, mul_a]
    · rw [Work.Higman.TwoStep.snd_mul, mul_b]
      rfl

theorem isSuzukiTwoGroup {n : ℕ} (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ1 : θ ≠ 1)
    (hodd : Odd (orderOf θ)) :
    IsSuzukiTwoGroup (SzA (GaloisField 2 n) θ) :=
  isSuzukiTwoGroup_of_mulEquiv (equivAType θ)
    (Work.Higman.AType_isSuzukiTwoGroup n θ hθ1 hodd)

end Work.ZassenhausSuzuki.SzA
