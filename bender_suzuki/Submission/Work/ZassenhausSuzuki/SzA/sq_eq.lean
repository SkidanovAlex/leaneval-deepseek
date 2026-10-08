import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Squares in the Higman group `A(K,θ)` in characteristic two

`A(K,θ)` is `K × K` with `(a,b) * (c,d) = (a+c, b+d+a·θ c)`.  In characteristic two both
coordinates of `x * x` collapse:

`x * x = ⟨x.a + x.a, x.b + x.b + x.a·θ x.a⟩ = ⟨0, x.a·θ x.a⟩`.

Consequently the square of every element lies in the centre `{(0,b)}` of `A(K,θ)` (this is
the standard "squares are central" property of Suzuki 2-groups, cf. BG Example 5.2), and
`x * x` is an involution.
-/

namespace Work.ZassenhausSuzuki.SzA

variable {K : Type*} [Field K] (θ : K ≃+* K)

/-- First coordinate of a square in `A(K,θ)`: `(x * x).a = x.a + x.a`. -/
theorem mul_self_a (x : SzA K θ) : (x * x).a = x.a + x.a := rfl

/-- Second coordinate of a square in `A(K,θ)`: `(x*x).b = x.b + x.b + x.a·θ x.a`. -/
theorem mul_self_b (x : SzA K θ) : (x * x).b = x.b + x.b + x.a * θ x.a := rfl

/-- **Squares in the Higman group.**  In characteristic two every element of `A(K,θ)`
squares to `⟨0, a·θ a⟩`: both `x.a + x.a` and `x.b + x.b` vanish. -/
theorem sq_eq {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (x : Work.ZassenhausSuzuki.SzA K θ) :
    x * x = ⟨0, x.a * θ x.a⟩ := by
  ext <;> simp [CharTwo.add_self_eq_zero]

/-- The first coordinate of a square vanishes in characteristic two. -/
theorem sq_a {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (x : SzA K θ) : (x * x).a = 0 := by
  rw [sq_eq]

/-- Every element `⟨0, b⟩` of the root group lies in the centre of `A(K,θ)`. -/
theorem mk_zero_mem_center (b : K) : (⟨0, b⟩ : SzA K θ) ∈ Subgroup.center (SzA K θ) := by
  rw [Subgroup.mem_center_iff]
  intro y
  ext <;> simp [add_comm]

/-- **Squares of `A(K,θ)` are central** (characteristic two). -/
theorem sq_mem_center {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (x : SzA K θ) : x * x ∈ Subgroup.center (SzA K θ) := by
  rw [sq_eq]
  exact mk_zero_mem_center θ _

/-- Squares of `A(K,θ)` commute with each other (characteristic two). -/
theorem sq_comm {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (x y : SzA K θ) :
    x * x * (y * y) = y * y * (x * x) :=
  ((Subgroup.mem_center_iff.mp (sq_mem_center θ x)) (y * y)).symm

/-- `x * x` is an involution in characteristic two. -/
theorem sq_inv_eq_self {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (x : SzA K θ) : (x * x)⁻¹ = x * x := by
  ext <;> simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq]

end Work.ZassenhausSuzuki.SzA
