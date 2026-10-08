import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coordinate bookkeeping for the terminal computation (HB III XI 11.13–11.14)

The elementary `A(K,θ)`-computations used by `tits_of_normalised` (the terminal step of
`suzukiTitsOfFix`): the images of the basic elements under the torus `h_λ`, in the
normalisation `e g = ⟨1,1⟩` (so `e (g²) = ⟨0,1⟩` and `e (g⁻¹) = ⟨1,0⟩`).

The two nontrivial `h_λ`-computations on the generic representatives `Xrep θ ν` are proved in
`Work.ZassenhausSuzuki.TitsCoordIdentities`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

variable {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)

/-- `(⟨1,1⟩ : A(K,θ))⁻¹ = ⟨1,0⟩` (characteristic two). -/
theorem inv_one_one : (⟨1, 1⟩ : SzA K θ)⁻¹ = ⟨1, 0⟩ := by
  ext <;> simp [SzA.inv_a, SzA.inv_b, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

/-- `⟨1,1⟩ * ⟨1,0⟩ = 1` in `A(K,θ)`. -/
theorem one_one_mul_one_zero : (⟨1, 1⟩ : SzA K θ) * ⟨1, 0⟩ = 1 := by
  ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]

/-- `⟨a,0⟩ * ⟨0,1⟩ = ⟨a,1⟩` in `A(K,θ)`. -/
theorem mk_mul_mk_zero_one (a : K) :
    (⟨a, 0⟩ : SzA K θ) * ⟨0, 1⟩ = (⟨a, 1⟩ : SzA K θ) := by
  ext <;> simp [SzA.mul_a, SzA.mul_b]

/-- `⟨0,s⟩ * ⟨1,1⟩ = ⟨1,1+s⟩` in `A(K,θ)` (characteristic two). -/
theorem zero_one_mul_one_one (s : K) :
    (⟨0, s⟩ : SzA K θ) * ⟨1, 1⟩ = (⟨1, 1 + s⟩ : SzA K θ) := by
  ext <;> simp [SzA.mul_a, SzA.mul_b, add_comm]

/-- `h_λ ⟨1,1⟩ = ⟨λ, λθλ⟩`. -/
theorem hLam_one_one (lam : K) :
    SzA.hLam θ lam (⟨1, 1⟩ : SzA K θ) = ⟨lam, lam * θ lam⟩ := by
  ext <;> simp [SzA.hLam]

/-- `⟨1,1⟩ ^ 2 = ⟨0,1⟩` in `A(K,θ)` (characteristic two): `⟨1,1⟩ = g` and `⟨0,1⟩ = g²`. -/
theorem one_one_sq : (⟨1, 1⟩ : SzA K θ) ^ 2 = (⟨0, 1⟩ : SzA K θ) := by
  rw [pow_two]
  ext <;> simp [SzA.mul_a, SzA.mul_b, CharTwo.add_self_eq_zero, map_one]

/-- `⟨0,1⟩ ^ 2 = 1` in `A(K,θ)`. -/
theorem zero_one_sq : (⟨0, 1⟩ : SzA K θ) ^ 2 = 1 := by
  rw [pow_two]
  ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]

/-- `a + b + b = a` in characteristic two. -/
theorem add_add_self (a b : K) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

end Work.ZassenhausSuzuki
