import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_detects_gamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement

namespace Work.SSGRoute

open Work.SSGRoute.prop5

/-- The self-pair witness word of the `(4,4)` graded step: `ν(A · ⁅x⁻¹,σx⁆ · A)` with `A = x·σx`,
where `ν(w) = (σ w)⁻¹ w` is the norm. -/
noncomputable def selfPairWord (X : Type) (σ : X ≃ X) (x : X) : FreeGroup X :=
  let A : FreeGroup X := FreeGroup.of x * FreeGroup.of (σ x)
  let D : FreeGroup X := ⁅(FreeGroup.of x)⁻¹, FreeGroup.of (σ x)⁆
  (FreeGroup.freeGroupCongr σ (A * D * A))⁻¹ * (A * D * A)

/-- The double witness word `ν(g · σ g)`. -/
noncomputable def doubleWord (X : Type) (σ : X ≃ X) (g : FreeGroup X) : FreeGroup X :=
  (FreeGroup.freeGroupCongr σ (g * FreeGroup.freeGroupCongr σ g))⁻¹
    * (g * FreeGroup.freeGroupCongr σ g)

/-- The reference class of the self-pair witness: `x²σx² + σx²x²` reduced mod `2`. -/
noncomputable def selfPairClass (X : Type) (σ : X ≃ X) (x : X) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  MonoidAlgebra.single (FreeMonoid.of (σ x) * FreeMonoid.of (σ x)
      * (FreeMonoid.of x * FreeMonoid.of x)) 1
    + MonoidAlgebra.single (FreeMonoid.of x * FreeMonoid.of x
      * (FreeMonoid.of (σ x) * FreeMonoid.of (σ x))) 1

/-! ## Degree truncation of the free associative algebra

`trunc N` keeps the coefficients on words of length `< N`. -/

/-- The projection of `FreeAssoc X = ℤ[X^*]` onto the words of length `< N`. -/
noncomputable def trunc (X : Type) (N : ℕ) : FreeAssoc X →+ FreeAssoc X where
  toFun a := MonoidAlgebra.ofCoeff
    (Finsupp.filter (fun w : FreeMonoid X => w.length < N) a.coeff)
  map_zero' := by
    rw [MonoidAlgebra.coeff_zero, Finsupp.filter_zero, MonoidAlgebra.ofCoeff_zero]
  map_add' a b := by
    rw [MonoidAlgebra.coeff_add, Finsupp.filter_add, MonoidAlgebra.ofCoeff_add]

@[simp] theorem trunc_apply (X : Type) (N : ℕ) (a : FreeAssoc X) (w : FreeMonoid X) :
    (trunc X N a).coeff w = if w.length < N then a.coeff w else 0 := by
  rw [show trunc X N a = MonoidAlgebra.ofCoeff
      (Finsupp.filter (fun w : FreeMonoid X => w.length < N) a.coeff) from rfl,
    MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]

theorem trunc_trunc (X : Type) (N : ℕ) (a : FreeAssoc X) :
    trunc X N (trunc X N a) = trunc X N a := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  rw [trunc_apply, trunc_apply]
  by_cases h : w.length < N <;> simp [h]

/-- `trunc N` changes nothing on an element whose coefficients vanish on all words of
length `≥ N`. -/
theorem trunc_eq_self (X : Type) (N : ℕ) (a : FreeAssoc X)
    (h : ∀ w : FreeMonoid X, N ≤ w.length → a.coeff w = 0) : trunc X N a = a := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  rw [trunc_apply]
  by_cases hw : w.length < N
  · simp [hw]
  · rw [if_neg hw]
    exact (h w (Nat.le_of_not_lt hw)).symm

end Work.SSGRoute
