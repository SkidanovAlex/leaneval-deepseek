/-
# Witt's theorem: the evaluation maps and the coefficient functional

* `monLie X : Magma X → FreeLieAlgebra ℤ X` : the Lie-bracket evaluation of a tree;
* `monBrkA X : Magma X → FreeAlgebra ℤ X` : the commutator evaluation in the free associative
  algebra;
* `monBrk X : Magma X → MonoidAlgebra ℤ (FreeMonoid X)` : the commutator evaluation in the free
  monoid algebra, i.e. `monBrkA` transported across `FreeAlgebra.equivMonoidAlgebraFreeMonoid`;
* `coeffF` : the coefficient of a word in an element of `MonoidAlgebra ℤ (FreeMonoid X)`.

The point of the last two is that the coefficients of the *words* in `monBrk c` for a Hall tree
`c` are accessible; the leading one is `foliage c` (with coefficient `1`).
-/
import Mathlib
import Submission.Work.SSGRoute.prop5.witt.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.SSGRoute.prop5

universe u

variable {X : Type u}

/-- **Lie evaluation**: generators to the corresponding generator of the free Lie algebra,
products to Lie brackets. -/
def monLie (X : Type u) : Magma X → FreeLieAlgebra ℤ X
  | .gen x => FreeLieAlgebra.of ℤ x
  | .mul a b => ⁅monLie X a, monLie X b⁆

@[simp] theorem monLie_gen (x : X) : monLie X (Magma.gen x) = FreeLieAlgebra.of ℤ x := rfl

@[simp] theorem monLie_mul (a b : Magma X) :
    monLie X (Magma.mul a b) = ⁅monLie X a, monLie X b⁆ := rfl

/-- **Commutator evaluation** in the free associative algebra. -/
def monBrkA (X : Type u) : Magma X → FreeAlgebra ℤ X
  | .gen x => FreeAlgebra.ι ℤ x
  | .mul a b => monBrkA X a * monBrkA X b - monBrkA X b * monBrkA X a

@[simp] theorem monBrkA_gen (x : X) : monBrkA X (Magma.gen x) = FreeAlgebra.ι ℤ x := rfl

@[simp] theorem monBrkA_mul (a b : Magma X) :
    monBrkA X (Magma.mul a b) = monBrkA X a * monBrkA X b - monBrkA X b * monBrkA X a := rfl

/-- **Commutator evaluation** in the free monoid algebra `ℤ[FreeMonoid X]`. -/
def monBrk (X : Type u) : Magma X → MonoidAlgebra ℤ (FreeMonoid X)
  | .gen x => MonoidAlgebra.single (FreeMonoid.of x) 1
  | .mul a b => monBrk X a * monBrk X b - monBrk X b * monBrk X a

@[simp] theorem monBrk_gen (x : X) :
    monBrk X (Magma.gen x) = MonoidAlgebra.single (FreeMonoid.of x) 1 := rfl

@[simp] theorem monBrk_mul (a b : Magma X) :
    monBrk X (Magma.mul a b) = monBrk X a * monBrk X b - monBrk X b * monBrk X a := rfl

/-- The two commutator evaluations agree under the algebra isomorphism
`FreeAlgebra ℤ X ≃ ℤ[FreeMonoid X]`. -/
theorem equivMonoidAlgebra_monBrkA (w : Magma X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (monBrkA X w) = monBrk X w := by
  induction w with
  | gen x =>
      rw [monBrkA_gen, monBrk_gen, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
      simp
  | mul a b iha ihb =>
      rw [monBrkA_mul, monBrk_mul, map_sub, map_mul, map_mul, iha, ihb]

/-- The coefficient of a word in an element of `ℤ[FreeMonoid X]`. -/
def coeffF (a : MonoidAlgebra ℤ (FreeMonoid X)) (w : List X) : ℤ :=
  a.coeff (FreeMonoid.ofList w)

@[simp] theorem coeffF_add (a b : MonoidAlgebra ℤ (FreeMonoid X)) (w : List X) :
    coeffF (a + b) w = coeffF a w + coeffF b w := by
  simp [coeffF]

@[simp] theorem coeffF_neg (a : MonoidAlgebra ℤ (FreeMonoid X)) (w : List X) :
    coeffF (-a) w = -coeffF a w := by
  simp [coeffF]

@[simp] theorem coeffF_sub (a b : MonoidAlgebra ℤ (FreeMonoid X)) (w : List X) :
    coeffF (a - b) w = coeffF a w - coeffF b w := by
  simp [coeffF]

end Work.SSGRoute.prop5
