import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.cupLeibniz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The unit for the Alexander–Whitney cup product

The `0`-cochain `unitCochain R X` (the augmentation, which is `1` on every `0`-simplex) is a two-sided
unit for the Alexander–Whitney cup product on the singular cochains of a simplicial set:

`unitCochain ⌣ α = α`  and  `α ⌣ unitCochain = α`.

Here the first identity is stated through the index transport `Nat.zero_add n : 0 + n = n`, since the
cup product of a degree `0` and a degree `n` cochain lives in degree `0 + n`.

The proof is the standard one: since `cup` is a linear functional on the `(n+m)`-chains which is
determined by its values on generators (the singular simplices), it suffices to compare both sides on
generators.  On a simplex `σ` the definition of `cup` gives
`(unit ⌣ α)(σ) = unit(σ_front) · α(σ_back) = 1 · α(σ_back)`, and `σ_back` is `σ` itself because the
"last `n` vertices" of an `n`-simplex are all of them; symmetrically for `α ⌣ unit`, where `σ_front`
is `σ`.  These two facts about the front/back faces of simplices are the content of the elementary
lemmas below.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The inclusion of the first `n+1` vertices of an `(n+0)`-simplex is the identity. -/
lemma frontIncl_self (n : ℕ) (h : n ≤ n + 0) : frontIncl n (n + 0) h = 𝟙 ⦋n⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  apply Fin.ext
  simp only [hom_frontIncl_val, CategoryTheory.id_apply]
  first | rfl | (erw [hom_frontIncl_val]) | simp [frontIncl]

/-- The front `n`-face of an `(n+0)`-simplex is the simplex itself. -/
lemma frontFace_self (X : SSet) (n : ℕ) (h : n ≤ n + 0) (σ : X _⦋n + 0⦌) :
    frontFace X n (n + 0) h σ = σ := by
  simp only [frontFace, frontIncl_self n h, CategoryTheory.op_id]
  simp

/-- The inclusion of the last `n+1` vertices of an `(n+0)`-simplex, followed by the index
identification `⦋0+n⦌ ≅ ⦋n⦌`, is the identity. -/
lemma backIncl_zero_comp (n : ℕ) :
    backIncl 0 n ≫ eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n)) = 𝟙 ⦋n⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, hom_backIncl_val, coe_eqToHom_mk (Nat.zero_add n),
    CategoryTheory.id_apply]
  exact Nat.zero_add k.val

/-- Evaluating a cochain transported along an index identification at a generator: the generator is
transported the other way. -/
lemma genEval_cast' (X : SSet) {a b : ℕ} (h : a = b)
    (f : (X.chainComplex (ModuleCat.of R R)).X a →ₗ[R] R) (y : X _⦋b⦌) :
    genEval R X (h ▸ f) y
      = genEval R X f (X.map (eqToHom (congrArg SimplexCategory.mk h)).op y) := by
  cases h
  simp [genEval]

/-- The cup product with the unit `0`-cochain on the left, evaluated at a generator:
`(unit ⌣ α)(σ) = α(σ_back)`. -/
lemma cup_unitCochain_left_apply (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) (σ : X _⦋0+n⦌) :
    genEval R X (cup R X (unitCochain R X) α) σ = genEval R X α (backFace X 0 n σ) := by
  rw [cup_apply', genEval_unitCochain, one_mul]

/-- The cup product with the unit `0`-cochain on the right, evaluated at a generator:
`(α ⌣ unit)(σ) = α(σ_front)`. -/
lemma cup_unitCochain_right_apply (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) (σ : X _⦋n+0⦌) :
    genEval R X (cup R X α (unitCochain R X)) σ
      = genEval R X α (frontFace X n (n+0) (by omega) σ) := by
  rw [cup_apply', genEval_unitCochain, mul_one]

/-- The back `n`-face of a simplex which has been transported from degree `n` to degree `0+n` is the
original simplex: the back face of an `(n+0)`-simplex is everything. -/
lemma backFace_zero_cast (X : SSet) (n : ℕ) (σ : X _⦋n⦌) :
    backFace X 0 n (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n))).op σ) = σ := by
  simp only [backFace]
  rw [map_op_comp, backIncl_zero_comp]
  simp

theorem cupUnit (R : Type) [CommRing R] (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) :
    (Nat.zero_add n ▸ Work.Cohomology.cup R X (Work.Cohomology.unitCochain R X) α) = α ∧
      Work.Cohomology.cup R X α (Work.Cohomology.unitCochain R X) = α := by
  constructor
  · apply genEval_ext
    intro σ
    rw [genEval_cast', cup_unitCochain_left_apply, backFace_zero_cast]
  · apply genEval_ext
    intro σ
    rw [cup_unitCochain_right_apply]
    rw [frontFace_self]

end

end Work.Cohomology
