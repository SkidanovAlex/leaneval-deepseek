import Mathlib
import Submission.Work.Pi6.SQM.SqOneDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The pointwise identity `(x ∪₁ x)(σ) ≡ (δx̃)(σ) / 2`

For a mod-2 `2`-cochain `x` with `0/1` lift `x̃ = liftZ X 2 x`, the value on a `3`-simplex `σ` of
the half-coboundary cochain `deltaHalf X x` of `SqOneDefs`, reduced mod `2`, is the value of the
mod-2 cup-1 square `x ∪₁ x = Sq¹ x` at `σ`.

Both sides are explicit in the four values `x(σ|δᵢ)` (`i = 0,1,2,3`): the left is
`x̃(δ₀σ) x̃(δ₂σ) - x̃(δ₃σ) x̃(δ₁σ)`, whose reduction mod `2` is `x(δ₀σ)x(δ₂σ) + x(δ₃σ)x(δ₁σ)`, and
the right is `x(δ₃σ)x(δ₁σ) - x(δ₀σ)x(δ₂σ)` by Steenrod's interval formula for the library's `cup1`
(`genEval_cup1`), the face identifications `Fface 2 2 0 = δ₃`, `Gface 2 2 0 = δ₁`,
`Fface 2 2 1 = δ₀`, `Gface 2 2 1 = δ₂` and `- = +` in `𝔽₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff Fface Gface genEval_cup1)

/-- Elimination of a cast along a self-equality of natural numbers. -/
theorem cast_self {α : ℕ → Type} {a : ℕ} (h : a = a) (y : α a) : h ▸ y = y := by
  cases h; rfl

/-- The front face of `Fface 2 2 0` is the face `δ 3` (dropping the last vertex). -/
theorem Fface_2_2_0 : Fface 2 2 0 (by omega) = SimplexCategory.δ (3 : Fin 4) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  fin_cases i <;> simp [Work.Cohomology.Fface_val, SimplexCategory.coe_δ,
    Work.Cohomology.succAbove_val_if']

/-- The back face of `Gface 2 2 0` is the face `δ 1`. -/
theorem Gface_2_2_0 : Gface 2 2 0 (by omega) = SimplexCategory.δ (1 : Fin 4) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  fin_cases i <;> simp [Work.Cohomology.Gface_apply, Work.Cohomology.Gfun_val_if,
    SimplexCategory.coe_δ, Work.Cohomology.succAbove_val_if']

/-- The front face of `Fface 2 2 1` is the face `δ 0`. -/
theorem Fface_2_2_1 : Fface 2 2 1 (by omega) = SimplexCategory.δ (0 : Fin 4) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  fin_cases i <;> simp [Work.Cohomology.Fface_val, SimplexCategory.coe_δ]

/-- The back face of `Gface 2 2 1` is the face `δ 2`. -/
theorem Gface_2_2_1 : Gface 2 2 1 (by omega) = SimplexCategory.δ (2 : Fin 4) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  fin_cases i <;> simp [Work.Cohomology.Gface_apply, Work.Cohomology.Gfun_val_if,
    SimplexCategory.coe_δ, Work.Cohomology.succAbove_val_if']

/-- `cup1m` in bidegree `(2,2)` is the library's `cup1` (the degree cast is along an equality of
equal numbers). -/
theorem cup1m_two_eq (X : SSet) (x : Cochain F2 X 2) :
    Work.Pi6.SQ.cup1m X 2 2 x x = Work.Cohomology.cup1 F2 X 2 2 x x := by
  rw [Work.Pi6.SQ.cup1m]

/-- **The value of the cup-1 square on a `3`-simplex.** -/
theorem genEval_cup1m_two (X : SSet) (x : Cochain F2 X 2) (σ : X _⦋3⦌) :
    genEval F2 X (Work.Pi6.SQ.cup1m X 2 2 x x) σ
      = genEval F2 X x (X.δ (3 : Fin 4) σ) * genEval F2 X x (X.δ (1 : Fin 4) σ)
        - genEval F2 X x (X.δ (0 : Fin 4) σ) * genEval F2 X x (X.δ (2 : Fin 4) σ) := by
  rw [cup1m_two_eq, Work.Cohomology.genEval_cup1]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, zero_mul, Nat.reduceMul, Nat.reduceAdd]
  rw [show X.map (Fface 2 2 0 (by omega)).op σ = X.δ (3 : Fin 4) σ from by
    rw [SimplicialObject.δ_def, Fface_2_2_0]]
  rw [show X.map (Gface 2 2 0 (by omega)).op σ = X.δ (1 : Fin 4) σ from by
    rw [SimplicialObject.δ_def, Gface_2_2_0]]
  rw [show X.map (Fface 2 2 1 (by omega)).op σ = X.δ (0 : Fin 4) σ from by
    rw [SimplicialObject.δ_def, Fface_2_2_1]]
  rw [show X.map (Gface 2 2 1 (by omega)).op σ = X.δ (2 : Fin 4) σ from by
    rw [SimplicialObject.δ_def, Gface_2_2_1]]
  ring_nf

/-- **The pointwise identity `(x ∪₁ x)(σ) ≡ (δx̃)(σ)/2`.** -/
theorem pointwiseSqOne (X : SSet) (x : Cochain F2 X 2) (σ : X _⦋3⦌) :
    ((genEval ℤ X (deltaHalf X x) σ : ℤ) : F2)
      = genEval F2 X (Work.Pi6.SQ.cup1m X 2 2 x x) σ := by
  rw [genEval_deltaHalf, genEval_liftZ, genEval_liftZ, genEval_liftZ, genEval_liftZ]
  rw [genEval_cup1m_two]
  simp only [Int.cast_sub, Int.cast_mul]
  rw [Work.Pi6.SQM.intCast_valZ, Work.Pi6.SQM.intCast_valZ, Work.Pi6.SQM.intCast_valZ,
    Work.Pi6.SQM.intCast_valZ]
  simp only [CharTwo.sub_eq_add]
  ring

end

end Work.Pi6.SQM
