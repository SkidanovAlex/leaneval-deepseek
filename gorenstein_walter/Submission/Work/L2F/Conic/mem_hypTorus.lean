import Mathlib
import Submission.Work.L2F.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Conic

/-! ## Membership in the "non-split torus" `hypTorus F d`

The set `hypTorusSet F d = {!![a, d*b; b, a] | a² - d b² = 1}` is a subgroup of `SL(2,F)`:

* `1 = !![1, 0; 0, 1]` is the pair `(a,b) = (1,0)`;
* the inverse of `!![a, d*b; b, a]` is `!![a, -d*b; -b, a]` (i.e. `(a,b) ↦ (a,-b)`), since
  `a² - d b² = 1` makes the adjugate the inverse;
* the product is given by `(a,b) * (c,e) = (ac + d·be, ae + bc)`, and
  `(ac+d·be)² - d(ae+bc)² = (a²-db²)(c²-de²) = 1`.

Hence the closure `hypTorus F d` is the set itself, which is the statement below.
-/

variable {F : Type*} [Field F]

/-- The product of two matrices `!![a, d*b; b, a]`, `!![c, d*e; e, c]` is again of this form. -/
private lemma hypMat_mul (d a b c e : F) :
    (!![a, d * b; b, a] : Matrix (Fin 2) (Fin 2) F) * !![c, d * e; e, c]
      = !![a * c + d * (b * e), d * (a * e + b * c); a * e + b * c, a * c + d * (b * e)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring

/-- The adjugate of `!![a, d*b; b, a]` is `!![a, -d*b; -b, a]`.  As `det = 1`, this is also its
inverse. -/
private lemma hypMat_adjugate (d a b : F) :
    (!![a, d * b; b, a] : Matrix (Fin 2) (Fin 2) F).adjugate = !![a, d * (-b); -b, a] := by
  rw [Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_neg]

/-- `det !![a, d*b; b, a] = a² - d b²`, so it is `1` when `a² - d b² = 1`. -/
lemma hypMat_det (d a b : F) (h : a ^ 2 - d * b ^ 2 = 1) :
    (!![a, d * b; b, a] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_fin_two_of, ← h]
  ring

/-- `hypTorusSet F d` is a subgroup of `SL(2,F)`: it contains `1 = !![1,0;0,1]` (the pair
`(a,b) = (1,0)`), and is closed under multiplication and under inverses by the formulas above. -/
def hypTorusSubgroup (F : Type*) [Field F] (d : F) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  { carrier := Work.L2F.hypTorusSet F d
    mul_mem' := by
      rintro y z ⟨a, b, ha, hm⟩ ⟨c, e, hc, hm'⟩
      refine ⟨a * c + d * (b * e), a * e + b * c, ?_, ?_⟩
      · calc (a * c + d * (b * e)) ^ 2 - d * (a * e + b * c) ^ 2
            = (a ^ 2 - d * b ^ 2) * (c ^ 2 - d * e ^ 2) := by ring
          _ = 1 := by rw [ha, hc, mul_one]
      · rw [Matrix.SpecialLinearGroup.coe_mul, hm, hm', hypMat_mul d a b c e]
    one_mem' := by
      refine ⟨1, 0, by ring, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    inv_mem' := by
      rintro y ⟨a, b, ha, hm⟩
      refine ⟨a, -b, ?_, ?_⟩
      · calc a ^ 2 - d * (-b) ^ 2 = a ^ 2 - d * b ^ 2 := by ring
          _ = 1 := ha
      · rw [Matrix.SpecialLinearGroup.coe_inv, hm, hypMat_adjugate d a b] }

/-- The closure defining `hypTorus F d` adds nothing to `hypTorusSet F d`. -/
theorem hypTorus_eq_hypTorusSubgroup (F : Type*) [Field F] (d : F) :
    Work.L2F.hypTorus F d = hypTorusSubgroup F d := by
  show Subgroup.closure (Work.L2F.hypTorusSet F d) = hypTorusSubgroup F d
  exact Subgroup.closure_eq (hypTorusSubgroup F d)

/-- Membership in `hypTorus F d` (the closure of the set of matrices `!![a, d*b; b, a]` with
`a² - d*b² = 1`): exactly those matrices.  The set is a subgroup — `1` is `(a,b) = (1,0)`;
`(a,b)⁻¹ = (a,-b)`; and `(a,b)*(c,e) = (ac + d*be, ae + bc)` with
`(ac+d*be)² - d(ae+bc)² = (a²-db²)(c²-de²) = 1` — so the closure is the set itself. -/
theorem mem_hypTorus (F : Type*) [Field F] (d : F) (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Work.L2F.hypTorus F d ↔
      ∃ a b : F, a ^ 2 - d * b ^ 2 = 1 ∧
        (x : Matrix (Fin 2) (Fin 2) F) = !![a, d * b; b, a] := by
  rw [hypTorus_eq_hypTorusSubgroup F d]
  exact Iff.rfl

end Work.L2F.Conic
