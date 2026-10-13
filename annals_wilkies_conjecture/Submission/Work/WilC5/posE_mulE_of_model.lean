import Mathlib
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.ReductEmb

namespace Work.WilC5

open WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

set_option maxHeartbeats 1000000

/-!
  The product of two positive elements of a model of `TE = Th(ℝ_exp)` is positive, where
  positivity is the definable order `0 < x  :⟺  leE zeroE x ∧ ¬ leE x zeroE`.

  This is a special case of "the definable order of a model of `TE` is a field order".  The
  statement is first-order, holds in `ℝ`, and hence — since `TE` is the complete theory of
  `ℝ` — transfers to every model by elementarity (`transfer` in `ReductEmb.lean`).
-/

/-- The `LEc`-sentence `0 < x ∧ 0 < y → 0 < x * y`, where `0 < t` is the definable order
`leE zeroE t ∧ ¬ leE t zeroE`, i.e. `isSquare (t - 0) ∧ ¬ isSquare (0 - t)`. -/
def posMulFormula : LEc.BoundedFormula Empty 2 :=
  ((leForm eZero (v2 0) ⊓ (leForm (v2 0) eZero).not) ⊓
   (leForm eZero (v2 1) ⊓ (leForm (v2 1) eZero).not)).imp
    (leForm eZero (eMul (v2 0) (v2 1)) ⊓ (leForm (eMul (v2 0) (v2 1)) eZero).not)

/-- Realization of `posMulFormula`: it says exactly that `mulE x y` satisfies the definable
positivity predicate whenever `x` and `y` do. -/
theorem posMulFormula_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    posMulFormula.Realize (emptyVar : Empty → M) xs ↔
      ((isSquare (subE (xs 0) zeroE) ∧ ¬ isSquare (subE zeroE (xs 0))) ∧
       (isSquare (subE (xs 1) zeroE) ∧ ¬ isSquare (subE zeroE (xs 1)))) →
      (isSquare (subE (mulE (xs 0) (xs 1)) zeroE) ∧
       ¬ isSquare (subE zeroE (mulE (xs 0) (xs 1)))) := by
  unfold posMulFormula
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    leForm_realize, v2, Term.realize_var, Sum.elim_inr, realize_eZero, realize_eMul]

/-- `posMulFormula` holds in `ℝ`: the product of two strictly positive reals is strictly
positive. -/
theorem posMul_real : ∀ xs : Fin 2 → ℝ, posMulFormula.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [posMulFormula_realize]
  simp only [subE_real, zeroE_real, mulE_real, isSquare_real]
  intro h
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := h
  have hxpos : 0 < xs 0 := by linarith
  have hypos : 0 < xs 1 := by linarith
  have hxy : 0 < xs 0 * xs 1 := mul_pos hxpos hypos
  exact ⟨by linarith, by linarith⟩

theorem posE_mulE_of_model {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {x y : M}
    (hx : Work.WilC5.leE Work.WilC5.zeroE x ∧ ¬ Work.WilC5.leE x Work.WilC5.zeroE)
    (hy : Work.WilC5.leE Work.WilC5.zeroE y ∧ ¬ Work.WilC5.leE y Work.WilC5.zeroE) :
    Work.WilC5.leE Work.WilC5.zeroE (Work.WilC5.mulE x y) ∧
      ¬ Work.WilC5.leE (Work.WilC5.mulE x y) Work.WilC5.zeroE := by
  have h := transfer hM posMulFormula posMul_real ![x, y]
  rw [posMulFormula_realize] at h
  exact h ⟨⟨hx.1, hx.2⟩, hy.1, hy.2⟩

end Work.WilC5
