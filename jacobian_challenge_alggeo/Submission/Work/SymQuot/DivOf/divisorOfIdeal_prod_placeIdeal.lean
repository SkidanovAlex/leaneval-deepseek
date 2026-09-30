import Mathlib
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_placeIdeal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_mul
import Submission.Work.SymQuot.DivOf.placeOrder_prod_placeIdeal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf
open Work.CurveBasics

theorem divisorOfIdeal_prod_placeIdeal {F : Type u} [Field F] {C : Curve F} {n : ℕ}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (y : Fin n → C.Place) (hy : ∀ m, (y m).point ∈ V) :
    divisorOfIdeal C V hV (∏ m, placeIdeal C V (y m) (hy m)) = ∑ m, Curve.Div.place (y m) := by
  ext z
  rw [divisorOfIdeal_apply]
  by_cases hz : z.point ∈ V
  · rw [dite_eq_left hz, placeOrder_prod_placeIdeal V hV y hy z hz]
    have hsum : (∑ m, Curve.Div.place (y m)) z
        = ((Finset.univ.filter (fun m => y m = z)).card : ℤ) := by
      rw [Finsupp.finsetSum_apply]
      simp only [Curve.Div.place, Finsupp.single_apply]
      rw [← Finset.sum_boole (fun m => y m = z) Finset.univ]
    rw [hsum]
  · rw [dite_eq_right hz]
    symm
    simp only [Curve.Div.place, Finsupp.finsetSum_apply, Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro m _
    rw [ite_eq_right]
    intro h
    exact hz (h ▸ hy m)

end Work.SymQuot.DivOf

open Work.CurveBasics

/-- The statement as requested at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal` (the declaration above,
which sits in the doubly opened namespace inherited from this file's original skeleton). -/
theorem divisorOfIdeal_prod_placeIdeal {F : Type u} [Field F] {C : Curve F} {n : ℕ}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (y : Fin n → C.Place) (hy : ∀ m, (y m).point ∈ V) :
    divisorOfIdeal C V hV (∏ m, placeIdeal C V (y m) (hy m)) = ∑ m, Curve.Div.place (y m) :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal V hV y hy

end Work.SymQuot.DivOf
