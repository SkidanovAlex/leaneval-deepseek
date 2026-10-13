/-
  WilC4/Wire : the frozen hole of area C, closed.

  `WilkiesDesign.CG.C4_valuation_inequality` (SPEC) is

      theorem C4_valuation_inequality
          (hR : ∀ n X, RExpExist X → RExpExist Xᶜ) (hOM : OMinModels) (hPB : PolyBoundedRExp) :
          ValIneq

  The route of `WilC4/Route.lean` (ULPM ⟹ Gap lemma ⟹ PreparationStep ⟹ `ValIneq`, via this
  area's rank induction `valIneq_of_preparation`) proves it with the same hypotheses, so the
  declaration below is the `…_proved` companion the lead's wiring consumes (in the style of
  `WilkiesDesign.CG.C0_rexp_syntax_proved`).  Its axiom footprint is
  `[propext, Classical.choice, Quot.sound]`.
-/
import Submission.Work.WilC4.Route
import Submission.Work.WilC4.Assembly

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign Work.WilC4

/-- **Wilkie's relativised valuation inequality for `T_r`**, i.e. the frozen
`C4_valuation_inequality`, proved. -/
theorem C4_valuation_inequality_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hOM : OMinModels) (hPB : PolyBoundedRExp) : ValIneq :=
  Work.WilC4.Route.C4_valuation_inequality_route hR hOM hPB

/-- The proved theorem has exactly the type of the frozen hole. -/
example : type_of% @C4_valuation_inequality_proved = type_of% @C4_valuation_inequality := rfl

end WilkiesDesign.CG
