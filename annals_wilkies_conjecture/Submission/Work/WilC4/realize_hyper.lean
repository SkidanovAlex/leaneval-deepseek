/-
  WilC4/realize_hyper : Łoś's theorem for `LRc`-formulas in the hyperreal model `HR`.

  This is the `n = 0` case of `Work.WilC4.realize_bd_hyper`: a formula is a bounded formula
  with no bound variables, so `BoundedFormula.Realize` with the (unique) empty valuation is
  the `Formula.Realize` of the formula.
-/
import Mathlib
import Submission.Work.WilC4.HyperRealSetup
import Submission.Work.WilC4.realize_bd_hyper

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

theorem realize_hyper {β : Type*} (φ : WilkiesDesign.CG.LRc.Formula β) (x : β → ℕ → ℝ) :
    (@FirstOrder.Language.Formula.Realize WilkiesDesign.CG.LRc Work.WilC4.HR Work.WilC4.instLRcHR β φ
        (fun i => (↑(x i) : Work.WilC4.HR))) ↔
      ∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ),
        @FirstOrder.Language.Formula.Realize WilkiesDesign.CG.LRc ℝ inferInstance β φ
          (fun i => x i a) := by
  have h := realize_bd_hyper (β := β) (n := 0) φ x (fun _ : Fin 0 => (0 : ℕ → ℝ))
  have h1 : (@BoundedFormula.Realize LRc HR instLRcHR β 0 φ (fun i => (↑(x i) : HR))
      (fun _ : Fin 0 => (↑(0 : ℕ → ℝ) : HR))) ↔
      (@Formula.Realize LRc HR instLRcHR β φ (fun i => (↑(x i) : HR))) :=
    Formula.boundedFormula_realize_eq_realize φ _ _
  have h2 : (∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ),
        @BoundedFormula.Realize LRc ℝ inferInstance β 0 φ (fun i => x i a)
          (fun _ : Fin 0 => (0 : ℝ))) ↔
      (∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ),
        @Formula.Realize LRc ℝ inferInstance β φ (fun i => x i a)) := by
    refine Filter.eventually_congr ?_
    filter_upwards with a
    exact Formula.boundedFormula_realize_eq_realize φ _ _
  exact h1.symm.trans (h.trans h2)

end Work.WilC4
