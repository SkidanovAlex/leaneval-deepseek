/-
  WilC4/TR_hyper : the hyperreal model is a model of `TR = Th(ℝ_rexp, ℝ)`.

  Sentences of `TR` are true in `ℝ` by definition of the complete theory, and Łoś's theorem
  (`Work.WilC4.realize_hyper`, the germ model's transfer) moves them to `HR`.  The only
  bookkeeping is that `Sentence.Realize` evaluates a sentence at the (unique) empty assignment,
  whereas Łoś is phrased for an arbitrary one; `Empty → M` being a subsingleton, any two
  assignments give equivalent `Realize`s.
-/
import Mathlib
import Submission.Work.WilC4.HyperRealCompat
import Submission.Work.WilC4.realize_hyper

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-- Łoś's theorem for sentences of `LRc`, in the hyperreal model. -/
theorem sentence_realize_hyper (σ : LRc.Sentence) :
    (@Sentence.Realize LRc HR instLRcHR σ) ↔
      (@Sentence.Realize LRc ℝ inferInstance σ) := by
  have hindepHR : ∀ v v' : Empty → HR,
      @Formula.Realize LRc HR instLRcHR Empty σ v ↔
        @Formula.Realize LRc HR instLRcHR Empty σ v' := by
    intro v v'
    rw [show v = v' from funext fun i => isEmptyElim i]
  have hindepR : ∀ v v' : Empty → ℝ,
      @Formula.Realize LRc ℝ inferInstance Empty σ v ↔
        @Formula.Realize LRc ℝ inferInstance Empty σ v' := by
    intro v v'
    rw [show v = v' from funext fun i => isEmptyElim i]
  have key := realize_hyper (φ := σ) (x := (fun _ : Empty => (0 : ℕ → ℝ)))
  have hR : (∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ),
        @Formula.Realize LRc ℝ inferInstance Empty σ (fun i : Empty => (0 : ℕ → ℝ) a)) ↔
      @Formula.Realize LRc ℝ inferInstance Empty σ (fun _ : Empty => (0 : ℝ)) := by
    refine (Filter.eventually_congr ?_).trans Filter.eventually_const
    filter_upwards with a
    exact hindepR (fun i : Empty => (0 : ℕ → ℝ) a) (fun _ : Empty => (0 : ℝ))
  rw [hR] at key
  exact (hindepHR _ _).trans (key.trans (hindepR _ _))

/-- The hyperreal model realises every sentence of `TR`. -/
theorem TR_hyper : @Theory.Model LRc HR instLRcHR WilkiesDesign.CG.TR :=
  Theory.Model.mk fun σ hσ => (sentence_realize_hyper σ).mpr hσ

end Work.WilC4
