/-
  WilC5 — the `rexp`-reduct of a model of `TE` is a model of `TR`.

  This is the first consequence of the syntactic translation of `Translate.lean`: the restricted
  exponential is definable from the full exponential, so every model of `TE` (the theory of
  `ℝ_exp`) carries, in its `rexp`-reduct, a model of `TR` (the theory of `ℝ` with `exp` restricted
  to `[-1,1]`).  Consequently every embedding of models of `TE` restricts to an embedding of the
  `rexp`-reducts, and the model completeness of `TR` applies to it.
-/
import Submission.Work.WilC5.Translate
import Submission.Work.WilC5.RealFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## Sentences and the empty assignment -/

/-- The canonical empty-free-variable and empty-bound-variable assignments. -/
abbrev emptyVar {M : Type} : Empty → M := fun e => Empty.elim e

abbrev emptyBnd {M : Type} : Fin 0 → M := fun i => Fin.elim0 i

/-- `Sentence.Realize` is the bounded realization at the empty assignment. -/
theorem sentenceRealize_iff_bounded {L : Language} {M : Type} [L.Structure M] (φ : L.Sentence) :
    (M ⊨ φ) ↔ BoundedFormula.Realize φ (default : Empty → M) (default : Fin 0 → M) :=
  Iff.rfl

/-- For a sentence the (empty) free and bound assignments are irrelevant. -/
theorem sentence_realize_irrel {L : Language} {M : Type} (inst : L.Structure M) (φ : L.Sentence)
    (v w : Empty → M) (xs ys : Fin 0 → M) :
    @BoundedFormula.Realize L M inst Empty 0 φ v xs ↔
      @BoundedFormula.Realize L M inst Empty 0 φ w ys := by
  rw [show v = w from funext fun e => Empty.elim e,
    show xs = ys from funext fun i => Fin.elim0 i]

/-- `Sentence.Realize` is the bounded realization at the canonical empty assignment. -/
theorem sentence_realize_bounded {L : Language} {M : Type} (inst : L.Structure M)
    (φ : L.Sentence) :
    @Sentence.Realize L M inst φ ↔ @BoundedFormula.Realize L M inst Empty 0 φ emptyVar emptyBnd :=
  sentence_realize_irrel inst φ (default : Empty → M) emptyVar (default : Fin 0 → M) emptyBnd

/-- **The `rexp`-reduct of a model of `TE` is a model of `TR`.** -/
theorem reduct_model_TR (M : Type) [LEc.Structure M] (h : M ⊨ TE) :
    @Theory.Model LRc M (reductStruct M) TR := by
  letI : LRc.Structure M := reductStruct M
  rw [Theory.model_iff]
  intro σ hσ
  change σ ∈ LRc.completeTheory ℝ at hσ
  rw [mem_completeTheory] at hσ
  have hσr : @Sentence.Realize LRc ℝ (reductStruct ℝ) σ := by
    rw [reductStruct_real_eq]
    exact hσ
  have hσr' : @BoundedFormula.Realize LRc ℝ (reductStruct ℝ) Empty 0 σ emptyVar emptyBnd :=
    (sentence_realize_bounded (reductStruct ℝ) σ).mp hσr
  have hσ' : @Sentence.Realize LEc ℝ _ (formulaTrans σ) := by
    rw [sentence_realize_bounded]
    rw [formulaTrans_realize]
    exact hσr'
  have hM : @Sentence.Realize LEc M _ (formulaTrans σ) :=
    (Theory.model_iff TE).mp h (formulaTrans σ) (mem_completeTheory.mpr hσ')
  have hM0 : @BoundedFormula.Realize LEc M _ Empty 0 (formulaTrans σ) emptyVar emptyBnd :=
    (sentence_realize_bounded (inferInstance : LEc.Structure M) (formulaTrans σ)).mp hM
  have hM' : rRealizeF emptyVar emptyBnd σ := (formulaTrans_realize σ emptyVar emptyBnd).mp hM0
  rw [sentence_realize_bounded]
  exact hM'

end Work.WilC5
