/-
  WilC5 — a model of `T_r` is a field in its ring reduct.

  `TR = LRc.completeTheory ℝ` is the complete theory of the standard `LRc`-structure `ℝ`, where
  `LRc = (ring ⊕ rexpL)[[ℝ]]`.  Its models therefore satisfy every `LRc`-sentence true in `ℝ`.
  Viewing a `Language.ring`-sentence `σ` as the `LRc`-sentence `trLringHom.onSentence σ` (the
  language of rings sits inside `LRc` at `Sum.inl (Sum.inl ·)`), the fact that `ℝ` is a field
  transfers to every model of `TR`, in the `Language.ring`-reduct `lrcRingReduct M` of
  `LRcReduct.lean`.

  The main statement `tr_ring_field` says exactly that: `M ⊨ Theory.field`.  The reduction uses
  only completeness of `TR`; it is the `LRc`/`TR` analogue of `teLog_ring_field` and is the input
  that lets Mathlib's `fieldOfModelField`/`CompatibleRing` machinery (and hence the o-minimality
  and valuation theory of areas C2/C4) be applied at a structure given only as an `LRc`-structure.
-/
import Mathlib
import Submission.Work.WilC5.LRcReduct

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The language of rings inside `LRc`.**  A ring symbol sits at `Sum.inl (Sum.inl ·)`
(`lrcRingReduct` in `LRcReduct.lean`); `Language.ring` has no relation symbols. -/
def trLringHom : Language.ring →ᴸ LRc where
  onFunction := fun {_} f => Sum.inl (Sum.inl f)
  onRelation := fun {_} r => isEmptyElim r

/-- On the standard structure `ℝ` (whose ring symbols are the field operations of `ℝ`), the
inclusion of the language of rings into `LRc` is an expansion. -/
instance trLringHom_isExpansionOn_real : trLringHom.IsExpansionOn ℝ where
  map_onFunction := fun {_} _ _ => rfl
  map_onRelation := fun {_} r _ => isEmptyElim r

/-- On any `LRc`-structure `M`, the ring symbols of `LRc` (as recalled by `lrcRingReduct M`) are
exactly the interpretation of the corresponding ring symbols, so the inclusion of the language of
rings into `LRc` is an expansion. -/
instance trLringHom_isExpansionOn_model (M : Type) [LRc.Structure M] :
    trLringHom.IsExpansionOn M where
  map_onFunction := fun {_} _ _ => rfl
  map_onRelation := fun {_} r _ => isEmptyElim r

/-- **A model of `TR` is a field in its ring reduct.** -/
theorem tr_ring_field (M : Type) [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    (h : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR) :
    FirstOrder.Language.Theory.Model M FirstOrder.Language.Theory.field := by
  rw [Theory.model_iff]
  intro σ hσ
  -- The field axioms hold in `ℝ`, so `σ` (a field axiom) is true in `ℝ`.
  have hR : ℝ ⊨ σ := Theory.realize_sentence_of_mem Theory.field hσ
  -- Translating `σ` into an `LRc`-sentence along `trLringHom`, it is still true in `ℝ`.
  have hR' : ℝ ⊨ trLringHom.onSentence σ :=
    (LHom.realize_onSentence ℝ trLringHom σ).mpr hR
  -- Hence it lies in `TR = LRc.completeTheory ℝ`, and so holds in `M`.
  have hmem : trLringHom.onSentence σ ∈ TR := mem_completeTheory.mpr hR'
  have hM' : M ⊨ trLringHom.onSentence σ := h.realize_of_mem _ hmem
  -- Translating back, `σ` holds in the ring reduct of `M`.
  exact (LHom.realize_onSentence M trLringHom σ).mp hM'

end Work.WilC5
