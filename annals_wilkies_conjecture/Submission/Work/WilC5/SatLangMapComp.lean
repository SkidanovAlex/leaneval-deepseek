import Mathlib
import Submission.Work.WilC5.SatSetup

open FirstOrder Language
open scoped FirstOrder

namespace Work.WilC5

/-- `SatLangMap` is functorial in the map on the constant sets: composing the maps induced by
`f : C → C'` and `g : C' → C''` is the map induced by `g ∘ f`. -/
private theorem SatLangMap_comp_aux {L : FirstOrder.Language.{0, 0}} {C C' C'' : Type}
    (f : C → C') (g : C' → C'') :
    (SatLangMap (L := L) g).comp (SatLangMap (L := L) f) = SatLangMap (L := L) (g ∘ f) := by
  ext n x
  · cases x with
    | inl a => rfl
    | inr b =>
        cases n with
        | zero => rfl
        | succ n => cases b
  · cases x <;> rfl

theorem SatLangMapComp {L : FirstOrder.Language.{0, 0}} {C C' C'' : Type} (f : C → C')
    (g : C' → C'') (τ : (SatLang L C).Sentence) :
    (SatLangMap g).onSentence ((SatLangMap f).onSentence τ)
      = (SatLangMap (L := L) (g ∘ f)).onSentence τ := by
  have h := congrFun (LHom.comp_onBoundedFormula (α := Empty) (n := 0)
    (φ := SatLangMap (L := L) g) (ψ := SatLangMap (L := L) f)) τ
  simp only [Function.comp_apply] at h
  simp only [LHom.onSentence, LHom.onFormula]
  rw [← h, SatLangMap_comp_aux]

end Work.WilC5
