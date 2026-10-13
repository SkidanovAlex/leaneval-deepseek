/-
  WilC5 — `SatExpansionModel`: the expansion of a model corresponds to the language map.

  Given an `L[[C]]`-structure `N` which is a model of a theory `T`, an injective map
  `inc : C → C'` on the constant sets and arbitrary prescribed values `w : C' → N` for the
  new constants, any sentence `σ` in the image of `T` under the induced language map
  `SatLangMap inc` holds in the expansion `SatExpansion inc hinc N w` of `N`.

  The mathematical content is the statement that `SatLangMap inc` is an *expansion* of the
  `L[[C]]`-structure `N` to the `L[[C']]`-structure `SatExpansion inc hinc N w`: the old
  constants keep their values (`SatExpansion_old`) and the `L`-part is unchanged, so realizing
  a formula after applying the language map is the same as realizing it in `N`
  (`LHom.realize_onSentence`).
-/
import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatExpand

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

/-- The value in the expansion of a constant symbol of `L[[C']]`. -/
theorem SatExpansion_funMap_const {L : FirstOrder.Language.{0, 0}} {C C' : Type} (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) (instN : (SatLang L C).Structure N) (w : C' → N)
    (c' : C') (x : Fin 0 → N) :
    @Structure.funMap (SatLang L C') N (@SatExpansion L C C' inc hinc N instN w) 0
      (Sum.inr c') x = @SatExpVal L C C' inc hinc N instN w c' := rfl

/-- `SatConVal` is the value of the corresponding constant symbol, for any argument of the empty
tuple type. -/
theorem SatConVal_funMap {L : FirstOrder.Language.{0, 0}} {C : Type} (N : Type)
    (instN : (SatLang L C).Structure N) (c : C) (x : Fin 0 → N) :
    @SatConVal L C N instN c = @Structure.funMap (SatLang L C) N instN 0 (Sum.inr c) x := by
  rw [show @SatConVal L C N instN c
      = @Structure.funMap (SatLang L C) N instN 0 (Sum.inr c) default from rfl]
  rw [show (default : Fin 0 → N) = x from funext fun i => i.elim0]

/-- `LHom.constantsOnMap` on a constant symbol, at arity zero. -/
theorem constantsOnMap_onFunction_zero {C C' : Type} (inc : C → C')
    (c : (constantsOn C).Functions 0) :
    (LHom.constantsOnMap inc).onFunction c = (inc c : (constantsOn C').Functions 0) := rfl

/-- The language map `SatLangMap inc` is an expansion of the `L[[C]]`-structure `N` to the
`L[[C']]`-structure `SatExpansion inc hinc N w`. -/
theorem SatExpansion_isExpansionOn {L : FirstOrder.Language.{0, 0}} {C C' : Type} (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) (instN : (SatLang L C).Structure N) (w : C' → N) :
    @FirstOrder.Language.LHom.IsExpansionOn (SatLang L C) (SatLang L C') (SatLangMap inc) N instN
      (@SatExpansion L C C' inc hinc N instN w) := by
  letI : (SatLang L C).Structure N := instN
  letI : (SatLang L C').Structure N := @SatExpansion L C C' inc hinc N instN w
  refine ⟨fun {n} f x => ?_, fun {n} R x => ?_⟩
  · cases f with
    | inl g =>
      simp only [SatLangMap, LHom.sumMap_onFunction, Sum.map_inl, LHom.id_onFunction, id_eq]
      rfl
    | inr c =>
      rcases n with _ | k
      · have hx : x = default := funext fun i => i.elim0
        rw [hx]
        simp only [SatLangMap, LHom.sumMap_onFunction, Sum.map_inr]
        rw [constantsOnMap_onFunction_zero inc c]
        have h1 : @Structure.funMap (SatLang L C') N (@SatExpansion L C C' inc hinc N instN w) 0
            (Sum.inr (inc c)) default = @SatConVal L C N instN c := by
          rw [@SatExpansion_funMap_const L C C' inc hinc N instN w (inc c) default]
          exact @SatExpVal_inc L C C' inc hinc N instN w c
        exact h1.trans (@SatConVal_funMap L C N instN c default).symm
      · exact isEmptyElim c
  · cases R with
    | inl r =>
      simp only [SatLangMap, LHom.sumMap_onRelation, Sum.map_inl, LHom.id_onRelation, id_eq]
      rfl
    | inr e => exact isEmptyElim e

theorem SatExpansionModel {L : FirstOrder.Language.{0, 0}} {C C' : Type} (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) (instN : (SatLang L C).Structure N) (w : C' → N)
    (T : (SatLang L C).Theory)
    (hT : @FirstOrder.Language.Theory.Model (SatLang L C) N instN T)
    (σ : (SatLang L C').Sentence)
    (hσ : σ ∈ (SatLangMap inc).onTheory T) :
    @FirstOrder.Language.Sentence.Realize (SatLang L C') N
      (@SatExpansion L C C' inc hinc N instN w) σ := by
  obtain ⟨τ, hτ, rfl⟩ := FirstOrder.Language.LHom.mem_onTheory.mp hσ
  exact (@FirstOrder.Language.LHom.realize_onSentence (SatLang L C) (SatLang L C') N instN
    (@SatExpansion L C C' inc hinc N instN w) (SatLangMap inc)
    (SatExpansion_isExpansionOn inc hinc N instN w) τ).2
    (hT.realize_of_mem τ hτ)

end Work.WilC5
