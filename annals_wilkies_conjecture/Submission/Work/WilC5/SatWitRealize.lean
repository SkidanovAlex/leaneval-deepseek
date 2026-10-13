import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatExpand

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section
open Classical

namespace Work.WilC5

/-- The two ways of viewing a constant of level `z` as a constant of the total set of constants
agree: `SatIncTotal` is compatible with `SatIncSucc`. -/
theorem SatIncTotal_SatIncSucc (L : FirstOrder.Language.{0, 0}) (M : Type) (κ : Cardinal.{0})
    (z : SatIdx κ) (c : SatC L M κ z) :
    SatIncTotal L M κ (Order.succ z) (SatIncSucc L M κ z c) = SatIncTotal L M κ z c :=
  congrFun (SatIncTotal_comp L M κ (le_of_lt (Order.lt_succ z))) c

/-- Realising a witness sentence `SatWitSent2 inc cnew q φ` in the structure obtained from an
`L[[C'']]`-structure `N` by pulling back along `inc' : C' → C''` is the same as realising the
original formula `φ` in the pullback along the composite `inc'' = inc' ∘ inc`, with the parameters
of the type interpreted by the values of their terms and the last variable interpreted by the value
of the new constant `cnew q`.

This is the "reduct" version of the semantic unfolding of the witness sentences; it is used below
with `inc = SatIncSucc z`, `inc' = SatIncTotal (succ z)` and `inc'' = SatIncTotal z`. -/
theorem SatWitSent2_reduct_realize {L : FirstOrder.Language.{0, 0}} {C C' C'' : Type}
    (inc : C → C') (inc' : C' → C'') (inc'' : C → C'')
    (hcomp : ∀ c, inc' (inc c) = inc'' c)
    (N : Type) [instN : (SatLang L C'').Structure N]
    (cnew : SatTyp2 L C → C') (q : SatTyp2 L C)
    (φ : (SatLang L C).Formula (q.1 ⊕ Fin 1)) :
    @FirstOrder.Language.Sentence.Realize (SatLang L C') N ((SatLangMap inc').reduct N)
        (SatWitSent2 inc cnew q φ) ↔
    @FirstOrder.Language.Formula.Realize (SatLang L C) N ((SatLangMap inc'').reduct N)
        (q.1 ⊕ Fin 1) φ
        (Sum.elim (fun t : q.1 =>
            @FirstOrder.Language.Term.realize (SatLang L C'') N instN Empty
              (default : Empty → N) ((SatLangMap inc'').onTerm t.1))
          (fun _ : Fin 1 => @SatConVal L C'' N instN (inc' (cnew q)))) := by
  letI i'' : (SatLang L C'').Structure N := instN
  letI i' : (SatLang L C').Structure N := (SatLangMap inc').reduct N
  letI i : (SatLang L C).Structure N := (SatLangMap inc'').reduct N
  haveI hexp : @FirstOrder.Language.LHom.IsExpansionOn (SatLang L C) (SatLang L C')
      (SatLangMap inc) N i i' := by
    refine ⟨?_, ?_⟩
    · intro n f x
      cases f with
      | inl g =>
        show @FirstOrder.Language.Structure.funMap (SatLang L C'') N instN n
              ((SatLangMap inc').onFunction ((SatLangMap inc).onFunction (Sum.inl g))) x
            = @FirstOrder.Language.Structure.funMap (SatLang L C'') N instN n
              ((SatLangMap inc'').onFunction (Sum.inl g)) x
        rfl
      | inr c =>
        cases n with
        | zero =>
          have h1 : (SatLangMap (L := L) inc).onFunction (Sum.inr c : (SatLang L C).Functions 0) =
              (Sum.inr (inc c) : (SatLang L C').Functions 0) := rfl
          have h2 : (SatLangMap (L := L) inc').onFunction
                (Sum.inr (inc c) : (SatLang L C').Functions 0) =
              (Sum.inr (inc' (inc c)) : (SatLang L C'').Functions 0) := rfl
          have h3 : (SatLangMap (L := L) inc'').onFunction
                (Sum.inr c : (SatLang L C).Functions 0) =
              (Sum.inr (inc'' c) : (SatLang L C'').Functions 0) := rfl
          show @FirstOrder.Language.Structure.funMap (SatLang L C'') N instN 0
                ((SatLangMap inc').onFunction ((SatLangMap inc).onFunction (Sum.inr c))) x
              = @FirstOrder.Language.Structure.funMap (SatLang L C'') N instN 0
                ((SatLangMap inc'').onFunction (Sum.inr c)) x
          rw [h1, h2, h3, hcomp c]
        | succ k => exact isEmptyElim c
    · intro n R x
      cases R with
      | inl r =>
        show @FirstOrder.Language.Structure.RelMap (SatLang L C'') N instN n
              ((SatLangMap inc').onRelation ((SatLangMap inc).onRelation (Sum.inl r))) x
            = @FirstOrder.Language.Structure.RelMap (SatLang L C'') N instN n
              ((SatLangMap inc'').onRelation (Sum.inl r)) x
        rfl
      | inr e => exact isEmptyElim e
  have hfun : (fun a : q.1 ⊕ Fin 1 =>
      @FirstOrder.Language.Term.realize (SatLang L C') N i' Empty (default : Empty → N)
        (match a with
         | Sum.inl t => (SatLangMap inc).onTerm t.1
         | Sum.inr _ =>
           (FirstOrder.Language.Constants.term (L.con (cnew q)) : (SatLang L C').Term Empty)))
      = Sum.elim (fun t : q.1 =>
          @FirstOrder.Language.Term.realize (SatLang L C'') N instN Empty (default : Empty → N)
            ((SatLangMap inc'').onTerm t.1))
        (fun _ : Fin 1 => @SatConVal L C'' N instN (inc' (cnew q))) := by
    funext a
    cases a with
    | inl t => simp only [Sum.elim_inl, FirstOrder.Language.LHom.realize_onTerm]
    | inr k =>
      rw [Sum.elim_inr]
      rw [FirstOrder.Language.Term.realize_constants]
      rfl
  rw [SatWitSent2, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    FirstOrder.Language.BoundedFormula.realize_subst]
  rw [FirstOrder.Language.Formula.boundedFormula_realize_eq_realize]
  rw [FirstOrder.Language.LHom.realize_onFormula]
  exact iff_of_eq (congrArg (FirstOrder.Language.Formula.Realize φ) hfun)

theorem SatWitRealize {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} {N : Type} [instN : (SatLang L (SatCTotal L M κ)).Structure N]
    {z : SatIdx κ} (q : SatTyp2 L (SatC L M κ z))
    (φ : (SatLang L (SatC L M κ z)).Formula (q.1 ⊕ Fin 1)) :
    @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ (Order.succ z))) N
        ((SatLangMap (SatIncTotal L M κ (Order.succ z))).reduct N)
        (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ) ↔
    @FirstOrder.Language.Formula.Realize (SatLang L (SatC L M κ z)) N
        ((SatLangMap (SatIncTotal L M κ z)).reduct N) (q.1 ⊕ Fin 1) φ
        (Sum.elim (fun a : q.1 =>
            @FirstOrder.Language.Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty
              (default : Empty → N) ((SatLangMap (SatIncTotal L M κ z)).onTerm a.1))
          (fun _ : Fin 1 =>
            @SatConVal L (SatCTotal L M κ) N instN
              (SatIncTotal L M κ (Order.succ z) (SatNewConst L M κ z q)))) :=
  SatWitSent2_reduct_realize (L := L) (C := SatC L M κ z) (C' := SatC L M κ (Order.succ z))
    (C'' := SatCTotal L M κ) (inc := SatIncSucc L M κ z)
    (inc' := SatIncTotal L M κ (Order.succ z)) (inc'' := SatIncTotal L M κ z)
    (hcomp := fun c => SatIncTotal_SatIncSucc L M κ z c) (N := N) (instN := instN)
    (cnew := SatNewConst L M κ z) (q := q) (φ := φ)

end Work.WilC5
