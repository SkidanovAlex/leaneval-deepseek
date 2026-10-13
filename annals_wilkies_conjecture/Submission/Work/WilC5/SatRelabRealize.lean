import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatHull
import Submission.Work.WilC5.SatTrans

namespace Work.WilC5

theorem SatRelabRealize {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} {N : Type} [instN : (SatLang L (SatCTotal L M κ)).Structure N]
    {z : SatIdx κ} {A : Type} (f : A → (SatLang L (SatC L M κ z)).Term Empty)
    (φ : L.Formula (A ⊕ Fin 1)) (x : N) :
    @FirstOrder.Language.Formula.Realize (SatLang L (SatC L M κ z)) N
        ((SatLangMap (SatIncTotal L M κ z)).reduct N) (Set.range f ⊕ Fin 1)
        (SatRelab L M κ z f φ)
        (Sum.elim (fun a' : Set.range f =>
            @FirstOrder.Language.Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty
              (default : Empty → N) ((SatLangMap (SatIncTotal L M κ z)).onTerm a'.1))
          (fun _ : Fin 1 => x)) ↔
    @FirstOrder.Language.Formula.Realize L N (SatReduct L M κ N) (A ⊕ Fin 1) φ
        (Sum.elim (fun a : A =>
            @FirstOrder.Language.Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty
              (default : Empty → N) ((SatLangMap (SatIncTotal L M κ z)).onTerm (f a)))
          (fun _ : Fin 1 => x)) := by
  rw [SatRelab]
  have hexp : @FirstOrder.Language.LHom.IsExpansionOn L (SatLang L (SatC L M κ z))
      (L.lhomWithConstants (SatC L M κ z)) N (SatReduct L M κ N)
      ((SatLangMap (SatIncTotal L M κ z)).reduct N) :=
    @FirstOrder.Language.LHom.isExpansionOn_reduct L (SatLang L (SatC L M κ z))
      (L.lhomWithConstants (SatC L M κ z)) N
      ((SatLangMap (SatIncTotal L M κ z)).reduct N)
  refine (@FirstOrder.Language.LHom.realize_onFormula L (SatLang L (SatC L M κ z)) N
      (SatReduct L M κ N) (Set.range f ⊕ Fin 1)
      ((SatLangMap (SatIncTotal L M κ z)).reduct N)
      (L.lhomWithConstants (SatC L M κ z)) hexp
      (FirstOrder.Language.BoundedFormula.subst φ (fun i => match i with
        | Sum.inl a => FirstOrder.Language.Term.var (Sum.inl ⟨f a, Set.mem_range_self a⟩)
        | Sum.inr k => FirstOrder.Language.Term.var (Sum.inr k)))
      (Sum.elim (fun a' : Set.range f =>
          @FirstOrder.Language.Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty
            (default : Empty → N) ((SatLangMap (SatIncTotal L M κ z)).onTerm a'.1))
        (fun _ : Fin 1 => x))).trans ?_
  simp only [FirstOrder.Language.Formula.Realize,
    FirstOrder.Language.BoundedFormula.realize_subst]
  refine iff_of_eq (congrArg (fun w =>
    @FirstOrder.Language.BoundedFormula.Realize L N (SatReduct L M κ N) (A ⊕ Fin 1) 0 φ w
      (default : Fin 0 → N)) ?_)
  funext a
  rcases a with a | k <;> rfl

end Work.WilC5
