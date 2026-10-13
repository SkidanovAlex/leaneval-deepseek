import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatSentRealize

namespace Work.WilC5

theorem SatCons2_exists_realize {L : FirstOrder.Language.{0, 0}} {C : Type} (N : Type)
    (instN : (Work.WilC5.SatLang L C).Structure N) {T : (Work.WilC5.SatLang L C).Theory}
    (hT : @FirstOrder.Language.Theory.Model (Work.WilC5.SatLang L C) N instN T)
    (q : Work.WilC5.SatTyp2 L C) (hq : Work.WilC5.SatCons2 T q)
    (F : Finset ((Work.WilC5.SatLang L C).Formula (q.1 ⊕ Fin 1)))
    (hF : ∀ φ ∈ F, φ ∈ q.2) :
    ∃ y : N, ∀ φ ∈ F,
      @FirstOrder.Language.Formula.Realize (Work.WilC5.SatLang L C) N instN (q.1 ⊕ Fin 1) φ
        (Sum.elim (fun t : q.1 =>
            @FirstOrder.Language.Term.realize (Work.WilC5.SatLang L C) N instN Empty
              (default : Empty → N) t.1)
          (fun _ : Fin 1 => y)) := by
  -- The finite fragment `F` consists of formulas of the type `q`, so its sentence `q.sent F`
  -- lies in the theory `T` by consistency of `q`.
  have hmem : q.sent F ∈ T := hq F hF
  -- Since `N` is a model of `T`, that sentence holds in `N`.
  have hsat : N ⊨ q.sent F := hT.realize_of_mem _ hmem
  -- Unfolding the semantics of `q.sent F` (the sentence `∃y ⋀F`) produces the required witness.
  exact (SatSentRealize N instN q F).mp hsat

end Work.WilC5
