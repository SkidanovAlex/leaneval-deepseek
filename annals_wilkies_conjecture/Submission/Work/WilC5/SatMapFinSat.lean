import Mathlib
import Submission.Work.WilC5.SatSetup

open FirstOrder Language
open scoped FirstOrder

namespace Work.WilC5

/-- The language map `L[[C]] →ᴸ L[[C']]` induced by an *injective* map `f : C → C'` on the
constants is itself injective (as a map of languages): it is the sum of the identity on `L` and
`constantsOnMap f`, and the latter is injective precisely because `f` is.

This is the key structural hypothesis needed to push the complete theory of an `L[[C]]`-structure
forward along `f` while retaining satisfiability. -/
theorem SatLangMap_injective {L : FirstOrder.Language.{0, 0}} {C C' : Type} (f : C → C')
    (hf : Function.Injective f) : (SatLangMap (L := L) f).Injective := by
  have hconst : ∀ n, Function.Injective fun c : (constantsOn C).Functions n =>
      (LHom.constantsOnMap f).onFunction c := by
    intro n
    cases n with
    | zero => exact hf
    | succ n => exact fun a => isEmptyElim a
  constructor
  · intro n
    exact (Function.injective_id.sumMap (hconst n))
  · intro n
    exact (Function.injective_id.sumMap (fun a => isEmptyElim a))

theorem SatMapFinSat {L : FirstOrder.Language.{0, 0}} {C C' : Type} (f : C → C')
    (hf : Function.Injective f) (M : Type) [Nonempty M]
    [FirstOrder.Language.Structure (FirstOrder.Language.withConstants L C) M] :
    ((SatLangMap f).onTheory (FirstOrder.Language.completeTheory
      (FirstOrder.Language.withConstants L C) M)).IsFinitelySatisfiable := by
  -- `M` models its own complete theory, hence that theory is satisfiable …
  have hT : (FirstOrder.Language.completeTheory
      (FirstOrder.Language.withConstants L C) M).IsSatisfiable :=
    FirstOrder.Language.Theory.Model.isSatisfiable M
  -- … and an injective language map preserves satisfiability of the theory it pushes forward.
  have h := (FirstOrder.Language.Theory.isSatisfiable_onTheory_iff
    (SatLangMap_injective f hf)).2 hT
  exact h.isFinitelySatisfiable

end Work.WilC5
