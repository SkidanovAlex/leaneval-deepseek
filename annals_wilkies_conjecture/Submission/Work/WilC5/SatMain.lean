/-
  WilC5 — the main induction of the syntactic saturation construction.

  `SatMain x` says that the specification `SatSpecG x` at level `x` is satisfiable and that the
  structure `SatMod3 x` built at level `x` realizes every sentence of that specification.  It is
  proved by well-founded induction on the well-ordered index type `SatIdx κ`, using the successor
  step `SatSpecSucc` and the limit step `SatSpecLimit`.
-/
import Mathlib
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatSpecSucc
import Submission.Work.WilC5.SatSpecLimit

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- **Main induction.**  For every level `x`, the specification `SatSpecG x` is satisfiable and the
structure `SatMod3 x` at level `x` realizes all its sentences. -/
theorem SatMain (hM : Nonempty M) (x : SatIdx κ) :
    (SatSpecG L M κ x).IsSatisfiable ∧
    (∀ σ : (L[[SatC L M κ x]]).Sentence, σ ∈ SatSpecG L M κ x →
      @Sentence.Realize (L[[SatC L M κ x]]) (SatMod3 L M κ x) (SatStruc3 L M κ x) σ) := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
  have hsat : (SatSpecG L M κ x).IsSatisfiable := by
    rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
    intro T0 hT0
    by_cases hsucc : ∃ u : SatIdx κ, Order.succ u = x
    · obtain ⟨m, rfl⟩ := hsucc
      refine SatSpecSucc (L := L) (M := M) (κ := κ) (m := m) (SatMod3_nonempty L M κ m)
        (fun σ hσ => (ih m (Order.lt_succ m)).2 σ hσ) T0 ?_
      intro σ hσ
      exact hT0 hσ
    · refine SatSpecLimit (L := L) (M := M) (κ := κ) (x := x) hM ?_
        (fun y _ => SatMod3_nonempty L M κ y) (fun y hy σ hσ => (ih y hy).2 σ hσ) T0 ?_
      · intro u hcon
        exact hsucc ⟨u, hcon.symm⟩
      · intro σ hσ
        exact hT0 hσ
  refine ⟨hsat, ?_⟩
  intro σ hσ
  change @Sentence.Realize (L[[SatC L M κ x]]) (SatData3 L M κ x).1 (SatData3 L M κ x).2 σ
  have hsig : SatData3 L M κ x = ⟨hsat.some.Carrier, hsat.some.struc⟩ := by
    rw [SatData3_eq L M κ x, dif_pos hsat]
  rw [hsig]
  exact hsat.some.is_model.realize_of_mem σ hσ

end Work.WilC5
