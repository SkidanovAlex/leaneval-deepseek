import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs

namespace Work.HP.numaux

theorem rk_span_eq {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} {b : Fin r → (ι → ℤ)}
    (hb : LinearIndependent ℤ b) : rk (Submodule.span ℤ (Set.range b)) = r := by
  rw [Work.HP.rk, finrank_span_eq_card hb, Fintype.card_fin]

end Work.HP.numaux
