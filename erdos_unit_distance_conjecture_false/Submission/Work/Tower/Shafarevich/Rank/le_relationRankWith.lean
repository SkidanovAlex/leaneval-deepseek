import Mathlib
import Submission.Work.Tower.Defs

namespace Work.Tower.Shafarevich.Rank

theorem le_relationRankWith {G : Type} [Group G] (d r : ℕ)
    (h : ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ ∧
      ∃ R : Fin r → FreeGroup (Fin d), φ.ker = Subgroup.normalClosure (Set.range R)) :
    Work.Tower.relationRankWith G d ≤ r :=
  Nat.sInf_le h

end Work.Tower.Shafarevich.Rank
