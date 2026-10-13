import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.coreLT_succ.SwapEquiv0

namespace Work.WilE7.Endgame

theorem E2_swapStratum_projFirst {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 ((n + 1) + m)) :
    WilkiesDesign.E.projFirst n (m + 1) ''
        Work.WilE7.MainDesign.absSet (Work.WilE7.Endgame.E2.swapStratum T)
      = Work.WilE7.MainDesign.basePr n m '' Work.WilE7.MainDesign.absSet T := by
  -- `π_n` (in the `(n, m+1)` frame) is `Fin.init ∘ projTop`: forget the vertical coordinate.
  have h1 : WilkiesDesign.E.projFirst n (m + 1)
      = Fin.init ∘ Work.WilE7.CoreStep.projTop n m := by
    funext z; exact (Work.WilE7.CoreStep.projTop_init n m z).symm
  -- `basePr n m` (in the `((n+1), m)` frame) is `Fin.init ∘ π_{n+1}`: forget the level coordinate.
  have h2 : Work.WilE7.MainDesign.basePr n m
      = fun z => Fin.init (WilkiesDesign.E.projFirst (n + 1) m z) := by
    funext z; exact (Work.WilE7.Endgame.E2.init_projFirst (n := n) (m := m) z).symm
  rw [h1, Set.image_comp, Work.WilE7.Endgame.E2.swapStratum_projTop, Set.image_image, ← h2]

end Work.WilE7.Endgame
