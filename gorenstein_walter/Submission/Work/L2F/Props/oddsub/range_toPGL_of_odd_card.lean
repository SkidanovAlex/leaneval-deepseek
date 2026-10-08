import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Props.odd_order_mem_toPGL_range

namespace Work.L2F.Props.oddsub

theorem range_toPGL_of_odd_card (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K)) :
    K ≤ Matrix.SpecialLinearGroup.toPGL.range := by
  intro k hk
  exact Work.L2F.Props.odd_order_mem_toPGL_range F k
    (Odd.of_dvd_nat hodd (K.orderOf_dvd_natCard hk))

end Work.L2F.Props.oddsub
