
import Mathlib
import Submission.Work.ORDunwoody.A_aux

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

theorem A_negSteps_rev (b : G) (j : Fin P.n) :
    Work.ORDunwoody.Dunwoody.negSteps D b j =
      (Work.ORDunwoody.Dunwoody.posSteps
          D (b * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹) j).reverse.map
        Work.ORDunwoody.Dunwoody.op := by
  rw [negSteps, posSteps]
  by_cases h : D.L (j, true) = 0
  · simp only [h, dif_pos, List.reverse_singleton, List.map_singleton,
      Work.ORDunwoody.Dunwoody.op_skip]
    congr 1
    group
  · simp only [dif_neg h, List.map_reverse, List.map_map]
    rfl

end Work.ORDunwoody
