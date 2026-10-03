import Mathlib
import Submission.Work.ORDunwoody.A_aux

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

universe u

/-- **The positive generator edge based at `b` is the reverse of the negative letter read at
`b * genE (j,true)`.**  Both readings traverse the *same* cells `⟨b, j, k⟩` of `Λ''`: `posSteps`
enumerates them forwards, while `negSteps D (b * genE (j,true)) j` enumerates them backwards (its
base point is `(b * genE (j,true)) * (genE (j,true))⁻¹ = b`, which is where the group identity is
used) and traverses each of them in the `bwd` direction.  Reversing that list and applying the
involution `op` that interchanges `fwd`/`bwd` recovers `posSteps D b j` exactly. -/
theorem A_posSteps_rev {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (b : G) (j : Fin P.n) :
    Work.ORDunwoody.Dunwoody.posSteps D b j =
      (Work.ORDunwoody.Dunwoody.negSteps
        D (b * Work.ORDunwoody.Cayley.CayV.genE P (j, true)) j).reverse.map
        Work.ORDunwoody.Dunwoody.op := by
  rw [posSteps, negSteps]
  by_cases h : D.L (j, true) = 0
  · -- a collapsed generator edge: a single `skip` step, reversed
    simp only [h, dif_pos, List.reverse_singleton, List.map_singleton, op_skip]
    congr 1
    group
  · -- a subdivided generator edge: the same cells, enumerated in the opposite order and reversed
    simp only [dif_neg h, List.map_reverse, List.map_map, List.reverse_reverse,
      mul_inv_cancel_right]
    rfl

end Work.ORDunwoody
