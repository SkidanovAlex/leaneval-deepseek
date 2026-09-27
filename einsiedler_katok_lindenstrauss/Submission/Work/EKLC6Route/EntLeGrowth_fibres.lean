import Mathlib
import Submission.Work.EKLC6Core.ofReal_hPart_le_HcondSig_of_growth
import Submission.Work.EKLC6Core.Assembly

/-!
# `Work.EKLC6Route.EntLeGrowth_fibres` — L0 of `C6GEOM_ROUTE_LEAD.md`

The equality case of Pisa 7.6(ii), `EntLeGrowth`, obtained from the tree's already proved
single-map-ergodic reduction `Work.EKLC6Core.ent_le_growth_of_growth` (which combines
`ent_le_growth_of_aerg` with the fibre route `ent_le_growth_of_not_aerg`).  Its only remaining
ingredient in the tree is `Work.EKLC6Core.exists_plaque_alg_gen_modmu` (Pisa 7.43), reached through
the `a`-ergodic branch.

This replaces `Work.EKLComp.entLeGrowth_of_countableGeom` (which consumed
`Work.EKLComp.C6GeomInput`, whose inner target is false as stated) in `prove_EntropyLeaf`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Route

open Work.EKLContract

/-- **L0.**  `EntLeGrowth` for `Uminus t`, via the fibre decomposition. -/
theorem entLeGrowth_via_fibres : Work.EKLC6Core.EntLeGrowth := by
  intro μ hμ ν X' X'' t hErg hL hcov hX'' hmeas hint
  haveI := hμ
  exact Work.EKLC6Core.ent_le_growth_of_growth (μ := μ) t hErg hL hcov hX'' hmeas hint

end Work.EKLC6Route
