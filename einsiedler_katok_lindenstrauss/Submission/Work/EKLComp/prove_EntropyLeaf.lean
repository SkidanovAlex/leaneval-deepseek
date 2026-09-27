import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Assembly
import Submission.Work.EKLC6Core.AssemblyFinal
import Submission.Work.EKLC6Core.FinalGlue
import Submission.Work.EKLC6Core.IntegrableAll
import Submission.Work.EKLC6Route.EntLeGrowth_fibres
import Submission.Work.EKLComp.C6EntGe
import Submission.Work.EKLComp.prove_Leafwise
import Submission.Work.EKLComp.prove_Product

/-!
# Component C6 (`Work.EKLComp.prove_EntropyLeaf`) — final state

Target (frozen, `EKLContract/Defs.lean`):

    P_EntropyLeaf : ∀ μ [IsProbabilityMeasure μ], IsAErgodic μ → ∀ t : Fin 3 → ℝ,
      0 < ent μ (aDiag t ·) ↔ ∃ i j (hij : i ≠ j), t i < t j ∧ ¬ CrossSection μ (Uij hij)

The component is the five-term application

    EKLC6Core.P_EntropyLeaf_of_components_final (EntGeGrowth) (EntLeGrowth) (P_Leafwise)
      (P_Product) (IntegrableGrowthAll) : P_EntropyLeaf

(`EKLC6Core/AssemblyFinal.lean`).  Its inputs:

* `P_Leafwise` (C5) — `EKLComp/prove_Leafwise.lean`;
* `P_Product` (C5b) — `EKLComp/prove_Product.lean`;
* `IntegrableGrowthAll` — `EKLC6Core/IntegrableAll.lean` (proved, axiom-clean);
* `EntGeGrowth` (the `⇐` direction, Pisa 7.6(ii)) — `EKLComp/C6EntGe.entGeGrowth_plq`
  (proved, axiom-clean), built on the proved `EKLC6Core.exists_desc_plaque_algebra_uniform`
  rather than on the refuted `exists_gen_partition`;
* `EntLeGrowth` (the `⇒` direction, the equality case of Pisa 7.6(ii)) —
  `Work.EKLC6Route.entLeGrowth_via_fibres` (L0 of `EKLComp/C6GEOM_ROUTE_LEAD.md`), which is the
  tree's proved single-map-ergodic reduction `EKLC6Core.ent_le_growth_of_growth`: the `a`-ergodic
  case `ent_le_growth_of_aerg` together with the fibre route `ent_le_growth_of_not_aerg`.

The proof-term closure of `prove_EntropyLeaf` therefore reaches **exactly one** unproved statement,
`Work.EKLC6Core.exists_plaque_alg_gen_modmu` (Pisa 7.43: for an `aDiag t`-ergodic `μ` a countable
family `S` with `IsPlaqueAlgebra (Uminus t) Z (pastSigSet t S)`, `GeneratesModMuSet μ t S` and
`HcondSig μ (σ S) ⊥ ≠ ⊤`), which is being filled by the route of `C6GEOM_ROUTE_LEAD.md`
(`Work.EKLC6Route.*`).  The earlier assembly through `EKLComp/C6GeomInput.lean`
(`entLeGrowth_of_countableGeom`) is **not** used any more: `C6GeomInput` is true but not provable
from the sources (Pisa 7.43 needs `aDiag t`-ergodicity), and its inner target
`exists_plaque_partition_finiteEnt` is false as stated (see `C6GEOM_ROUTE_LEAD.md` §1).
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Component C6** — the requested statement. -/
theorem prove_EntropyLeaf : Work.EKLContract.P_EntropyLeaf :=
  Work.EKLC6Core.P_EntropyLeaf_of_components_final
    (Work.EKLComp.entGeGrowth_plq Work.EKLComp.prove_Leafwise Work.EKLComp.prove_Product
      (Work.EKLC6Core.integrableGrowthAll_holds Work.EKLComp.prove_Leafwise))
    Work.EKLC6Route.entLeGrowth_via_fibres
    Work.EKLComp.prove_Leafwise Work.EKLComp.prove_Product
    (Work.EKLC6Core.integrableGrowthAll_holds Work.EKLComp.prove_Leafwise)

end Work.EKLComp
