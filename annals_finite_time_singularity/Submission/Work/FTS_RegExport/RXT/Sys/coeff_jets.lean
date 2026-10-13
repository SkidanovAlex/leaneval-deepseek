import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffBnd
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.coeff_jets` — the `CoeffJets` producer for the constructed family

This file assembles the coefficient package `CoeffJets` consumed by the RX-St1 chain
(`CoeffJetsDefs`, the repair of `VelPkgSup` on the open angular interval) from its two halves:

* `Sys.CoeffBnd.coeff_dbnd` — the order-`≤ 2` mixed-jet bounds of `Vz7`, `Vθ7/sin 2θ`, `cs7`
  and the `∂_θ`-bound of `Vz7`, uniform in the fake time `τ ∈ [0,S]`.  Its inputs are the
  uniform slot bounds `RXT.velVanish2`, the explicit-piece bounds `Sys.explicit_pieces_coeff`,
  the `∂_θ`-slot bound `Sys.pth_vop_slot_bd`, the uniform `L₁₂`-bound of
  `Sys.L12FK_family_jets` and the `C²`-regularity/coefficient bounds of
  `Sys.CoeffSmooth`/`Sys.CoeffBounds`.
* `Sys.CoeffCont.coeff_cont` — the `τ`-continuity of the three coefficient slices, from the
  clock hypothesis `ClockBd` (the `τ`-continuity of `μ`), the `τ`-Lipschitz bounds of
  `L₁₂(F_τ)`/`𝔽K(F_τ)` (`Sys.L12FK_family_jets`), the slot continuity
  `Sys.slot_tau_cont_alpha` and the closed form of the `Θ`-part (`SysAux.Theta_ops`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

theorem coeff_jets {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, Work.FTS_RegExport.RXT.CoeffJets (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.μR α Φs E g) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) S := by
  intro S hS
  exact ⟨coeff_dbnd (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS,
    coeff_cont (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS⟩

end Work.FTS_RegExport.RXT.Sys
