import Submission.Work.EKLC6Core.AssemblyFinal

/-!
# `Work.EKLC6Core.FinalGlue` — the last mile of component C6

`AssemblyFinal.P_EntropyLeaf_of_tools` proves the frozen component

    P_EntropyLeaf : 0 < ent μ (aDiag t ·) ↔ ∃ i j (hij : i ≠ j), t i < t j ∧ ¬ CrossSection μ (Uij hij)

from `EntLeGrowth` (Pisa 7.43), the component `Prop`s `P_Leafwise` (C5) and `P_Product` (C5b),
and the integrability `IntegrableGrowthAll` of the entropy contribution.  `P_Leafwise` is proved
(`EKLComp/prove_Leafwise.lean`) and `P_Product` is proved as well
(`EKLComp/prove_Product.lean`), and both are `sorry`-free; `EntLeGrowth` is instantiated from
`EKLC6Core.ent_le_growth` by

```lean
theorem entLeGrowth_holds : EntLeGrowth := by
  intro μ hμ ν X' X'' t hErg hL hcov hX'' hmeas hint
  haveI := hμ
  exact ent_le_growth t hErg hL hcov hX'' hmeas hint
```

(`ent_le_growth` is `sorry`-free; see item 2 below for the `sorry`s in its closure).  So the last
line of the component is

```lean
theorem prove_EntropyLeaf : Work.EKLContract.P_EntropyLeaf :=
  Work.EKLC6Core.P_EntropyLeaf_of_all <entLeGrowth_holds> Work.EKLComp.prove_Leafwise
    Work.EKLComp.prove_Product <IntegrableGrowthAll>
```

and this file states that assembly with `EntLeGrowth` and `IntegrableGrowthAll` as explicit
hypotheses, so that it does not depend on work in flight.

## The two remaining inputs

**(1) `IntegrableGrowthAll`** — finiteness of the entropy contribution `D_μ(a,U)` (Pisa 7.6/7.18)
for the full stable horospherical subgroup and for every contracted root group:
`Integrable (fun x => growthFun U ν t x) μ`.

`growthFun` is non-negative (`conjBox U t ⊆ Box1 U` for a contracted `U`,
`EKLC6Core.box_conjBox_subset`), so this is a statement about the *size* of the leaf-wise
measures.  Remarks:

* the natural source would be the inequality `∫ growthFun ≤ ent μ (aDiag t ·)` *itself* — hence
  the circularity: the packaged inequalities `EntGeGrowth`/`EntLeGrowth` carry `Integrable`
  explicitly, because the development writes the entropy contribution as a Bochner integral;
* **a proof route for measures of compact support** (which is all the glue needs, since it applies
  `P_EntropyLeaf` only to `μ` with `μ (Thrho ρ) = 1` and `Thrho ρ` is compact):
  on a compact Lusin set of the leaf-wise system (U6 of `P_Leafwise`), `x ↦ ν x (V δ)` is
  continuous and strictly positive (the `pos` field), hence bounded below by a positive constant;
  since `conjBox U t` contains `V δ ∩ U` for some `δ > 0` (`EKLC6Core.conjBox_nhds`), this bounds
  `growthFun` from above by a constant on that compact set, so the integral over `μ` is finite.
  The same argument bounds `∫ growthFun` by `C / μ (Lusin set)` and needs μ to be supported on a
  compact set (or the leaf-wise measures to be locally uniformly non-degenerate);
* the fully faithful (Bochner-integral-free) formulation replaces the Bochner integral by the
  `ℝ≥0∞`-valued `∫⁻ x, ENNReal.ofReal (growthFun U ν t x)`, which is what `ent` is valued in.
  With that formulation Pisa 7.6(ii) needs no integrability hypothesis at all and the case
  `ent μ (aDiag t ·) = ∞` is absorbed by `∞`-arithmetic; the present development keeps the
  workspace's Bochner-integral API, so the finiteness of `D_μ(a,U)` has to be supplied.

**(2) the four `sorry`s in the closure of `ent_le_growth`** at the time of writing:
`exists_plaque_family_conull` (2, the conull plaque algebra; also the sole remaining input of
`EntGeGrowth`), `exists_finPart_plaquePast_generating`, `condExpKernel_quasiErgodic` and
`fiber_leafwise_thm`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Component C6** (`P_EntropyLeaf`) from its four named inputs. -/
theorem P_EntropyLeaf_of_all (hle : EntLeGrowth) (hLeaf : P_Leafwise) (hprod : P_Product)
    (hint : IntegrableGrowthAll) : P_EntropyLeaf :=
  P_EntropyLeaf_of_tools hle hLeaf hprod hint

end Work.EKLC6Core

end
