import Submission.Work.EKLC6Core.Assembly
import Submission.Work.EKLC6Core.factor_growth_pos
import Submission.Work.EKLC6Core.ent_ge_growth_uminus
import Submission.Work.EKLC6Core.growth_integral_le_uminus

/-!
# `EKLC6Core.AssemblyFinal` — the assembly with all of C6's mathematics fed in

`Assembly.lean` assembles `P_EntropyLeaf` out of the packaged inequalities `EntGeGrowth`
(`⇐` direction: a contracted root group which is not a cross-section forces positive entropy) and
`EntLeGrowth` (`⇒` direction: the entropy of `aDiag t ·` is bounded by the entropy contribution of
the full stable horospherical subgroup), the packaged case analysis `FactorGrowthPos` and the
integrability `IntegrableGrowthAll` of the entropy contribution.

This file discharges the packagings from the actual theorems:

* `factorGrowthPos_holds` — the case analysis, from `factor_growth_pos` (Pisa Cor. 9.10/R2);
* `entGeGrowth_holds` — `EntGeGrowth` from
  * `ent_ge_growth_uminus` (Pisa 7.6(ii) for `U = Uminus t`), and
  * `growth_integral_le_uminus` (the additivity `∫ growthFun (Uminus t) = Σ ∫ growthFun (Uij)`
    with all summands non-negative, singling out one contracted root group);
* `entLeGrowth_holds` — `EntLeGrowth` from `ent_le_growth` (Pisa 7.43);
* `P_EntropyLeaf_of_tools` — `P_EntropyLeaf` from the component `Prop`s `P_Leafwise`, `P_Product`
  and the integrability `IntegrableGrowthAll`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The packaged case analysis, discharged by `factor_growth_pos`. -/
theorem factorGrowthPos_holds : FactorGrowthPos := by
  intro hLeaf hprod μ hμ hErg t ν X' X'' hL hcov hX'' hint hintf hpos
  haveI := hμ
  exact factor_growth_pos hLeaf hprod hErg t hL hcov hX'' hint hintf hpos

/-- **`EntGeGrowth`** (`⇐` direction of Pisa 7.6): the entropy contribution of a *single*
contracted root group is dominated by the entropy of `aDiag t ·`.

Route: Pisa 7.6(ii) for the full stable horospherical subgroup `Uminus t`
(`ent_ge_growth_uminus`), plus the additivity of the entropy contribution over the root-group
decomposition of `Uminus t` (`growth_integral_le_uminus`), whose other summands are `≥ 0` since
`conjBox U t ⊆ Box1 U` for a contracted `U`. -/
theorem entGeGrowth_holds (hLeaf : P_Leafwise) (hprod : P_Product) (hint : IntegrableGrowthAll) :
    EntGeGrowth := by
  intro μ hμ hErg t i j hij hlt ν X' X'' hL hcov hX'' hmeas hintij
  haveI := hμ
  have hAinv : IsAInvariant μ := hErg.1
  have hHoro : IsHoro (Uminus t) := (uminus_isHoro t).1
  obtain ⟨t0, ht0⟩ := hHoro.2.2
  have hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hAinv t0
  obtain ⟨ν0, X0, hL0⟩ := (hLeaf μ (Uminus t) hHoro t0 hmp ht0).1
  obtain ⟨hL0', hfin0⟩ := Work.EKLCompLeaf.fixRadon hL0
  set νU : X3 → Measure SL3 := Work.EKLComp.fixRadon ν0 X0 with hνU
  obtain ⟨X0'', -, -, hX0''null, hcov0⟩ := acovariant_of_leafwise hLeaf hAinv hHoro hL0'
  have hintU : Integrable (growthFun (Uminus t) νU t) μ := (hint μ hAinv t).1 νU X0 hL0'
  have hboundU := ent_ge_growth_uminus t hErg hL0' hcov0 hX0''null hintU
  have hintf : ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j →
      ∀ (ν' : X3 → Measure SL3) (X : Set X3), IsLeafwise μ (Uij hij) ν' X →
        Integrable (growthFun (Uij hij) ν' t) μ :=
    fun i j hij hlt ν' X hL' => (hint μ hAinv t).2 i j hij hlt ν' X hL'
  obtain ⟨νij, Xij, hLij, hle⟩ :=
    growth_integral_le_uminus hLeaf hprod hErg t hL0' hcov0 hX0''null hintU hintf i j hij hlt
  have hHoroij : IsHoro (Uij hij) := Lemmas.isHoro_Uij hij
  obtain ⟨t1, ht1⟩ := hHoroij.2.2
  have hmpt1 : MeasurePreserving (fun x : X3 => aDiag t1 • x) μ μ := hAinv t1
  have huniq : ∀ᵐ x ∂μ, νij x = ν x :=
    ((hLeaf μ (Uij hij) hHoroij t1 hmpt1 ht1).2 ν X' hL).1 νij Xij hLij
  have hgrowth_eq : growthFun (Uij hij) νij t =ᵐ[μ] growthFun (Uij hij) ν t :=
    huniq.mono fun x hx => by simp only [growthFun, hx]
  have hint_eq : ∫ x, growthFun (Uij hij) νij t x ∂μ = ∫ x, growthFun (Uij hij) ν t x ∂μ :=
    integral_congr_ae hgrowth_eq
  calc ENNReal.ofReal (∫ x, growthFun (Uij hij) ν t x ∂μ)
      = ENNReal.ofReal (∫ x, growthFun (Uij hij) νij t x ∂μ) := by rw [hint_eq]
    _ ≤ ENNReal.ofReal (∫ x, growthFun (Uminus t) νU t x ∂μ) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ent μ (fun x : X3 => aDiag t • x) := hboundU

/-- **`P_EntropyLeaf` from the two packaged inequalities and the two component `Prop`s.** -/
theorem P_EntropyLeaf_of_components_final (hge : EntGeGrowth) (hle : EntLeGrowth)
    (hLeaf : P_Leafwise) (hprod : P_Product) (hint : IntegrableGrowthAll) : P_EntropyLeaf :=
  P_EntropyLeaf_of_components hge hle factorGrowthPos_holds hLeaf hprod hint

/-- **Component C6, reduced to `EntLeGrowth` and the component `Prop`s.**  Everything
mathematical from Pisa §7 that C6 needs for the `⇐` direction is fed in here
(`entGeGrowth_holds`); the remaining inputs are `EntLeGrowth` (Pisa 7.43, i.e.
`EKLC6Core.ent_le_growth`), the component `Prop`s `P_Leafwise` (C5) and `P_Product` (C5b), and
the integrability of the entropy contribution (`IntegrableGrowthAll`, i.e. Pisa 7.6/7.18:
`D_μ(a,U) < ∞`). -/
theorem P_EntropyLeaf_of_tools (hle : EntLeGrowth) (hLeaf : P_Leafwise) (hprod : P_Product)
    (hint : IntegrableGrowthAll) : P_EntropyLeaf :=
  P_EntropyLeaf_of_components_final (entGeGrowth_holds hLeaf hprod hint) hle
    hLeaf hprod hint

end Work.EKLC6Core

end
