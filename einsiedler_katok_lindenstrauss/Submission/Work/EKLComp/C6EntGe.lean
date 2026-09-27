import Mathlib
import Submission.Work.EKLC6Core.Assembly
import Submission.Work.EKLC6Core.factor_growth_pos
import Submission.Work.EKLC6Core.growth_integral_le_uminus
import Submission.Work.EKLC6Core.ent_ge_growth_assembly
import Submission.Work.EKLC6Core.ent_ge_growth_uminus
import Submission.Work.EKLC6Core.exists_good_set_plaque
import Submission.Work.EKLC6Core.exists_markov_plaque_algebra
import Submission.Work.EKLC6Core.acovariant_of_leafwise

/-!
# `Work.EKLComp.C6EntGe` — the `⇐` half of C6 without the *false* geometric input

`Work.EKLC6Core.ent_ge_growth_uminus` (Pisa 7.6(ii) for the full contracted horospherical
subgroup, the inequality `ofReal (∫ growthFun (Uminus t) ν t) ≤ ent μ (aDiag t ·)`) obtains its
conull, `aDiag t`-decreasing plaque algebra from `Work.EKLC6Core.exists_gen_plaque`, whose proof
rests on `Work.EKLC6Core.exists_gen_partition`.  That last statement demands the **exact**
σ-algebra equality `fullSigma t P = borel X₃` for a *countable partition* `P`, which is *false* as
stated (uncountably many fixed points of `aDiag t ·` cannot be separated by the σ-algebra of a
countable family; see the machine-checked refutation in
`EKLC6Core/gen_partition_of_core.lean`, recorded in `EKLC6Core/ENTROPY_GEN_NOTE.md` §0b).

Only three clauses of `exists_gen_plaque` are used by that proof:
`IsPlaqueAlgebra (Uminus t) Z A`, `μ Zᶜ = 0` and `comap (aDiag t ·) A ≤ A`.  All three are
supplied, unconditionally for an `A`-ergodic `μ`, by the **proved, axiom-clean**
`Work.EKLC6Core.exists_desc_plaque_algebra_uniform` (Pisa 7.37/7.38 + the ergodic conull upgrade;
`EKLC6Core/exists_markov_plaque_algebra.lean`).  This file repeats that proof with the corrected
source, and repackages `EntGeGrowth` (the `⇐` direction of Pisa 7.6) on top of it, so that the
`⇐` direction no longer depends on the false statement.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-- **Pisa 7.6(ii) for the full contracted horospherical subgroup**, with the conull descending
plaque algebra taken from `Work.EKLC6Core.exists_desc_plaque_algebra_uniform`. -/
theorem ent_ge_growth_uminus_plq {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : X3 → MeasureTheory.Measure SL3} {X' X'' : Set X3} (t : Fin 3 → ℝ)
    (hErg : IsAErgodic μ)
    (hL : IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) ≤
      ent μ (fun x : X3 => aDiag t • x) := by
  have hAinv : IsAInvariant μ := hErg.1
  have hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ := hAinv t
  have hU : IsHoro (Work.EKLC6Core.Uminus t) := (Work.EKLC6Core.uminus_isHoro t).1
  have hcontr : ∀ u ∈ Work.EKLC6Core.Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1) :=
    Work.EKLC6Core.tendsto_conj_mem_uminus t
  by_cases hne : Work.EKLC6Core.Uminus t = (⊥ : Subgroup SL3)
  · rw [hne] at hL ⊢
    exact Work.EKLC6Core.ent_ge_growth_bot hL t hne
  · -- the conull descending plaque algebra, from the proved uniform Markov core
    obtain ⟨A, Z, _C, hplaq, hZ, hdec, -, -⟩ :=
      Work.EKLC6Core.exists_desc_plaque_algebra_uniform (μ := μ) t hErg
    obtain ⟨Y, δ, R, hYmeas, hδ, hR, hY, hvisit⟩ :=
      Work.EKLC6Core.exists_good_set_plaque t hmp hplaq hZ
    exact Work.EKLC6Core.ent_ge_growth_of_goodset hL hU hcov hX'' t hcontr hAinv hint
      hplaq hdec hZ hYmeas hδ hR hY hvisit

/-- **`EntGeGrowth`** (`⇐` direction of Pisa 7.6), with the corrected plaque-algebra source. -/
theorem entGeGrowth_plq (hLeaf : P_Leafwise) (hprod : P_Product)
    (hint : Work.EKLC6Core.IntegrableGrowthAll) : Work.EKLC6Core.EntGeGrowth := by
  intro μ hμ hErg t i j hij hlt ν X' X'' hL hcov hX'' hmeas hintij
  haveI := hμ
  have hAinv : IsAInvariant μ := hErg.1
  have hHoro : IsHoro (Work.EKLC6Core.Uminus t) := (Work.EKLC6Core.uminus_isHoro t).1
  obtain ⟨t0, ht0⟩ := hHoro.2.2
  have hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hAinv t0
  obtain ⟨ν0, X0, hL0⟩ := (hLeaf μ (Work.EKLC6Core.Uminus t) hHoro t0 hmp ht0).1
  obtain ⟨hL0', hfin0⟩ := Work.EKLCompLeaf.fixRadon hL0
  set νU : X3 → Measure SL3 := Work.EKLComp.fixRadon ν0 X0 with hνU
  obtain ⟨X0'', -, -, hX0''null, hcov0⟩ :=
    Work.EKLC6Core.acovariant_of_leafwise hLeaf hAinv hHoro hL0'
  have hintU : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) νU t) μ :=
    (hint μ hAinv t).1 νU X0 hL0'
  have hboundU := ent_ge_growth_uminus_plq (μ := μ) t hErg hL0' hcov0 hX0''null hintU
  have hintf : ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j →
      ∀ (ν' : X3 → Measure SL3) (X : Set X3), IsLeafwise μ (Uij hij) ν' X →
        MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Uij hij) ν' t) μ :=
    fun i j hij hlt ν' X hL' => (hint μ hAinv t).2 i j hij hlt ν' X hL'
  obtain ⟨νij, Xij, hLij, hle⟩ :=
    Work.EKLC6Core.growth_integral_le_uminus hLeaf hprod hErg t hL0' hcov0 hX0''null hintU
      hintf i j hij hlt
  have hHoroij : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  obtain ⟨t1, ht1⟩ := hHoroij.2.2
  have hmpt1 : MeasurePreserving (fun x : X3 => aDiag t1 • x) μ μ := hAinv t1
  have huniq : ∀ᵐ x ∂μ, νij x = ν x :=
    ((hLeaf μ (Uij hij) hHoroij t1 hmpt1 ht1).2 ν X' hL).1 νij Xij hLij
  have hgrowth_eq : Work.EKLC6Core.growthFun (Uij hij) νij t =ᵐ[μ]
      Work.EKLC6Core.growthFun (Uij hij) ν t :=
    huniq.mono fun x hx => by simp only [Work.EKLC6Core.growthFun, hx]
  have hint_eq : ∫ x, Work.EKLC6Core.growthFun (Uij hij) νij t x ∂μ
      = ∫ x, Work.EKLC6Core.growthFun (Uij hij) ν t x ∂μ :=
    integral_congr_ae hgrowth_eq
  calc ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Uij hij) ν t x ∂μ)
      = ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Uij hij) νij t x ∂μ) := by rw [hint_eq]
    _ ≤ ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) νU t x ∂μ) :=
        ENNReal.ofReal_le_ofReal hle
    _ ≤ ent μ (fun x : X3 => aDiag t • x) := hboundU

end Work.EKLComp

end
