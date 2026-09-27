import Submission.Work.EKLC6Core.Growth
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLC6Core.trivial_ae_dichotomy
import Submission.Work.EKLC6Core.acovariant_of_leafwise
import Submission.Work.EKLC6Core.growth_pos_of_nontrivial
import Submission.Work.EKLC6Core.exists_desc_subordinate
import Submission.Work.EKLC6Core.growth_integral_sup
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLCompLeaf.fixRadon
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.Assembly` — assembling `P_EntropyLeaf` from its components

This module carries the assembly of component C6 (the main argument, as opposed to the
supporting lemmas).  It is written against the frozen component `Prop`s:

* `P_Leafwise` (C5) — the leaf-wise measures, their existence (first half) and U3/U7 (second
  half), extracted in `Growth.crossSection_iff_dirac_of_leafwise` and `acovariant_of_leafwise`;
* `P_Product` (C5b) — used inside the delegated `growth_integral_sup`;
* `ent_ge_growth` (this development) — `ofReal (∫ growthFun U ν t) ≤ ent μ (aDiag t ·)` for a
  contracted `aDiag t`-normalised `U` (Pisa 7.6(ii) + 7.34 + 7.40); it is being proved in
  `EKLC6Core/ent_ge_growth.lean` and is packaged here as the hypothesis `EntGeGrowth`.
* the integrability of the entropy contribution, packaged as `IntegrableGrowth`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The inequality `ofReal (∫ growthFun (Uij) ν t) ≤ ent μ (aDiag t ·)` of Pisa
7.6(ii)+7.34+7.40, **for a contracted root group** `Uij` (`t i < t j`) and an `A`-ergodic `μ`.

This is the form consumed by `ent_pos_of_not_crossSection` (`⇐` direction of `P_EntropyLeaf`) and
it is the statement proved here: the `U = Uminus t` case (Pisa 7.6(ii)) is
`EKLC6Core.ent_ge_growth_uminus`, and the passage from `Uminus t` down to a single root group is
the additivity `EKLC6Core.growth_integral_le_uminus`. -/
def EntGeGrowth : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ → ∀ (t : Fin 3 → ℝ),
    ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j →
    ∀ (ν : X3 → Measure SL3) (X' X'' : Set X3),
      IsLeafwise μ (Uij hij) ν X' → ACovariant ν X'' → μ (X''ᶜ) = 0 →
      Measurable (growthFun (Uij hij) ν t) → Integrable (growthFun (Uij hij) ν t) μ →
      ENNReal.ofReal (∫ x, growthFun (Uij hij) ν t x ∂μ) ≤ ent μ (fun x : X3 => aDiag t • x)

/-- Integrability of the entropy contribution; discharged in the final assembly from the
finiteness of the entropy (component C4b), see `PLAN.md`. -/
def IntegrableGrowth (μ : Measure X3) (U : Subgroup SL3) (t : Fin 3 → ℝ) : Prop :=
  ∀ (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ U ν X' →
    Integrable (growthFun U ν t) μ

/-- Integrability of the entropy contribution, for the full stable horospherical subgroup and for
every contracted root group.  This is a *theorem* about the leaf-wise systems (Pisa 7.6/7.18:
the entropy contribution `D_μ(a,U)` is finite); in the workspace it is
`EKLC6Core.integrable_growthFun_uminus` for `U = Uminus t`, and the root-group cases follow from
the additivity `EKLC6Core.growth_integral_le_uminus`. -/
def IntegrableGrowthAll : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ → ∀ t : Fin 3 → ℝ,
    IntegrableGrowth μ (Uminus t) t ∧
      ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j → IntegrableGrowth μ (Uij hij) t

/-- **The `⇐` direction of `P_EntropyLeaf`**: a contracted root group that is not a
cross-section forces positive entropy.  This is the direction consumed by the `k = 3` case
analysis of the glue. -/
theorem ent_pos_of_not_crossSection (hge : EntGeGrowth) (hLeaf : P_Leafwise)
    (μ : Measure X3) [IsProbabilityMeasure μ] (hErg : IsAErgodic μ)
    (t : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j) (hlt : t i < t j)
    (hint : IntegrableGrowth μ (Uij hij) t)
    (hcs : ¬ CrossSection μ (Uij hij)) :
    0 < ent μ (fun x : X3 => aDiag t • x) := by
  have hAinv : IsAInvariant μ := hErg.1
  have hHoro : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  obtain ⟨t0, ht0⟩ := hHoro.2.2
  have hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hAinv t0
  obtain ⟨ν, X', hL⟩ := (hLeaf μ (Uij hij) hHoro t0 hmp ht0).1
  obtain ⟨hL', hfin⟩ := Work.EKLCompLeaf.fixRadon hL
  set ν' : X3 → Measure SL3 := Work.EKLComp.fixRadon ν X' with hν'def
  obtain ⟨X'', -, -, hX''null, hcov⟩ :=
    acovariant_of_leafwise hLeaf hAinv hHoro hL'
  -- U3 of `P_Leafwise`: not a cross-section means not trivial a.e.
  have hU3 := crossSection_iff_dirac_of_leafwise hLeaf hAinv hHoro hL'
  have hnotd : ¬ (∀ᵐ x ∂μ, ν' x = Measure.dirac 1) := fun h => hcs (hU3.mpr h)
  have hntriv : ∀ᵐ x ∂μ, ν' x ≠ Measure.dirac 1 := by
    rcases trivial_ae_dichotomy hL' hHoro hcov hX''null hErg with h | h
    · exact absurd h hnotd
    · exact h
  have hmeas : Measurable (growthFun (Uij hij) ν' t) := by
    unfold growthFun
    exact ((measurable_growthFun hL' hfin hHoro t).log).neg
  have hint' : Integrable (growthFun (Uij hij) ν' t) μ := hint _ _ hL'
  have hpos : 0 < ∫ x, growthFun (Uij hij) ν' t x ∂μ :=
    growth_pos_of_nontrivial hL' hHoro hcov hX''null t
      (tendsto_conj_mem_Uij t hij hlt) hAinv hntriv hmeas hint'
  have hbound := hge μ hErg t i j hij hlt ν' X' X'' hL' hcov hX''null hmeas hint'
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) hbound

/-- The **equality case** of Pisa 7.6(ii) for the full stable horospherical subgroup `Uminus t`
(Pisa 7.43): `ent μ (aDiag t ·) ≤ ofReal (∫ growthFun (Uminus t) ν t)`.  Being proved in
`EKLC6Core/ent_le_growth.lean`. -/
def EntLeGrowth : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ] (ν : X3 → Measure SL3) (X' X'' : Set X3)
    (t : Fin 3 → ℝ), IsAErgodic μ → IsLeafwise μ (Uminus t) ν X' →
    ACovariant ν X'' → μ (X''ᶜ) = 0 →
    Measurable (growthFun (Uminus t) ν t) → Integrable (growthFun (Uminus t) ν t) μ →
    ent μ (fun x : X3 => aDiag t • x) ≤
      ENNReal.ofReal (∫ x, growthFun (Uminus t) ν t x ∂μ)

/-- The case analysis that reduces the entropy contribution of the full stable horospherical
subgroup to a single contracted root group; being proved in `EKLC6Core/factor_growth_pos.lean`
out of `growth_integral_sup` (R2) and the shape lemmas `uminus_eq_three` etc. -/
def FactorGrowthPos : Prop :=
  ∀ (hLeaf : P_Leafwise) (hprod : P_Product) (μ : Measure X3) [IsProbabilityMeasure μ],
    IsAErgodic μ → ∀ (t : Fin 3 → ℝ) (ν : X3 → Measure SL3) (X' X'' : Set X3),
    IsLeafwise μ (Uminus t) ν X' → ACovariant ν X'' → μ (X''ᶜ) = 0 →
    Integrable (growthFun (Uminus t) ν t) μ →
    (∀ (i j : Fin 3) (hij : i ≠ j), t i < t j → IntegrableGrowth μ (Uij hij) t) →
    0 < ∫ x, growthFun (Uminus t) ν t x ∂μ →
    ∃ (i j : Fin 3) (hij : i ≠ j) (_ : t i < t j),
      ∃ (νij : X3 → Measure SL3) (Xij : Set X3),
        IsLeafwise μ (Uij hij) νij Xij ∧ 0 < ∫ x, growthFun (Uij hij) νij t x ∂μ

/-- **The `⇒` direction of `P_EntropyLeaf`**: positive entropy of a diagonal element forces some
contracted root group to be a non-cross-section. -/
theorem crossSection_of_ent_pos (hle : EntLeGrowth) (hfp : FactorGrowthPos)
    (hLeaf : P_Leafwise) (hprod : P_Product)
    (μ : Measure X3) [IsProbabilityMeasure μ] (hErg : IsAErgodic μ) (t : Fin 3 → ℝ)
    (hintU : IntegrableGrowth μ (Uminus t) t)
    (hintf : ∀ (i j : Fin 3) (hij : i ≠ j), t i < t j → IntegrableGrowth μ (Uij hij) t)
    (hent : 0 < ent μ (fun x : X3 => aDiag t • x)) :
    ∃ (i j : Fin 3) (hij : i ≠ j), t i < t j ∧ ¬ CrossSection μ (Uij hij) := by
  have hAinv : IsAInvariant μ := hErg.1
  have hHoro : IsHoro (Uminus t) := (uminus_isHoro t).1
  obtain ⟨t0, ht0⟩ := hHoro.2.2
  have hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hAinv t0
  obtain ⟨ν, X', hL⟩ := (hLeaf μ (Uminus t) hHoro t0 hmp ht0).1
  obtain ⟨hL', hfin⟩ := Work.EKLCompLeaf.fixRadon hL
  set ν' : X3 → Measure SL3 := Work.EKLComp.fixRadon ν X' with hν'def
  obtain ⟨X'', -, -, hX''null, hcov⟩ :=
    acovariant_of_leafwise hLeaf hAinv hHoro hL'
  have hmeas : Measurable (growthFun (Uminus t) ν' t) := by
    unfold growthFun
    exact ((measurable_growthFun hL' hfin hHoro t).log).neg
  have hintU' : Integrable (growthFun (Uminus t) ν' t) μ := hintU _ _ hL'
  have hbound := hle μ ν' X' X'' t hErg hL' hcov hX''null hmeas hintU'
  have hpos : 0 < ∫ x, growthFun (Uminus t) ν' t x ∂μ :=
    ENNReal.ofReal_pos.mp (lt_of_lt_of_le hent hbound)
  obtain ⟨i, j, hij, hlt, νij, Xij, hLij, hposij⟩ :=
    hfp hLeaf hprod μ hErg t ν' X' X'' hL' hcov hX''null hintU' hintf hpos
  refine ⟨i, j, hij, hlt, ?_⟩
  intro hcs
  have hU3 := crossSection_iff_dirac_of_leafwise hLeaf hAinv (Lemmas.isHoro_Uij hij) hLij
  have htriv : ∀ᵐ x ∂μ, νij x = Measure.dirac 1 := hU3.mp hcs
  have hzero : ∫ x, growthFun (Uij hij) νij t x ∂μ = 0 := by
    have hae : growthFun (Uij hij) νij t =ᵐ[μ] fun _ : X3 => (0 : ℝ) :=
      htriv.mono fun x hx => growthFun_eq_zero_of_eq_dirac (Lemmas.isHoro_Uij hij) t x hx
    rw [integral_congr_ae hae, integral_zero]
  rw [hzero] at hposij
  exact lt_irrefl _ hposij

/-- **Component C6, assembled from its two directions.**  This is the shape of the requested
`prove_EntropyLeaf`: unconditional in `μ`, `t`, with the component `Prop`s (`P_Leafwise`,
`P_Product`) and the two delegated inequalities (Pisa 7.6(ii)+7.34+7.40 and Pisa 7.43) as
hypotheses, together with the integrability of the entropy contribution. -/
theorem P_EntropyLeaf_of_components (hge : EntGeGrowth) (hle : EntLeGrowth)
    (hfp : FactorGrowthPos) (hLeaf : P_Leafwise) (hprod : P_Product)
    (hint : IntegrableGrowthAll) :
    P_EntropyLeaf := by
  intro μ hμ hErg t
  haveI := hμ
  refine ⟨fun hent => ?_, fun h => ?_⟩
  · exact crossSection_of_ent_pos hle hfp hLeaf hprod μ hErg t (hint μ hErg.1 t).1
      (hint μ hErg.1 t).2 hent
  · obtain ⟨i, j, hij, hlt, hcs⟩ := h
    exact ent_pos_of_not_crossSection hge hLeaf μ hErg t hij hlt
      ((hint μ hErg.1 t).2 i j hij hlt) hcs

end Work.EKLC6Core

end
