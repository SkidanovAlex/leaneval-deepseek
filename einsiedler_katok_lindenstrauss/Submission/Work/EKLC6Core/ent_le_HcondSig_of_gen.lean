import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.PastJoin
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.growth_le_HcondSig_mp
import Submission.Work.EKLC6Core.exists_leafwise_growthFun_measurable
import Submission.Work.EKLC6Core.HcondSigFree.HcondSig_le_lintegral_atomInfo_mp
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_single_t
import Submission.Work.EKLC6Core.ent_le_growth_single_t
import Submission.Work.EKLComp.hPart_eq_ent_of_generating
import Submission.Work.EKLComp.hPart_Hcond
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.ent_le_HcondSig_of_gen` — Pisa 7.40, the one-sided generator inequality

For a probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the single element `T = (aDiag t ·)`,
a conull plaque algebra `A` for the full contracted horospherical subgroup `U = Uminus t`
(`IsPlaqueAlgebra (Uminus t) Z A`, `μ Zᶜ = 0`), `T`-decreasing (`hdec`) and generating for the
inverse flow (`hgen`), the Kolmogorov–Sinai entropy of `T` is bounded by the σ-algebra conditional
entropy `HcondSig μ A (comap T A)`.

## Route (as formalised here)

Write `U = Uminus t` and `T = (aDiag t ·)`.

* `U = ⊥` forces `aDiag t = 1` (`Basic.aDiag_eq_one_of_uminus_eq_bot`), so `T = id` and the
  entropy vanishes (`Basic.ent_aDiag_eq_zero_of_uminus_eq_bot`).

* Otherwise fix a leaf-wise system `ν` for `U` with globally measurable entropy contribution
  (`exists_leafwise_growthFun_measurable`), its conull set of single-`t` covariance
  (`covAlong.acovariantAlong_of_leafwise`) and the pointwise entropy contribution
  `growthFun U ν t x = -log ν x (conjBox U t)`, which is non-negative a.e.
  (`growthFun_uminus_nonneg_gen` below).

  Three published facts about the entropy contribution are used:

  * `ent_le_growth_single_t` (Pisa 7.6(ii), equality case, for a probability preserved by the
    single map `T` and covariance along the integer multiples of `t`):
    `ent μ T ≤ ofReal (∫ growthFun U ν t)`;
  * `integrable_growthFun_uminus_of_leafwise` (Pisa 6.29/7.9, via the cusp estimate): the
    entropy contribution is integrable, so the Bochner integral above is the honest one;
  * `lintegral_growthFun_le_lintegral_atomInfo_single_t` (Pisa 7.18/7.34, the transfer from the
    leaf-wise measure to the conditional measure of the plaque algebra `A`):
    `∫⁻ ofReal (growthFun U ν t) ≤ ∫⁻ ofReal (atomInfo A U ν t)` whenever the right-hand side is
    finite.

  The two clean halves `HcondSigFree.HcondSig_le_lintegral_atomInfo_mp` and
  `lintegral_atomInfo_le_nocov` identify `HcondSig μ A (comap T A)` with
  `∫⁻ ofReal (atomInfo A U ν t)` (Pisa 7.34/7.35 for the given plaque algebra `A`), and
  `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` converts the Bochner integral of the
  non-negative entropy contribution into its `ℝ≥0∞`-valued version.  The case split on whether
  `∫⁻ ofReal (atomInfo A U ν t) = ⊤` makes the finiteness hypothesis of the transfer lemma
  unnecessary.

## Status

The proof below is complete given `ent_le_growth_single_t`, which is on the critical path of the
geometric input of component C6 (Pisa 7.37/7.38 + 7.43: the existence of a *generating* plaque
algebra).  The workspace's current formalisation of that input for a *finite* partition
(`EKLC6Core.exists_finPart_plaquePast_generating`, on which `EKLC6Core.HasPlaquePartition` and
hence `ent_le_growth_single_t` depend) has been declared mis-stated by a prover: the published
theorems produce a *countable* generating plaque algebra, and the finite-partition form is
strictly stronger (centraliser ambiguity: EKL Prop. 9.2).  The countable form (with generation
only modulo `μ`) is delegated as
`EKLC6Core.exists_countable_partition_plaque_past_generating_mp`.

The hypothesis `hgen` is not needed by this route: the comparison with the given plaque algebra
`A` is precisely the statement that `HcondSig μ A (comap T A)` does not depend on the choice of
the subordinate `A` (Pisa 7.34), which is what makes the bound independent of the presentation.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- On the conull domain of a leaf-wise system for the contracted subgroup `Uminus t`, the
contracted box `conjBox (Uminus t) t` is contained in the normalising box `Box1 (Uminus t)`, whose
`ν x`-mass is `1`; hence the entropy contribution `growthFun (Uminus t) ν t` is non-negative
almost everywhere. -/
theorem growthFun_uminus_nonneg_gen {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X') :
    ∀ᵐ x ∂μ, 0 ≤ Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x := by
  have hU : Work.EKLContract.IsHoro (Work.EKLC6Core.Uminus t) :=
    (Work.EKLC6Core.uminus_isHoro t).1
  have hsub : Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t ⊆
      Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t) :=
    (Work.EKLC6Core.box_conjBox_subset hU (Work.EKLC6Core.tendsto_conj_mem_uminus t)).1
  have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff]
    exact hL.conull
  filter_upwards [hmem] with x hx
  have hle : ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t) ≤ 1 := by
    calc ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)
        ≤ ν x (Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t)) :=
          MeasureTheory.measure_mono hsub
      _ = 1 := hL.normalised x hx
  have hle' : (ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal ≤ 1 := by
    calc (ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal
        ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := by simp
  have hlog : Real.log ((ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal) ≤ 0 :=
    Real.log_nonpos ENNReal.toReal_nonneg hle'
  simp only [Work.EKLC6Core.growthFun]
  linarith

theorem ent_le_HcondSig_of_gen {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hgen : (⨆ n : ℕ, MeasurableSpace.comap
        ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • x)^[n]) A)
        = Work.EKLContract.instMeasurableSpaceX3) :
    @Work.EKLContract.ent Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
      ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
          (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) := by
  by_cases hU : Work.EKLC6Core.Uminus t = ⊥
  · -- degenerate case: `T = id`
    rw [Work.EKLC6Core.ent_aDiag_eq_zero_of_uminus_eq_bot t hU]
    exact bot_le
  · obtain ⟨ν, X', hL, hfin, hmeas⟩ :=
      Work.EKLC6Core.exists_leafwise_growthFun_measurable (μ := μ) t hmp
    obtain ⟨X'', hX''sub, hX''meas, hX''null, hcov⟩ :=
      Work.EKLC6Core.acovariantAlong_of_leafwise (μ := μ) t hmp hL
    have hnonneg := growthFun_uminus_nonneg_gen (μ := μ) t hL
    -- `HcondSig μ A (comap T A)` is the `∫⁻`-integral of the pointwise information of `A`
    have hid : @Work.EKLC6Core.HcondSig Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
        = ∫⁻ x, ENNReal.ofReal
            (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ :=
      le_antisymm
        (Work.EKLC6Core.HcondSigFree.HcondSig_le_lintegral_atomInfo_mp (μ := μ) t hmp hL
          hplq hZ hdec)
        (Work.EKLC6Core.lintegral_atomInfo_le_nocov (μ := μ) t hL
          (Work.EKLC6Core.uminus_isHoro t).1 hmp hplq hdec hZ)
    by_cases htop : ∫⁻ x, ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ = ⊤
    · -- the extended information of `A` is infinite, so the conditional entropy is `⊤`
      rw [hid, htop]
      exact le_top
    · -- the extended information is finite: the entropy contribution is integrable
      have hlint : ∫⁻ x, ENNReal.ofReal
          (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x) ∂μ ≠ ⊤ :=
        ne_top_of_le_ne_top htop
          (Work.EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_single_t (μ := μ) t hmp hL
            hcov hX''null hmeas hplq hZ hdec htop)
      have hint : MeasureTheory.Integrable
          (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
          hnonneg).mp hlint
      calc @Work.EKLContract.ent Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ
            (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
          ≤ ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) :=
            Work.EKLC6Core.ent_le_growth_single_t (μ := μ) t hmp hL hcov hX''null hmeas hint
        _ = ∫⁻ x, ENNReal.ofReal
              (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x) ∂μ :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg
        _ ≤ ∫⁻ x, ENNReal.ofReal
              (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ :=
            Work.EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_single_t (μ := μ) t hmp hL
              hcov hX''null hmeas hplq hZ hdec htop
        _ = @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
              (MeasurableSpace.comap
                (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) := hid.symm

end Work.EKLC6Core
