import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_uij
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.haar_uminus_data_right_scaling_ge_one
import Submission.Work.EKLC6Core.lintegral_growthFun_le_exists_bound_uminus

/-!
# `EKLC6Core.lintegral_growthFun_le_exists_bound_uminus_meas`

Uniform finiteness of the entropy contribution of the full contracted horospherical subgroup
`U⁻(t) = Uminus t`, in the `ℝ≥0∞` form

`∫⁻ x, ofReal (growthFun (Uminus t) ν t x) ∂μ ≤ C`

for a constant `C` depending only on `t`, uniformly over all `aDiag t`-invariant probabilities
`μ`, all leaf-wise systems `ν` for `Uminus t`, and all conull `aDiag t`-decreasing plaque
algebras `A`.  This is Pisa 7.18/7.34 (the entropy contribution of a contracted horospherical
subgroup is finite), in the form needed by the `condExpKernel` fibre argument
(`Work.EKLC6Core.integrable_growthFun_uminus_of_leafwise`).

## The chain

Writing `U = Uminus t`, `T x = aDiag t • x` and `B = comap T A`,

`∫⁻ ofReal (growthFun U ν t) ≤ ∫⁻ ofReal (atomInfo A U ν t) ≤ HcondSig μ A B ≤ C`,

* `lintegral_growthFun_le_lintegral_atomInfo_horo` — the coboundary form of the shape
  comparison of Pisa 7.34/7.35 (its finiteness hypothesis is supplied by the next step);
* `lintegral_atomInfo_le_nocov` — Pisa 7.35: the pointwise atom information is dominated by the
  σ-algebra conditional entropy, through the atom-conditional probabilities;
* `hcondSig_le_ofReal_log_scaling` — Pisa 7.9/§7.55: the Gibbs inequality for the countably
  generated plaque algebra `A`, compared against the Haar measure of `U⁻(t)`, whose conjugation
  modulus under `aDiag (-t)` is the constant `c ≥ 1` supplied by
  `haar_uminus_data_right_scaling_ge_one`.  This is the part of the argument in which the
  potential `log (mU (shape A U ·))` is a one-sided coboundary, so that
  `lintegral_ofReal_shift_sub_le_ae` bounds its `∫⁻` by `ofReal (log c)`.

The generic one-step reduction of the last inequality to a uniform bound on `HcondSig` is
recorded as `lintegral_growthFun_le_bound_of_HcondSig_bound` below.
-/

namespace Work.EKLC6Core

open MeasureTheory
open scoped ENNReal

open Work.EKLContract

/-- **The reduction.**  A uniform bound on the σ-algebra conditional entropy
`HcondSig μ A (comap (aDiag t ·) A)` over conull `aDiag t`-decreasing plaque algebras `A` of
`U⁻(t) = Uminus t` gives the uniform bound on the entropy contribution. -/
theorem lintegral_growthFun_le_bound_of_HcondSig_bound (t : Fin 3 → ℝ) {C : ENNReal}
    (hCfin : C < ⊤)
    (hC : ∀ (μ : MeasureTheory.Measure Work.EKLContract.X3),
      MeasureTheory.IsProbabilityMeasure μ →
      MeasureTheory.MeasurePreserving
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ →
      ∀ {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3},
        Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A →
        μ Zᶜ = 0 →
        MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A →
        @Work.EKLC6Core.HcondSig Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ A
          (MeasurableSpace.comap
            (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) ≤ C) :
    (∀ (μ : MeasureTheory.Measure Work.EKLContract.X3),
      MeasureTheory.IsProbabilityMeasure μ →
      MeasureTheory.MeasurePreserving
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ →
      ∀ {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
        {X' : Set Work.EKLContract.X3},
        Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X' →
      ∀ {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3},
        Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A →
        μ Zᶜ = 0 →
        MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A →
        @Measurable Work.EKLContract.X3 ℝ Work.EKLContract.instMeasurableSpaceX3
          Real.measurableSpace
          (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) →
        @MeasureTheory.lintegral Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ
          (fun x => ENNReal.ofReal
            (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x)) ≤ C) := by
  intro μ hμ hmp ν X' hL A Z hplq hZ hdec hmeas
  haveI := hμ
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr := (uminus_isHoro t).2
  have hsig := hC μ ‹MeasureTheory.IsProbabilityMeasure μ› hmp hplq hZ hdec
  have hatom : @MeasureTheory.lintegral Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (fun x => ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x))
      ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) :=
    lintegral_atomInfo_le_nocov t hL hU hmp hplq hdec hZ
  have hfin : @MeasureTheory.lintegral Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (fun x => ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_of_lt (lt_of_le_of_lt (hatom.trans hsig) hCfin)) le_rfl
  exact (lintegral_growthFun_le_lintegral_atomInfo_horo (μ := μ) (U := Uminus t) t hU hcontr
    hmp hL hmeas hplq hdec hZ hfin).trans (hatom.trans hsig)

theorem lintegral_growthFun_le_exists_bound_uminus_meas (t : Fin 3 → ℝ) :
    ∃ C : ENNReal, C < ⊤ ∧
      (∀ (μ : MeasureTheory.Measure Work.EKLContract.X3),
        MeasureTheory.IsProbabilityMeasure μ →
        MeasureTheory.MeasurePreserving
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ →
        ∀ {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
          {X' : Set Work.EKLContract.X3},
          Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X' →
        ∀ {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3},
          Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A →
          μ Zᶜ = 0 →
          MeasurableSpace.comap
            (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A →
          @Measurable Work.EKLContract.X3 ℝ Work.EKLContract.instMeasurableSpaceX3
            Real.measurableSpace
            (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) →
          @MeasureTheory.lintegral Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ
            (fun x => ENNReal.ofReal
              (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x)) ≤ C) := by
  obtain ⟨mU, c, hc1, hctop, hcar, hposm, hfinm, hri, hscale⟩ :=
    haar_uminus_data_right_scaling_ge_one t
  refine ⟨ENNReal.ofReal (Real.log c.toReal), ENNReal.ofReal_lt_top, ?_⟩
  intro μ hμ hmp ν X' hL A Z hplq hZ hdec hmeas
  haveI := hμ
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (uminus_isHoro t).2
  have hsig : @Work.EKLC6Core.HcondSig Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ A
      (MeasurableSpace.comap
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
      ≤ ENNReal.ofReal (Real.log c.toReal) :=
    hcondSig_le_ofReal_log_scaling t hmp hL hplq hZ hdec hposm hcar hfinm hri hscale hc1 hctop
  have hatom : @MeasureTheory.lintegral Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (fun x => ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x))
      ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) :=
    lintegral_atomInfo_le_nocov t hL hU hmp hplq hdec hZ
  have hfin : @MeasureTheory.lintegral Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (fun x => ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (hatom.trans hsig) ENNReal.ofReal_lt_top)
  exact (lintegral_growthFun_le_lintegral_atomInfo_horo (μ := μ) (U := Uminus t) t hU hcontr
    hmp hL hmeas hplq hdec hZ hfin).trans (hatom.trans hsig)

end Work.EKLC6Core
