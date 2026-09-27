import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.lintegral_growthFun_le_exists_bound_uminus
import Submission.Work.EKLC6Core.haar_uminus_data_right_scaling_ge_one
import Submission.Work.EKLRelCross.leafwise_exists
import Submission.Work.EKLComp.prove_X3

set_option linter.style.haveILetI false

namespace Work.EKLC6Core

open MeasureTheory
open scoped ENNReal

open Work.EKLContract

/-- **Pisa 7.9/§7.55, uniform form.** For every `t : Fin 3 → ℝ` there is a finite constant `C`
(depending only on `t`) such that for every `aDiag t`-invariant probability `μ` and every conull
`aDiag t`-decreasing `U⁻(t)`-plaque algebra `A`, the σ-algebra conditional entropy
`HcondSig μ A (comap (aDiag t ·) A)` is at most `C`.

The constant is the logarithm of the conjugation modulus `c` of the Haar measure of `U⁻(t)`
(`haar_uminus_data_right_scaling_ge_one`); the leaf-wise system used in the Gibbs comparison is
produced by `Work.EKLRelCross.leafwise_exists` (Pisa 6.3) from the invariance of `μ` alone. -/
theorem HcondSig_uminus_uniform_bound (t : Fin 3 → ℝ) :
    ∃ C : ENNReal, C < ⊤ ∧
      (∀ (μ : MeasureTheory.Measure Work.EKLContract.X3),
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
              (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) ≤ C) := by
  obtain ⟨mU, c, hc1, hctop, hcar, hposm, hfinm, hri, hscale⟩ :=
    haar_uminus_data_right_scaling_ge_one t
  refine ⟨ENNReal.ofReal (Real.log c.toReal), ENNReal.ofReal_lt_top, ?_⟩
  intro μ hμ hmp A Z hplq hZ hdec
  haveI := hμ
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (uminus_isHoro t).2
  obtain ⟨ν, X', hL⟩ :=
    Work.EKLRelCross.leafwise_exists Work.EKLComp.prove_X3 μ (Uminus t) hU t hmp hcontr
  exact hcondSig_le_ofReal_log_scaling t hmp hL hplq hZ hdec hposm hcar hfinm hri hscale hc1 hctop

end Work.EKLC6Core
