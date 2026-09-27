import Mathlib
import Submission.Work.EKLC6Core.Growth
import Submission.Work.EKLC6Core.box_conjBox_subset

namespace Work.EKLC6Core

open MeasureTheory
open scoped ENNReal

/-- **The entropy contribution is a non-negative observable.**

For a root group `Uij` (`i ≠ j`) contracted by `aDiag t`, i.e. `t i < t j`, the `ij`-box
`conjBox (Uij hij) t` — the `aDiag t`-contraction of the normalising box `B₁^{Uij}`, which for
`i ≠ j`, `t i < t j` is the small interval `u_ij([-λ,λ])`, `λ = e^{t i - t j} < 1` — is contained
in `B₁^{Uij}` (`Work.EKLC6Core.box_conjBox_subset`, applied to the contraction
`Work.EKLC6Core.tendsto_conj_mem_Uij`).  Since a leaf-wise system is normalised by
`ν x (B₁^{Uij}) = 1` on the conull set `X'`, we get `ν x (conjBox (Uij hij) t) ≤ 1` there, hence
`growthFun (Uij hij) ν t x = -log ((ν x (conjBox (Uij hij) t)).toReal) ≥ 0` a.e.; the integral of
an a.e. non-negative function is non-negative.

This is the pointwise-positivity half of the fact that the Birkhoff average of `growthFun` is the
entropy contribution `D_μ(a,Uij)` of Pisa 7.6/7.18, whose positivity feeds the equivalence
`0 < ent μ (aDiag t ·) ↔ ∃ i j, t i < t j ∧ ¬ CrossSection μ (Uij ·)`. -/
theorem growthFun_integral_nonneg_Uij {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    {i j : Fin 3} (hij : i ≠ j) (hlt : t i < t j)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X') :
    0 ≤ ∫ x, Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) ν t x ∂μ := by
  have hU : Work.EKLContract.IsHoro (Work.EKLContract.Uij hij) :=
    Work.EKLContract.Lemmas.isHoro_Uij hij
  have hcontr := Work.EKLC6Core.tendsto_conj_mem_Uij t hij hlt
  have hsub : Work.EKLC6Core.conjBox (Work.EKLContract.Uij hij) t ⊆
      Work.EKLContract.Box1 (Work.EKLContract.Uij hij) :=
    (Work.EKLC6Core.box_conjBox_subset hU hcontr).1
  -- `X'` is conull, and on `X'` the leaf-wise measures are normalised on `B₁^{Uij}`.
  have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff]
    exact hL.conull
  refine MeasureTheory.integral_nonneg_of_ae ?_
  show ∀ᵐ x ∂μ, 0 ≤ Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) ν t x
  filter_upwards [hmem] with x hx
  have hle : ν x (Work.EKLC6Core.conjBox (Work.EKLContract.Uij hij) t) ≤ 1 := by
    calc ν x (Work.EKLC6Core.conjBox (Work.EKLContract.Uij hij) t)
        ≤ ν x (Work.EKLContract.Box1 (Work.EKLContract.Uij hij)) :=
          MeasureTheory.measure_mono hsub
      _ = 1 := hL.normalised x hx
  have hle' : (ν x (Work.EKLC6Core.conjBox (Work.EKLContract.Uij hij) t)).toReal ≤ 1 := by
    calc (ν x (Work.EKLC6Core.conjBox (Work.EKLContract.Uij hij) t)).toReal
        ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := by simp
  have hlog : Real.log ((ν x (Work.EKLC6Core.conjBox (Work.EKLContract.Uij hij) t)).toReal) ≤ 0 :=
    Real.log_nonpos ENNReal.toReal_nonneg hle'
  simp only [Work.EKLC6Core.growthFun]
  linarith

end Work.EKLC6Core
