import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.box_conjBox_subset

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-- **The entropy contribution is non-negative.**  For a horospherical subgroup `U` contracted by
the flow `aDiag t` (`hcontr`), and a leaf-wise system `ν` over the probability measure `μ`
normalised by `ν x (B₁^U) = 1` (`IsLeafwise.normalised`), the pointwise information

`growthFun U ν t x = -log (ν x (conjBox U t))`

is non-negative `μ`-almost everywhere.

The only input is the sandwich `conjBox U t ⊆ B₁^U` of `box_conjBox_subset`: the contracting
conjugation shrinks the normalising box into itself, so

`ν x (conjBox U t) ≤ ν x (B₁^U) = 1`  for `x ∈ X'`,

whence `(ν x (conjBox U t)).toReal ≤ 1`, `log · ≤ 0` and `growthFun U ν t x ≥ 0`.  The domain
`X'` is conull (`IsLeafwise.conull`), which is what makes the statement hold `μ`-a.e. rather than
merely on `X'`.

This is the reason the entropy contribution `D_μ(a,U) = lim_n (1/n) log ν x (a^{-n} B₁^U a^n)`
(Pisa 7.6/7.18) is a limit of non-negative Birkhoff averages. -/
theorem ae_nonneg_growthFun_of_contracted
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hU : Work.EKLContract.IsHoro U)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    0 ≤ᵐ[μ] Work.EKLC6Core.growthFun U ν t := by
  -- the contracted box is trapped in the normalising box `B₁^U`
  have hsub : conjBox U t ⊆ Box1 U := (box_conjBox_subset hU hcontr).1
  -- the leaf-wise domain `X'` is conull
  have hmem : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff]
    exact hL.conull
  filter_upwards [hmem] with x hx
  have hle1 : ν x (conjBox U t) ≤ 1 := by
    calc ν x (conjBox U t) ≤ ν x (Box1 U) := measure_mono hsub
      _ = 1 := hL.normalised x hx
  have hle1' : (ν x (conjBox U t)).toReal ≤ 1 :=
    le_trans (ENNReal.toReal_mono (by simp) hle1) (by simp)
  have hlog : Real.log ((ν x (conjBox U t)).toReal) ≤ 0 :=
    Real.log_nonpos ENNReal.toReal_nonneg hle1'
  show (0 : ℝ) ≤ -Real.log ((ν x (conjBox U t)).toReal)
  exact neg_nonneg.mpr hlog

end Work.EKLC6Core
