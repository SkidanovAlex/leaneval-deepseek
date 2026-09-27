import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_single_t
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.ent_ge_HcondSig_le
import Submission.Work.EKLC6Core.exists_gen_plaque_data
import Submission.Work.EKLC6Core.ent_le_growth_single_t
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.conull_cut_exposed
import Submission.Work.EKLC6Core.lintegral_le_of_condKernel_bound
import Submission.Work.EKLC6Core.lintegral_growthFun_le_exists_bound_uminus_meas
import Submission.Work.EKLC6Core.HcondSig_uminus_uniform_bound

/-!
# `Work.EKLC6Core.growthFun_lintegral_lt_top_of_gen_data`

Finiteness of the entropy contribution of the stable horospherical subgroup `U⁻(t) = Uminus t`
of `aDiag t` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, for an arbitrary (not necessarily ergodic)
`aDiag t`-invariant probability `μ`:

`∫⁻ x, ofReal (growthFun (Uminus t) ν t x) ∂μ < ⊤`.

## The argument

**Step 1 (uniform bound).**  `Work.EKLC6Core.HcondSig_uminus_uniform_bound` (Pisa 7.9/§7.55: the
σ-algebra conditional entropy of a conull `aDiag t`-descending `U⁻(t)`-plaque algebra is bounded
by the logarithm of the conjugation modulus of the Haar measure of `U⁻(t)`, uniformly in `μ`) feeds
`Work.EKLC6Core.lintegral_growthFun_le_bound_of_HcondSig_bound` (Pisa 7.18/7.34 followed by
Pisa 7.35), which yields a constant `C < ⊤` with

`∫⁻ x, ofReal (growthFun (Uminus t) ν t x) ∂κ ≤ C`

for *every* `aDiag t`-invariant probability `κ`, every leaf-wise system `ν` for `U⁻(t)`, and every
**conull** `aDiag t`-descending `U⁻(t)`-plaque algebra.

**Step 2 (conull plaque algebra).**  `Work.EKLC6Core.conull_cut_exposed` (Pisa 7.37/7.38, the cut
construction) supplies such a plaque algebra for every `aDiag t`-**quasi-ergodic** `κ`.

**Step 3 (ergodic decomposition).**  For a general `μ` this is the Jacobs step, in the form used by
`Work.EKLC6Core.ent_le_growth_fiber_along_single_t`:

* for `μ`-a.e. `x` the conditional measure `κ x = condExpKernel μ (invariants T) x` of the
  invariant σ-algebra is again `T`-invariant (`Work.EKLEntJacobs.fiber_inv`) and quasi-ergodic
  (`Work.EKLC6Core.condExpKernel_quasiErgodic`);
* the *same* `ν` is a leaf-wise system for `κ x` a.e. (`Work.EKLC6Core.fiber_leafwise_along`,
  Pisa 7.23), and the covariance hypothesis is a pointwise statement, so it transfers as soon as
  `κ x X''ᶜ = 0` (`Work.EKLC6Core.condExpKernel_eq_zero_of_null_single_t`);
* hence the fibre integrals are bounded by `C` for a.e. `x`, and the disintegration identity
  `∫⁻ y, F y ∂μ = ∫⁻ x, ∫⁻ y, F y ∂(κ x) ∂μ`
  (`Work.EKLC6Core.lintegral_le_of_condKernel_bound`) turns the uniform fibre bound into the bound
  `C` for `μ` itself.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure Work.EKLContract.X3}

/-! ## The target -/

theorem growthFun_lintegral_lt_top_of_gen_data
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t)) :
    ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x) ∂μ < ⊤ := by
  haveI : StandardBorelSpace Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.2.2
  -- Step 1: the uniform bound (Pisa 7.9 + 7.18/7.34, uniform in the measure)
  obtain ⟨C, hCfin, hCsig⟩ := HcondSig_uminus_uniform_bound t
  have hBound := lintegral_growthFun_le_bound_of_HcondSig_bound t hCfin hCsig
  let T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag t • x
  let κ : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.X3 :=
    fun x => condExpKernel μ (MeasurableSpace.invariants T) x
  have hT : Measurable T := (continuous_const_smul (Work.EKLContract.aDiag t)).measurable
  have hU : IsHoro (Work.EKLC6Core.Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Work.EKLC6Core.Uminus t, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1) := (uminus_isHoro t).2
  -- Step 3a: `X''` is conull for a.e. fibre
  have hX''fib : ∀ᵐ x ∂μ, κ x (X''ᶜ) = 0 := by
    obtain ⟨B, hXB, hBmeas, hB0⟩ := MeasureTheory.exists_measurable_superset_of_null hX''
    filter_upwards [condExpKernel_eq_zero_of_null_single_t (μ := μ) hT hmp hBmeas hB0] with x hx
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hXB) (le_of_eq hx)) bot_le
  -- Steps 2 and 3b: the uniform fibre bound
  have hfib : ∀ᵐ x ∂μ, ∫⁻ y,
      ENNReal.ofReal (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t y) ∂(κ x) ≤ C := by
    filter_upwards [Work.EKLEntJacobs.fiber_inv μ T hT hmp,
      condExpKernel_quasiErgodic μ T hT hmp,
      fiber_leafwise_along (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hmp hL hcov hX'',
      hX''fib] with x hinv hqerg hLx hX''x
    obtain ⟨M, Q, Z, -, -, hplq, hZ, hdec⟩ := conull_cut_exposed (μ := κ x) hU t hinv hcontr hqerg
    exact hBound (κ x) (ProbabilityTheory.IsMarkovKernel.is_probability_measure' x) hinv hLx
      hplq hZ hdec hmeas
  -- Step 3c: integrate the uniform fibre bound (disintegration identity for the kernel)
  exact lt_of_le_of_lt (lintegral_le_of_condKernel_bound t _
    hmeas.ennreal_ofReal.aemeasurable C hfib) hCfin

end Work.EKLC6Core
