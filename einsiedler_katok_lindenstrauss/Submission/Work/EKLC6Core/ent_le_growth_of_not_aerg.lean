import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.ent_jacobs
import Submission.Work.EKLEntJacobs.fiber_inv
import Submission.Work.EKLC6Core.ent_le_growth_fiber

/-!
# `Work.EKLC6Core.ent_le_growth_of_not_aerg` — Pisa 7.6(ii)-equality, integrated

For a probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by `T = (aDiag t ·)`, with `μ` `A`-ergodic
and with `T` *not* ergodic, and a leaf-wise system `ν` for the full contracted horospherical
subgroup `Uminus t = G⁻(t)`, one has

  `ent μ T ≤ ofReal (∫ growthFun (Uminus t) ν t dμ)`.

This is the non-`T`-ergodic case of Pisa Theorem 7.6(ii) (the equality `h_μ(a) = h_μ(a,G⁻)`),
integrated.  The hypothesis `haerg` is in fact not needed: the argument is the *`a`-ergodic
reduction* of Pisa 7.19–7.24, which passes through the ergodic decomposition of the system.

## The argument

Write `T = (aDiag t ·)`, `𝒥 = invariants T` and `κ x = condExpKernel μ 𝒥 x` (the ergodic
component of `μ` through `x`).

1. **Jacobs' theorem** (`Work.EKLComp.ent_jacobs`):
   `ent μ T = ∫⁻ x, ent (κ x) T ∂μ`.
2. **The fibres are ergodic** (`condExpKernel_quasiErgodic`), `T`-invariant (`fiber_inv`) and
   carry `ν` as a leaf-wise system (`fiber_leafwise`, Pisa 7.22).
3. **The `T`-ergodic case** (`ent_le_growth_of_aerg`, Pisa 7.6(ii) with equality):
   `ent (κ x) T ≤ ofReal (∫ y, growthFun (Uminus t) ν t y ∂(κ x))`.
4. **Non-negativity**: `conjBox (Uminus t) t ⊆ Box1 (Uminus t)` (`box_conjBox_subset`), so
   `growthFun (Uminus t) ν t ≥ 0` on `X'`; since `X'` is a.e. `κ x`-conull, the inner integrals
   are `≥ 0` a.e.
5. **The mean of the fibre integrals** is `∫ growthFun dμ`, by
   `condExp_ae_eq_integral_condExpKernel` and `integral_condExp`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- If `B` is `μ`-null, then the conditional measures of the invariant σ-algebra of a
measure-preserving `T` vanish on `B` almost everywhere. -/
private theorem condExpKernel_eq_zero_of_null {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace X3]
    {T : X3 → X3} (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    {B : Set X3} (hBmeas : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B = 0 := by
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace X3) :=
    MeasurableSpace.invariants_le T
  have hind : B.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] (0 : X3 → ℝ) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine le_antisymm ?_ bot_le
    refine le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hB0)
    intro x hx
    by_contra hxc
    exact hx (by simp [Set.indicator_of_notMem hxc])
  have h2 : μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] =ᵐ[μ]
      (0 : X3 → ℝ) := by
    have h := MeasureTheory.condExp_congr_ae (μ := μ) (m := MeasurableSpace.invariants T) hind
    rwa [MeasureTheory.condExp_zero] at h
  have hreal : (fun x => (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x).real B)
      =ᵐ[μ] (0 : X3 → ℝ) :=
    (ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
      (m := MeasurableSpace.invariants T) hm hBmeas).trans h2
  filter_upwards [hreal] with x hx
  haveI : IsProbabilityMeasure (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.is_probability_measure' x
  have hfin : ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ B)) ?_
    rw [MeasureTheory.measure_univ]
    exact ENNReal.one_lt_top
  rw [MeasureTheory.measureReal_def] at hx
  rcases (ENNReal.toReal_eq_zero_iff _).mp hx with h | h
  · exact h
  · exact absurd h (ne_of_lt hfin)

/-- **Pisa 7.24** (`a`-ergodic reduction): the entropy of `T = (aDiag t ·)` is bounded by the
integral of the growth function of the full contracted horospherical subgroup, for every
probability `μ` preserved by `T` with a leaf-wise system `ν` for `Uminus t`. -/
theorem ent_le_growth_of_not_aerg {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (haerg : ¬ ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
      μ E = 0 ∨ μ Eᶜ = 0)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≤
      ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  haveI hSB : StandardBorelSpace Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.2.2
  let T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag t • x
  have hTmeas : Measurable T := (continuous_const_smul (Work.EKLContract.aDiag t)).measurable
  have hmp : MeasureTheory.MeasurePreserving T μ μ := hErg.1 t
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace Work.EKLContract.X3) :=
    MeasurableSpace.invariants_le T
  let g : Work.EKLContract.X3 → ℝ := Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t
  let κ : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.X3 :=
    fun x => ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x
  -- 1. Jacobs' theorem
  have hJ : Work.EKLContract.ent μ T = ∫⁻ x, Work.EKLContract.ent (κ x) T ∂μ :=
    Work.EKLComp.ent_jacobs μ T hTmeas hmp
  -- 3. the per-fibre (ergodic-component) bound, Pisa 7.19–7.24
  have hper : ∀ᵐ x ∂μ, Work.EKLContract.ent (κ x) T ≤
      ENNReal.ofReal (∫ y, g y ∂(κ x)) :=
    ent_le_growth_fiber (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hmp hL hcov hX'' hmeas hint
  -- 4. non-negativity of `g` on `X'`
  have hgpt : ∀ y ∈ X', 0 ≤ g y := by
    intro y hy
    have hbox := (Work.EKLC6Core.box_conjBox_subset (Work.EKLC6Core.uminus_isHoro t).1
      (Work.EKLC6Core.uminus_isHoro t).2).1
    have hmono : ν y (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t) ≤
        ν y (Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t)) := MeasureTheory.measure_mono hbox
    have h1 : ν y (Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t)) = 1 := hL.normalised y hy
    have hle1 : (ν y (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal ≤ 1 := by
      rw [h1] at hmono
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmono
    have hge0 : 0 ≤ (ν y (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal :=
      ENNReal.toReal_nonneg
    simp only [g, Work.EKLC6Core.growthFun]
    exact neg_nonneg.mpr (Real.log_nonpos hge0 hle1)
  -- `X'` and `X''` are a.e. conull for the fibres
  have hX'fib : ∀ᵐ x ∂μ, κ x (X'ᶜ) = 0 :=
    condExpKernel_eq_zero_of_null hTmeas hmp hL.meas_dom.compl hL.conull
  have hX''fib : ∀ᵐ x ∂μ, κ x (X''ᶜ) = 0 := by
    obtain ⟨B, hXB, hBmeas, hB0⟩ := MeasureTheory.exists_measurable_superset_of_null hX''
    filter_upwards [condExpKernel_eq_zero_of_null hTmeas hmp hBmeas hB0] with x hx
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hXB) (le_of_eq hx)) bot_le
  let a : Work.EKLContract.X3 → ℝ := fun x => ∫ y, g y ∂(κ x)
  have ha_int : MeasureTheory.Integrable a μ :=
    hint.integral_condExpKernel (m := MeasurableSpace.invariants T)
  have ha_nonneg : 0 ≤ᵐ[μ] a := by
    filter_upwards [hX'fib] with x hx
    refine MeasureTheory.integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂(κ x), 0 ≤ g y
    rw [MeasureTheory.ae_iff]
    have hsub : {y | ¬ 0 ≤ g y} ⊆ X'ᶜ := by
      intro y hy
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_not] at hy ⊢
      by_contra hc
      exact hy (hgpt y hc)
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hx)) bot_le
  have ha_condExp : a =ᵐ[μ] μ[g | MeasurableSpace.invariants T] :=
    (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hm hint).symm
  have ha_eq : ∫ x, a x ∂μ = ∫ x, g x ∂μ := by
    rw [MeasureTheory.integral_congr_ae ha_condExp]
    exact MeasureTheory.integral_condExp (m := MeasurableSpace.invariants T) (μ := μ) hm
  -- 5. put everything together
  calc Work.EKLContract.ent μ T
      = ∫⁻ x, Work.EKLContract.ent (κ x) T ∂μ := hJ
    _ ≤ ∫⁻ x, ENNReal.ofReal (a x) ∂μ := MeasureTheory.lintegral_mono_ae hper
    _ = ENNReal.ofReal (∫ x, a x ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ha_int ha_nonneg).symm
    _ = ENNReal.ofReal (∫ x, g x ∂μ) := by rw [ha_eq]

end Work.EKLC6Core
