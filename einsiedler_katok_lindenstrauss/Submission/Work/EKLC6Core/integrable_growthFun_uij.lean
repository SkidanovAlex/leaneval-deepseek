import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.Growth
import Submission.Work.EKLC6Core.lintegral_growthFun_le_HcondSig_uij
import Submission.Work.EKLC6Core.HcondSig_le_ofReal_haar_uij_cf
import Submission.Work.EKLC6Core.fiber_leafwise_uij
import Submission.Work.EKLC6Core.aeStronglyMeasurable_growthFun
import Submission.Work.EKLC6Core.desc_plaque_conull_ergodic_pt
import Submission.Work.EKLC6Core.lintegral_le_of_condKernel_bound
import Submission.Work.EKLC6Core.fiber_inv_finite
import Submission.Work.EKLC6Core.condExpKernel_ergodic
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# `Work.EKLC6Core.integrable_growthFun_uij`

`growthFun (Uij hij) ν t` is `μ`-integrable, for `μ` a probability measure on
`X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the single diagonal element `aDiag t` (with `t i < t j`, so
that `Uij hij` is contracted) and `ν` any leaf-wise system for `Uij hij` over `μ`.

## Argument

Everything is reduced to the *`ℝ≥0∞`* (faithful) form of the entropy-contribution bound

    ∫⁻ x, ENNReal.ofReal (growthFun (Uij hij) ν t x) ∂μ ≤ ENNReal.ofReal (t j - t i) =: C   (†)

(Pisa 7.9 for the root group `Uij`; `lintegral_growthFun_le_ofReal_uij`).  The Bochner form
`ofReal (∫ growthFun) ≤ …` would *not* suffice: the Bochner integral of a non-integrable function
is `0` by the junk convention, so a bound on it carries no information exactly in the case we
need.

* *Fibre reduction.*  With `T = (aDiag t ·)` and `κ x := condExpKernel μ (invariants T) x`
  (`μ`-a.e. `x`), the measure `κ x` is `T`-invariant (`fiber_inv_finite`), `T`-ergodic
  (`condExpKernel_ergodic`) and carries `ν` as a leaf-wise system for `Uij`
  (`fiber_leafwise_uij`, Pisa 7.22).  So (†) holds with `μ` replaced by `κ x` a.e., and the
  disintegration identity for the conditional kernel (`lintegral_le_of_condKernel_bound`) upgrades
  the a.e. fibre bound to (†) for `μ`.
* *From (†) to integrability.*  `growthFun (Uij hij) ν t ≥ 0` a.e., since
  `conjBox (Uij hij) t ⊆ Box1 (Uij hij)` and `ν x (Box1 _) = 1` on the conull `X'`; hence
  `HasFiniteIntegral` follows from (†) (replace `‖·‖` by `·` a.e.), and `AEStronglyMeasurable` is
  `aeStronglyMeasurable_growthFun`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The `a.e.` (`T ⁻¹' s =ᵐ s`) form of ergodicity implies the "pointwise off a null set"
form, for a measure-preserving `T`. -/
theorem ae_ergodic_to_pointwise {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] {T : α → α}
    (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (h : ∀ s : Set α, MeasurableSet s → T ⁻¹' s =ᵐ[μ] s → μ s = 0 ∨ μ sᶜ = 0) :
    ∀ s : Set α, MeasurableSet s →
      (∃ N : Set α, μ N = 0 ∧ ∀ x, x ∉ N → x ∈ s → T x ∈ s) → μ s = 0 ∨ μ sᶜ = 0 := by
  intro s hs hpt
  obtain ⟨N, hN0, hN⟩ := hpt
  have hTmeas : Measurable T := hmp.measurable
  have hsm : MeasurableSet (T ⁻¹' s) := hs.preimage hTmeas
  have h1 : μ (s \ T ⁻¹' s) = 0 :=
    measure_mono_null (fun x hx => by
      by_contra hxN
      exact hx.2 (hN x hxN hx.1)) hN0
  have h2 : μ (T ⁻¹' s) = μ s := hmp.measure_preimage hs.nullMeasurableSet
  have h3 : μ (T ⁻¹' s \ s) = 0 := by
    have hA := measure_inter_add_sdiff (μ := μ) (T ⁻¹' s) hs
    have hB := measure_inter_add_sdiff (μ := μ) s hsm
    rw [Set.inter_comm s (T ⁻¹' s), h1, add_zero, ← h2] at hB
    rw [hB] at hA
    refine (ENNReal.add_right_inj (measure_ne_top μ (T ⁻¹' s))).mp ?_
    rw [hA, add_zero]
  refine h s hs ?_
  have hsymm : {x | ¬(x ∈ T ⁻¹' s ↔ x ∈ s)} = (s \ T ⁻¹' s) ∪ (T ⁻¹' s \ s) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_union, Set.mem_diff]
    tauto
  filter_upwards [MeasureTheory.ae_iff.mpr (by rw [hsymm]; exact measure_union_null h1 h3)]
    with x hx
  exact propext hx

/-- **The target.**  `growthFun (Uij hij) ν t` is `μ`-integrable for every leaf-wise system `ν`
of the contracted root group `Uij hij` over an `aDiag t`-invariant probability measure `μ`. -/
theorem integrable_growthFun_uij {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {i j : Fin 3} (hij : i ≠ j) (hlt : t i < t j) :
    ∀ (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
      (X' : Set Work.EKLContract.X3),
      Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X' →
      MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLContract.Uij hij) ν t) μ := by
  classical
  intro ν X' hL
  haveI : StandardBorelSpace X3 := Work.EKLComp.X3Background.2.2.2.2
  have hU : IsHoro (Uij hij) := Lemmas.isHoro_Uij hij
  have hTmeas : Measurable (fun x : X3 => aDiag t • x) :=
    (continuous_const_smul (aDiag t)).measurable
  -- (1) the a.e. fibre bound, from the ergodic case applied to the components of `μ`
  have hbound : ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (growthFun (Uij hij) ν t y) ∂
      (condExpKernel μ (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) x)
        ≤ ENNReal.ofReal (t j - t i) := by
    filter_upwards [fiber_leafwise_uij (μ := μ) (ν := ν) (X' := X') t hij hlt hmp hL,
      condExpKernel_ergodic μ (fun x : X3 => aDiag t • x) hTmeas hmp,
      fiber_inv_finite μ (fun x : X3 => aDiag t • x) hTmeas hmp]
      with x hLx hergx hinvx
    -- name the ambient measure space so that the local `A` below cannot be captured
    let κ : @MeasureTheory.Measure X3 Work.EKLContract.instMeasurableSpaceX3 :=
      condExpKernel μ (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) x
    haveI : IsProbabilityMeasure κ := IsMarkovKernel.isProbabilityMeasure x
    have hLx' : IsLeafwise κ (Uij hij) ν X' := hLx
    have hinvx' : MeasurePreserving (fun x : X3 => aDiag t • x) κ κ := hinvx
    have herg' := ae_ergodic_to_pointwise hinvx hergx
    -- the conull plaque algebra of the component (it is `T`-ergodic, Pisa 7.37)
    obtain ⟨A, Z, hplqA, hZA, hdecA⟩ := desc_plaque_conull_ergodic_pt hij t hlt hinvx herg'
    -- the `ℝ≥0∞` sandwich (Pisa 7.34) and the entropy-contribution bound (Pisa 7.9)
    have h1 : ∫⁻ y, ENNReal.ofReal (growthFun (Uij hij) ν t y) ∂κ
        ≤ @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3
            κ A (MeasurableSpace.comap
              (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) :=
      lintegral_growthFun_le_HcondSig_uij (μ := κ) (ν := ν) (X' := X') t hij hlt hinvx' hLx'
        hplqA hZA hdecA
    have h2 : @Work.EKLC6Core.HcondSig Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 κ A (MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
        ≤ ENNReal.ofReal (t j - t i) :=
      HcondSig_le_ofReal_haar_uij_cf hij t hlt hinvx' herg' hplqA hZA hdecA
    exact le_trans h1 h2
  -- (2) upgrade to `μ` by the disintegration identity of the conditional kernel
  have hlin : ∫⁻ y, ENNReal.ofReal (growthFun (Uij hij) ν t y) ∂μ
      ≤ ENNReal.ofReal (t j - t i) :=
    lintegral_le_of_condKernel_bound (μ := μ) t
      (fun y => ENNReal.ofReal (growthFun (Uij hij) ν t y))
      ((aeStronglyMeasurable_growthFun hU hL t).aemeasurable.ennreal_ofReal)
      (ENNReal.ofReal (t j - t i)) hbound
  -- (3) `growthFun` is non-negative a.e.
  have hsub : conjBox (Uij hij) t ⊆ Box1 (Uij hij) :=
    (box_conjBox_subset hU (tendsto_conj_mem_Uij t hij hlt)).1
  have hmem : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have hnn : 0 ≤ᵐ[μ] growthFun (Uij hij) ν t := by
    filter_upwards [hmem] with x hx
    have hle1 : ν x (conjBox (Uij hij) t) ≤ 1 := by
      calc ν x (conjBox (Uij hij) t) ≤ ν x (Box1 (Uij hij)) := measure_mono hsub
        _ = 1 := hL.normalised x hx
    have hle1' : (ν x (conjBox (Uij hij) t)).toReal ≤ 1 :=
      le_trans (ENNReal.toReal_mono (by simp) hle1) (by simp)
    have hlog : Real.log ((ν x (conjBox (Uij hij) t)).toReal) ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg hle1'
    show (0 : ℝ) ≤ -Real.log ((ν x (conjBox (Uij hij) t)).toReal)
    exact neg_nonneg.mpr hlog
  -- (4) integrability
  refine ⟨aeStronglyMeasurable_growthFun hU hL t, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
  exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top

end Work.EKLC6Core
