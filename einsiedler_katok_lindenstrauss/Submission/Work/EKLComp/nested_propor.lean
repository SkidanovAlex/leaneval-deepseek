import Mathlib
import Submission.Work.EKLComp.LeafAux

/-!
# The nested case of Pisa Proposition 5.17: proportionality of conditional measures

For a finite measure `ν` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, two σ-algebras `𝔪 ≤ 𝔫` below the Borel
σ-algebra with `𝔫` countably generated, and the tower property of the conditional kernels
(in the form `κ_𝔪 x = (κ_𝔪 x) ∘ₘ κ_𝔫` for `ν`-a.e. `x`, where `κ_𝔪`, `κ_𝔫` denote the
conditional expectation kernels of `𝔪` and `𝔫`), the conditional measure of `𝔪` restricted
to an `𝔫`-atom is a multiple of the conditional measure of `𝔫` restricted to that atom:
for `ν`-a.e. `x`,

`(κ_𝔪 x)|_[x]_𝔫 = κ_𝔪 x ([x]_𝔫) • (κ_𝔫 x)|_[x]_𝔫`.

The proof is the standard one.  Write `A x = [x]_𝔫` for the `𝔫`-atom of `x`.
1. `κ_𝔫 y ([y]_𝔫) = 1` for `ν`-a.e. `y` (`condExpKernel_atom`); let `Bad` be a *measurable*
   `ν`-null set containing all the `y` where this fails.
2. By `kernel_measure_eq_zero`, for `ν`-a.e. `x` the measure `κ_𝔪 x` gives `Bad` measure `0`.
   Thus, for such an `x` and `κ_𝔪 x`-a.e. `y`, the `𝔫`-conditional measure of `y` is carried by
   its own atom `[y]_𝔫`.
3. Fix such an `x` and a Borel set `s`.  Testing the tower property at `s ∩ A x` and
   integrating the pointwise identity
   `κ_𝔫 y (s ∩ [x]_𝔫) = 1_[x]_𝔫(y) · κ_𝔫 x (s ∩ [x]_𝔫)`
   (`κ_𝔫` is constant on `𝔫`-atoms, and distinct atoms are disjoint) against `κ_𝔪 x` gives
   `κ_𝔪 x (s ∩ A x) = κ_𝔪 x (A x) · κ_𝔫 x (s ∩ A x)`.
4. The equality of measures follows from the countable π-system `piBasis` generating the Borel
   σ-algebra (`ext_of_piBasis`), together with the total-mass identity
   `κ_𝔪 x (A x) = κ_𝔪 x (A x) · 1`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLComp

theorem nested_propor (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 𝔫 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3)
    (hn : 𝔫.m ≤ borel Work.EKLContract.X3) (hmn : 𝔪.m ≤ 𝔫.m)
    (hgen : Work.EKLComp.CountablyGen 𝔫.m)
    (hmix : ∀ᵐ x ∂ν, ProbabilityTheory.condExpKernel ν 𝔪.m x =
      MeasureTheory.Measure.bind (ProbabilityTheory.condExpKernel ν 𝔪.m x)
        (ProbabilityTheory.condExpKernel ν 𝔫.m)) :
    ∀ᵐ x ∂ν, (ProbabilityTheory.condExpKernel ν 𝔪.m x).restrict
        (Work.EKLContract.atom 𝔫.m x) =
      ProbabilityTheory.condExpKernel ν 𝔪.m x (Work.EKLContract.atom 𝔫.m x) •
        (ProbabilityTheory.condExpKernel ν 𝔫.m x).restrict (Work.EKLContract.atom 𝔫.m x) := by
  classical
  -- Step 1: `κ_𝔫 y` is carried by the `𝔫`-atom of `y` for `ν`-a.e. `y`; put all the exceptions
  -- in a measurable `ν`-null set `Bad`.
  have hatom : ∀ᵐ y ∂ν, (ProbabilityTheory.condExpKernel ν 𝔫.m y)
      (Work.EKLContract.atom 𝔫.m y) = 1 :=
    Work.EKLComp.condExpKernel_atom 𝔫 hn hgen ν
  let w : Work.EKLContract.X3 → ℝ≥0∞ := fun y =>
    (ProbabilityTheory.condExpKernel ν 𝔫.m y) (Work.EKLContract.atom 𝔫.m y)
  have hbad_ν : ν {y | w y ≠ 1} = 0 := MeasureTheory.ae_iff.mp hatom
  obtain ⟨Bad, hBad_sub, hBad_meas, hBad_ν⟩ :=
    MeasureTheory.exists_measurable_superset ν {y | w y ≠ 1}
  have hBad_ν0 : ν Bad = 0 := by rw [hBad_ν, hbad_ν]
  -- Step 2: for `ν`-a.e. `x` the measure `κ_𝔪 x` vanishes on `Bad`.
  have hnull : ∀ᵐ x ∂ν, (ProbabilityTheory.condExpKernel ν 𝔪.m x) Bad = 0 :=
    Work.EKLComp.kernel_measure_eq_zero ν 𝔪 hm hBad_meas hBad_ν0
  filter_upwards [hnull, hmix, hatom] with x hxnull hxmix hxatom
  have hA : MeasurableSet (Work.EKLContract.atom 𝔫.m x) :=
    hn _ (Work.EKLComp.measurableSet_atom 𝔫.m hgen x)
  haveI hprob : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.condExpKernel ν 𝔪.m x) :=
    ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x
  refine Work.EKLComp.ext_of_piBasis ?_ ?_
  · intro s hs
    have hsa : MeasurableSet s := Work.EKLComp.measurableSet_of_mem_piBasis hs
    have hsA : MeasurableSet (s ∩ Work.EKLContract.atom 𝔫.m x) := hsa.inter hA
    -- Restate the goal as an identity between numbers.
    rw [MeasureTheory.Measure.restrict_apply hsa, MeasureTheory.Measure.smul_apply, smul_eq_mul,
      MeasureTheory.Measure.restrict_apply hsa]
    have hnotBad : ∀ᵐ y ∂(ProbabilityTheory.condExpKernel ν 𝔪.m x), y ∉ Bad :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hxnull
    -- Step 3a: pointwise identity of the two integrands, `κ_𝔪 x`-a.e.
    have hpoint : (fun y => (ProbabilityTheory.condExpKernel ν 𝔫.m y)
          (s ∩ Work.EKLContract.atom 𝔫.m x)) =ᵐ[ProbabilityTheory.condExpKernel ν 𝔪.m x]
        (fun y => (Work.EKLContract.atom 𝔫.m x).indicator
          (fun _ => (ProbabilityTheory.condExpKernel ν 𝔫.m x)
            (s ∩ Work.EKLContract.atom 𝔫.m x)) y) := by
      filter_upwards [hnotBad] with y hyBad
      have hyatom : (ProbabilityTheory.condExpKernel ν 𝔫.m y)
          (Work.EKLContract.atom 𝔫.m y) = 1 := by
        by_contra hc
        exact hyBad (hBad_sub hc)
      by_cases hyA : y ∈ Work.EKLContract.atom 𝔫.m x
      · -- `y` is in the atom of `x`: the kernel is constant on the atom.
        have hyx : (ProbabilityTheory.condExpKernel ν 𝔫.m y)
            = (ProbabilityTheory.condExpKernel ν 𝔫.m x) :=
          (Work.EKLComp.kernel_atom_const (μ := ν) 𝔫 hyA).symm
        rw [hyx, Set.indicator_of_mem hyA]
      · -- `y` is outside the atom of `x`: the two atoms are disjoint and the second kernel is
        -- carried by `[y]_𝔫`.
        have hdisj : Disjoint (Work.EKLContract.atom 𝔫.m y)
            (Work.EKLContract.atom 𝔫.m x) := by
          rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
          rintro z ⟨hzy, hzx⟩
          have h1 : Work.EKLContract.atom 𝔫.m z = Work.EKLContract.atom 𝔫.m y :=
            Work.EKLComp.atom_eq_of_mem 𝔫.m hzy
          have h2 : Work.EKLContract.atom 𝔫.m z = Work.EKLContract.atom 𝔫.m x :=
            Work.EKLComp.atom_eq_of_mem 𝔫.m hzx
          refine hyA ?_
          rw [← h2, h1]
          exact Set.mem_sInter.mpr fun t ht => ht.2
        have hzero : (ProbabilityTheory.condExpKernel ν 𝔫.m y)
            (s ∩ Work.EKLContract.atom 𝔫.m x) = 0 := by
          have hsub : s ∩ Work.EKLContract.atom 𝔫.m x ⊆
              (Work.EKLContract.atom 𝔫.m y)ᶜ := by
            rintro z ⟨-, hzx⟩ hzy
            exact (Set.disjoint_left.mp hdisj hzy) hzx
          have hle : (ProbabilityTheory.condExpKernel ν 𝔫.m y)
              (s ∩ Work.EKLContract.atom 𝔫.m x) ≤ 0 := by
            calc (ProbabilityTheory.condExpKernel ν 𝔫.m y)
                  (s ∩ Work.EKLContract.atom 𝔫.m x)
                ≤ (ProbabilityTheory.condExpKernel ν 𝔫.m y)
                    ((Work.EKLContract.atom 𝔫.m y)ᶜ) := MeasureTheory.measure_mono hsub
              _ = 0 := by
                rw [MeasureTheory.measure_compl
                    (hn _ (Work.EKLComp.measurableSet_atom 𝔫.m hgen y))
                    (MeasureTheory.measure_ne_top _ _),
                  (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure y).measure_univ,
                  hyatom, tsub_self]
          exact le_antisymm hle bot_le
        rw [hzero, Set.indicator_of_notMem hyA]
    -- Step 3b: test the tower property on `s ∩ [x]_𝔫` and integrate the pointwise identity.
    calc (ProbabilityTheory.condExpKernel ν 𝔪.m x) (s ∩ Work.EKLContract.atom 𝔫.m x)
        = (MeasureTheory.Measure.bind (ProbabilityTheory.condExpKernel ν 𝔪.m x)
            (ProbabilityTheory.condExpKernel ν 𝔫.m)) (s ∩ Work.EKLContract.atom 𝔫.m x) :=
          congrArg (fun m : MeasureTheory.Measure Work.EKLContract.X3 =>
            m (s ∩ Work.EKLContract.atom 𝔫.m x)) hxmix
      _ = ∫⁻ y, (ProbabilityTheory.condExpKernel ν 𝔫.m y)
            (s ∩ Work.EKLContract.atom 𝔫.m x)
            ∂(ProbabilityTheory.condExpKernel ν 𝔪.m x) :=
          MeasureTheory.Measure.bind_apply hsA
            ((ProbabilityTheory.condExpKernel ν 𝔫.m).measurable.mono hn le_rfl).aemeasurable
      _ = ∫⁻ y, (Work.EKLContract.atom 𝔫.m x).indicator
            (fun _ => (ProbabilityTheory.condExpKernel ν 𝔫.m x)
              (s ∩ Work.EKLContract.atom 𝔫.m x)) y
            ∂(ProbabilityTheory.condExpKernel ν 𝔪.m x) :=
          MeasureTheory.lintegral_congr_ae hpoint
      _ = (ProbabilityTheory.condExpKernel ν 𝔫.m x) (s ∩ Work.EKLContract.atom 𝔫.m x) *
            (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Work.EKLContract.atom 𝔫.m x) :=
          MeasureTheory.lintegral_indicator_const hA _
      _ = (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Work.EKLContract.atom 𝔫.m x) *
            (ProbabilityTheory.condExpKernel ν 𝔫.m x) (s ∩ Work.EKLContract.atom 𝔫.m x) :=
          mul_comm _ _
  · -- Step 4: total mass.  Both sides are `κ_𝔪 x (A x)` because `κ_𝔫 x (A x) = 1`.
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      MeasureTheory.Measure.smul_apply, smul_eq_mul,
      MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hxatom, mul_one]

end Work.EKLComp
