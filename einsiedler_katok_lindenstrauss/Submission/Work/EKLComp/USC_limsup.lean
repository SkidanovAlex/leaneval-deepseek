import Mathlib
import Submission.Work.EKLComp.ErgMax.USCDefs
import Submission.Work.EKLComp.exists_small_part
import Submission.Work.EKLComp.polishSpace_X3
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.limsup_measure_closed_le
import Submission.Work.EKLComp.tendsto_measure_of_null_frontier_of_integral
import Submission.Work.Misiurewicz.frontier_joinSets_smulMap_eq_zero

/-!
# C4b (part ii) — upper semicontinuity of entropy on compacta

`Work.EKLComp.USC_limsup` is clause (ii) of `P_USC'` (`Submission/Work/EKLComp/ErgMax/USCDefs.lean`):
for a weakly convergent sequence of `aDiag t`-invariant probability measures carried by a compact
forward-invariant set `K`, the Kolmogorov–Sinai entropy is upper semicontinuous.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.EKLComp

open Work.EKLContract

noncomputable section

/-- A weak limit of `aDiag t`-invariant probability measures is `aDiag t`-invariant. -/
theorem aDiag_invariant_of_weak_limit_aux
    (t : Fin 3 → ℝ) (νseq : ℕ → Measure X3) (νlim : Measure X3)
    (hprob : ∀ n, IsProbabilityMeasure (νseq n))
    (hproblim : IsProbabilityMeasure νlim)
    (hmp : ∀ n, MeasurePreserving (fun x : X3 => aDiag t • x) (νseq n) (νseq n))
    (hweak : ∀ f : X3 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(νseq n)) atTop (𝓝 (∫ x, f x ∂νlim))) :
    MeasurePreserving (fun x : X3 => aDiag t • x) νlim νlim := by
  have hφc : Continuous (fun x : X3 => aDiag t • x) := continuous_const_smul _
  haveI : HasOuterApproxClosed X3 := inferInstance
  refine ⟨hφc.measurable, ?_⟩
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  have hcomp : ∀ n, ∫ x, f ((fun x : X3 => aDiag t • x) x) ∂(νseq n) = ∫ x, f x ∂(νseq n) := by
    intro n
    have h := integral_map (μ := νseq n) hφc.measurable.aemeasurable
      (f.continuous.aestronglyMeasurable)
    rw [MeasurePreserving.map_eq (hmp n)] at h
    exact h.symm
  rw [integral_map hφc.measurable.aemeasurable (f.continuous.aestronglyMeasurable)]
  let g : X3 →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : X3 => f (aDiag t • x)) (f.continuous.comp hφc) ‖f‖
    (fun x => BoundedContinuousFunction.norm_coe_le_norm f (aDiag t • x))
  have hlim1 : Tendsto (fun n => ∫ x, f ((fun x : X3 => aDiag t • x) x) ∂(νseq n)) atTop
      (𝓝 (∫ x, f ((fun x : X3 => aDiag t • x) x) ∂νlim)) := hweak g
  have hlim2 : Tendsto (fun n => ∫ x, f x ∂(νseq n)) atTop (𝓝 (∫ x, f x ∂νlim)) := hweak f
  exact tendsto_nhds_unique (by simpa only [hcomp] using hlim1) hlim2

/-- `Hfam` of the `M`-fold join of `P` along `x ↦ aDiag t • x` converges along a weakly
convergent sequence, provided the limit measure is `a`-invariant and the members of `P` have
`νlim`-null frontier. -/
theorem Hfam_joinSets_tendsto
    (t : Fin 3 → ℝ) (P : FinPart X3) (M : ℕ) (νseq : ℕ → Measure X3) (νlim : Measure X3)
    (hprob : ∀ n, IsProbabilityMeasure (νseq n)) (hproblim : IsProbabilityMeasure νlim)
    (hweak : ∀ f : X3 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(νseq n)) atTop (𝓝 (∫ x, f x ∂νlim)))
    (hT : MeasurePreserving (fun x : X3 => aDiag t • x) νlim νlim)
    (hbdry : ∀ i, νlim (frontier (P.parts i)) = 0) :
    Tendsto (fun n => Hfam (νseq n) (joinSets (fun x : X3 => aDiag t • x) P M)) atTop
      (𝓝 (Hfam νlim (joinSets (fun x : X3 => aDiag t • x) P M))) := by
  have hTmeas : Measurable (fun x : X3 => aDiag t • x) := (continuous_const_smul _).measurable
  have key : ∀ w : Fin M → Fin P.n, Tendsto
      (fun n => Real.negMulLog ((νseq n (joinSets (fun x : X3 => aDiag t • x) P M w)).toReal))
      atTop
      (𝓝 (Real.negMulLog
        ((νlim (joinSets (fun x : X3 => aDiag t • x) P M w)).toReal))) := by
    intro w
    have hfr : νlim (frontier (joinSets (fun x : X3 => aDiag t • x) P M w)) = 0 :=
      Work.Misiurewicz.frontier_joinSets_smulMap_eq_zero νlim (aDiag t) hT P hbdry M w
    have hmeas : MeasurableSet (joinSets (fun x : X3 => aDiag t • x) P M w) :=
      Core.joinSets_measurable hTmeas P M w
    have hconv := tendsto_measure_of_null_frontier_of_integral νseq νlim hprob hweak hmeas hfr
    have hne : νlim (joinSets (fun x : X3 => aDiag t • x) P M w) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (measure_mono (Set.subset_univ _)) ?_)
      rw [measure_univ]
    have h2 := (ENNReal.tendsto_toReal hne).comp hconv
    exact (Real.continuous_negMulLog.tendsto _).comp h2
  have hsum := tendsto_finsetSum Finset.univ (fun w _ => key w)
  simpa [Hfam] using hsum

/-- `limsup u ≤ c` when `u ≤ v` pointwise and `v → c`. -/
lemma limsup_le_of_forall_le_tendsto {u v : ℕ → ℝ} {c : ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) (hv : Tendsto v atTop (𝓝 c)) :
    Filter.limsup u Filter.atTop ≤ c := by
  have hbdd : IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    isBoundedUnder_of_eventually_le
      ((hv.eventually (isOpen_Iio.mem_nhds (lt_add_one c))).mono
        (fun n hn => le_of_lt (lt_of_le_of_lt (huv n) hn)))
  refine (Filter.limsup_le_iff (f := Filter.atTop) (u := u)
    (isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall hu0)) hbdd).mpr ?_
  intro y hy
  filter_upwards [hv.eventually (isOpen_Iio.mem_nhds hy)] with n hn
  exact lt_of_le_of_lt (huv n) hn

theorem USC_limsup
    (h : ∀ (t : Fin 3 → ℝ), (∃ i j : Fin 3, t i ≠ t j) → ∀ (K : Set Work.EKLContract.X3),
      IsCompact K → (∀ x ∈ K, Work.EKLContract.aDiag t • x ∈ K) →
      Work.EKLComp.ErgMax.AtomSmallEntropy t K)
    (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) (K : Set Work.EKLContract.X3)
    (hK : IsCompact K) (hfwd : ∀ x ∈ K, Work.EKLContract.aDiag t • x ∈ K) :
    ∀ (νseq : ℕ → MeasureTheory.Measure Work.EKLContract.X3)
      (νlim : MeasureTheory.Measure Work.EKLContract.X3),
      (∀ n, MeasureTheory.IsProbabilityMeasure (νseq n)) →
      MeasureTheory.IsProbabilityMeasure νlim → (∀ n, νseq n K = 1) →
      (∀ n, MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) (νseq n) (νseq n)) →
      (∀ f : BoundedContinuousFunction Work.EKLContract.X3 ℝ,
        Filter.Tendsto (fun n => MeasureTheory.integral (νseq n) f) Filter.atTop
          (nhds (MeasureTheory.integral νlim f))) →
      Filter.limsup (fun n => Work.EKLContract.ent (νseq n) (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) Filter.atTop ≤
        Work.EKLContract.ent νlim (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) := by
  intro νseq νlim hprob hproblim hKν hmp hweak
  obtain ⟨δ, hδpos, hδP⟩ := h t ht K hK hfwd
  obtain ⟨P, hPsmall, hPbdry⟩ := Work.EKLComp.exists_small_part K hK νlim hδpos
  have hmp_lim : MeasurePreserving (fun x : X3 => aDiag t • x) νlim νlim :=
    aDiag_invariant_of_weak_limit_aux t νseq νlim hprob hproblim hmp hweak
  have hbound : ∀ n, hPart (νseq n) (fun x : X3 => aDiag t • x) P
      ≤ Real.log (P.n : ℝ) := by
    intro n
    calc hPart (νseq n) (fun x : X3 => aDiag t • x) P
        ≤ Hfam (νseq n) P.parts := ErgMax.hPart_le_Hfam _ _ _
      _ ≤ Real.log (Fintype.card (Fin P.n) : ℝ) :=
          Core.Hfam_le_log_card _ (ErgMax.isMPart_parts P)
      _ = Real.log (P.n : ℝ) := by simp
  have hreal : Filter.limsup (fun n => hPart (νseq n) (fun x : X3 => aDiag t • x) P) atTop
      ≤ hPart νlim (fun x : X3 => aDiag t • x) P := by
    show _ ≤ ⨅ N : ℕ, Hfam νlim (joinSets (fun x : X3 => aDiag t • x) P (N+1)) / ((N:ℝ)+1)
    refine le_ciInf (fun N => ?_)
    exact limsup_le_of_forall_le_tendsto
      (u := fun n => hPart (νseq n) (fun x : X3 => aDiag t • x) P)
      (v := fun n => Hfam (νseq n) (joinSets (fun x : X3 => aDiag t • x) P (N+1)) / ((N:ℝ)+1))
      (c := Hfam νlim (joinSets (fun x : X3 => aDiag t • x) P (N+1)) / ((N:ℝ)+1))
      (fun n => Core.hPart_nonneg (νseq n) _ P)
      (fun n => Core.hPart_le_avg (νseq n) _ P N)
      ((Hfam_joinSets_tendsto t P (N+1) νseq νlim hprob hproblim hweak hmp_lim hPbdry).div_const _)
  have h1 : IsCoboundedUnder (· ≤ ·) atTop
      (fun n => hPart (νseq n) (fun x : X3 => aDiag t • x) P) :=
    isCoboundedUnder_le_of_eventually_le _
      (Eventually.of_forall (fun n => Core.hPart_nonneg (νseq n) _ P))
  have h2 : IsBoundedUnder (· ≤ ·) atTop
      (fun n => hPart (νseq n) (fun x : X3 => aDiag t • x) P) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hbound)
  calc Filter.limsup (fun n => ent (νseq n) (fun x : X3 => aDiag t • x)) atTop
      = Filter.limsup
          (fun n => ENNReal.ofReal (hPart (νseq n) (fun x : X3 => aDiag t • x) P)) atTop := by
        refine Filter.limsup_congr (Eventually.of_forall (fun n => ?_))
        exact hδP P hPsmall (νseq n) (hprob n) (hKν n) (hmp n)
    _ = ENNReal.ofReal
          (Filter.limsup (fun n => hPart (νseq n) (fun x : X3 => aDiag t • x) P) atTop) :=
        (ENNReal.ofReal_limsup h1 h2).symm
    _ ≤ ENNReal.ofReal (hPart νlim (fun x : X3 => aDiag t • x) P) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ent νlim (fun x : X3 => aDiag t • x) :=
        le_iSup (fun Q : FinPart X3 =>
          ENNReal.ofReal (hPart νlim (fun x : X3 => aDiag t • x) Q)) P

end

end Work.EKLComp
