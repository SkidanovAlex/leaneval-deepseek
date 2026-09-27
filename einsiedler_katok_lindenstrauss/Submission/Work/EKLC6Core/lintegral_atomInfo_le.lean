import Mathlib
import Submission.Work.EKLC6Core.C6Aux
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLContract.All
import Submission.Work.EKLC6Core.exists_refining_part_seq_borel
import Submission.Work.EKLC6Core.lintegral_ofReal_condExp_mul
import Submission.Work.EKLC6Core.tendsto_neg_log_toReal_iInf
import Submission.Work.EKLC6Core.tendsto_atomCondProb

open MeasureTheory Filter Topology
open scoped ENNReal MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The per-partition identity -/

theorem lintegral_ofReal_atomSurprisal_eq_Hcond (μ : Measure X3) [IsProbabilityMeasure μ]
    (S : Work.EKLRelCross.MSAlg) (hSle : S.m ≤ borel X3) (t : Fin 3 → ℝ) (P : FinPart X3) :
    ∫⁻ x, ENNReal.ofReal (atomSurprisal μ S t P x) ∂μ =
      ENNReal.ofReal (Hcond μ P (pullAlg t S)) := by
  classical
  have hmle : pullAlg t S ≤ instMeasurableSpaceX3 := pullAlg_le_borel t S hSle
  have hIcc : ∀ i : Fin P.n, ∀ᵐ x ∂μ, atomCondExp μ S t P i x ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => atomCondExp_mem_Icc S hSle t P i
  have hIccae : ∀ᵐ x ∂μ, ∀ i : Fin P.n, atomCondExp μ S t P i x ∈ Set.Icc (0 : ℝ) 1 :=
    (ae_all_iff (μ := μ)).mpr hIcc
  -- the pointwise rewrite of `ofReal (atomSurprisalSum)` into the sum of the `ofReal`s
  have hpoint : ∀ x : X3, ENNReal.ofReal (atomSurprisalSum μ S t P x) =
      ∑ i, (P.parts i).indicator
        (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) x := by
    intro x
    classical
    obtain ⟨i₀, hi₀⟩ : ∃ i, x ∈ P.parts i := by
      have h : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact Set.mem_univ x
      simpa using h
    have huniq : ∀ i, x ∈ P.parts i → i = i₀ := by
      intro i hi
      by_contra hne
      exact Set.disjoint_left.mp (P.disjoint hne) hi hi₀
    have h1 : (∑ i, ((P.parts i).indicator
        (fun y => -Real.log (atomCondExp μ S t P i y)) x)) = -Real.log (atomCondExp μ S t P i₀ x) := by
      have hsum : (∑ i, ((P.parts i).indicator
          (fun y => -Real.log (atomCondExp μ S t P i y)) x))
          = (P.parts i₀).indicator (fun y => -Real.log (atomCondExp μ S t P i₀ y)) x := by
        refine Finset.sum_eq_single
          (f := fun i : Fin P.n =>
            (P.parts i).indicator (fun y => -Real.log (atomCondExp μ S t P i y)) x) i₀
          (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
        exact Set.indicator_of_notMem (fun hx => hne (huniq i hx))
          (fun y => -Real.log (atomCondExp μ S t P i y))
      rw [hsum, Set.indicator_of_mem hi₀]
    have h2 : (∑ i, (P.parts i).indicator
        (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) x)
        = ENNReal.ofReal (-Real.log (atomCondExp μ S t P i₀ x)) := by
      have hsum : (∑ i, (P.parts i).indicator
          (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) x)
          = (P.parts i₀).indicator
            (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i₀ y))) x := by
        refine Finset.sum_eq_single
          (f := fun i : Fin P.n =>
            (P.parts i).indicator (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) x) i₀
          (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
        exact Set.indicator_of_notMem (fun hx => hne (huniq i hx))
          (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)))
      rw [hsum, Set.indicator_of_mem hi₀]
    simp only [atomSurprisalSum]
    simp only [atomCondExp_eq] at h1 h2 ⊢
    rw [h1, h2]
  -- measurability of the summands
  have hFmeas' : ∀ i : Fin P.n, Measurable[pullAlg t S]
      (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) := fun i =>
    ENNReal.measurable_ofReal.comp ((measurable_atomCondExp μ S t P i).log).neg
  have hFmeas : ∀ i : Fin P.n,
      Measurable (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) := fun i =>
    Measurable.mono (hFmeas' i) hmle le_rfl
  have hGmeas : ∀ i : Fin P.n,
      Measurable (fun y => ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i y))) := fun i =>
    ENNReal.measurable_ofReal.comp (Real.continuous_negMulLog.measurable.comp
      (measurable_atomCondExp_borel μ S hSle t P i))
  -- the pull-out identity
  have hpull : ∀ i : Fin P.n,
      ∫⁻ y, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) * ENNReal.ofReal (atomCondExp μ S t P i y) ∂μ
        = ∫⁻ y in P.parts i, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) ∂μ := by
    intro i
    have h := lintegral_ofReal_condExp_mul (m := pullAlg t S) (mX := instMeasurableSpaceX3)
      hmle μ (f := (P.parts i).indicator (fun _ => (1 : ℝ)))
      ((integrable_const (1 : ℝ)).indicator (P.measurable i))
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (g := fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) (hFmeas' i)
    calc ∫⁻ y, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) * ENNReal.ofReal (atomCondExp μ S t P i y) ∂μ
        = ∫⁻ y, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) * ENNReal.ofReal
              (condExp (pullAlg t S) μ ((P.parts i).indicator (fun _ => (1 : ℝ))) y) ∂μ := by
          simp only [atomCondExp_eq]
      _ = ∫⁻ y, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) * ENNReal.ofReal
              (((P.parts i).indicator (fun _ => (1 : ℝ))) y) ∂μ := h
      _ = ∫⁻ y in P.parts i, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) ∂μ := by
          rw [← lintegral_indicator (μ := μ) (P.measurable i)
            (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)))]
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ P.parts i
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ENNReal.ofReal_one, mul_one]
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero,
              mul_zero]
  -- from the pull-out to the entropy term
  have hneg : ∀ i : Fin P.n,
      ∫⁻ y, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) * ENNReal.ofReal (atomCondExp μ S t P i y) ∂μ
        = ∫⁻ y, ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i y)) ∂μ := by
    intro i
    refine lintegral_congr_ae ?_
    filter_upwards [hIcc i] with y hy
    have hy0 : 0 ≤ atomCondExp μ S t P i y := hy.1
    have hlog : ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y)) * ENNReal.ofReal (atomCondExp μ S t P i y)
        = ENNReal.ofReal (atomCondExp μ S t P i y * (-Real.log (atomCondExp μ S t P i y))) := by
      rw [ENNReal.ofReal_mul hy0, mul_comm]
    rw [hlog]
    congr 1
    rw [Real.negMulLog]
    ring
  -- the sum of the entropy terms
  have hsumG : ∫⁻ y, ∑ i : Fin P.n,
        ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i y)) ∂μ
      = ∑ i : Fin P.n, ∫⁻ y, ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i y)) ∂μ :=
    lintegral_finsetSum (μ := μ) Finset.univ (fun i _ => hGmeas i)
  have hofRealsum : (fun y : X3 => ENNReal.ofReal
        (∑ i : Fin P.n, Real.negMulLog (atomCondExp μ S t P i y)))
      =ᵐ[μ] (fun y : X3 => ∑ i : Fin P.n,
        ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i y))) := by
    filter_upwards [hIccae] with y hy
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    exact Real.negMulLog_nonneg (hy i).1 (hy i).2
  -- integrability and nonnegativity of the entropy density
  have hg_int : Integrable (fun y : X3 => ∑ i : Fin P.n,
      Real.negMulLog (atomCondExp μ S t P i y)) μ := by
    refine Integrable.of_bound ?_ (P.n : ℝ) ?_
    · rw [show (fun y : X3 => ∑ i : Fin P.n, Real.negMulLog (atomCondExp μ S t P i y))
          = (∑ i : Fin P.n, fun y : X3 => Real.negMulLog (atomCondExp μ S t P i y)) from by
            ext y; rw [Finset.sum_apply]]
      exact Finset.aestronglyMeasurable_sum (μ := μ) (s := Finset.univ)
        (f := fun i : Fin P.n => fun y : X3 => Real.negMulLog (atomCondExp μ S t P i y))
        (fun i _ => Real.continuous_negMulLog.comp_aestronglyMeasurable
          (measurable_atomCondExp_borel μ S hSle t P i).aestronglyMeasurable)
    · filter_upwards [hIccae] with y hy
      rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
        Real.negMulLog_nonneg (hy i).1 (hy i).2))]
      calc ∑ i : Fin P.n, Real.negMulLog (atomCondExp μ S t P i y)
          ≤ ∑ _i : Fin P.n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
              have h1 := Real.negMulLog_le_one_sub_self (hy i).1
              linarith [(hy i).1])
        _ = (P.n : ℝ) := by simp
  have hg_nn : 0 ≤ᵐ[μ] (fun y : X3 => ∑ i : Fin P.n,
      Real.negMulLog (atomCondExp μ S t P i y)) := by
    filter_upwards [hIccae] with y hy
    exact Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hy i).1 (hy i).2)
  -- the integral of the entropy density is `Hcond`
  have hHcond : ∫ y, (∑ i : Fin P.n, Real.negMulLog (atomCondExp μ S t P i y)) ∂μ
      = Hcond μ P (pullAlg t S) := by
    simp only [atomCondExp_eq]
    rw [integral_finsetSum Finset.univ (fun i _ => ?_), ← Hcond_eq_sum_integral (μ := μ)
      (m := pullAlg t S) (mX := instMeasurableSpaceX3) P]
    exact integrable_negMulLog_condExp (μ := μ) (m := pullAlg t S)
      (f := (P.parts i).indicator (fun _ => (1 : ℝ)))
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ P.parts i
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]; norm_num)
      ((integrable_const (1 : ℝ)).indicator (P.measurable i))
  calc ∫⁻ x, ENNReal.ofReal (atomSurprisal μ S t P x) ∂μ
      = ∫⁻ x, ENNReal.ofReal (atomSurprisalSum μ S t P x) ∂μ :=
        lintegral_congr (fun x => by rw [atomSurprisal_eq_sum])
    _ = ∫⁻ x, ∑ i : Fin P.n, (P.parts i).indicator
          (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) x ∂μ :=
        lintegral_congr hpoint
    _ = ∑ i : Fin P.n, ∫⁻ x, (P.parts i).indicator
          (fun y => ENNReal.ofReal (-Real.log (atomCondExp μ S t P i y))) x ∂μ :=
        lintegral_finsetSum Finset.univ (fun i _ => (hFmeas i).indicator (P.measurable i))
    _ = ∑ i : Fin P.n, ∫⁻ x in P.parts i,
          ENNReal.ofReal (-Real.log (atomCondExp μ S t P i x)) ∂μ :=
        Finset.sum_congr rfl (fun i _ => lintegral_indicator (P.measurable i) _)
    _ = ∑ i : Fin P.n, ∫⁻ x, ENNReal.ofReal (-Real.log (atomCondExp μ S t P i x))
          * ENNReal.ofReal (atomCondExp μ S t P i x) ∂μ :=
        Finset.sum_congr rfl (fun i _ => (hpull i).symm)
    _ = ∑ i : Fin P.n, ∫⁻ x, ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i x)) ∂μ :=
        Finset.sum_congr rfl (fun i _ => hneg i)
    _ = ∫⁻ x, ∑ i : Fin P.n, ENNReal.ofReal (Real.negMulLog (atomCondExp μ S t P i x)) ∂μ :=
        hsumG.symm
    _ = ∫⁻ x, ENNReal.ofReal (∑ i : Fin P.n, Real.negMulLog (atomCondExp μ S t P i x)) ∂μ :=
        lintegral_congr_ae hofRealsum.symm
    _ = ENNReal.ofReal (∫ x, ∑ i : Fin P.n, Real.negMulLog (atomCondExp μ S t P i x) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hg_int hg_nn).symm
    _ = ENNReal.ofReal (Hcond μ P (pullAlg t S)) := by rw [hHcond]

/-! ## The main assembly -/

private lemma le_of_monotone_tendsto {u : ℕ → ℝ} (hmono : Monotone u) {L : ℝ}
    (htend : Filter.Tendsto u Filter.atTop (nhds L)) (n : ℕ) : u n ≤ L := by
  have h := Antitone.le_of_tendsto (f := fun k => -u k) (a := -L)
    (fun i j hij => by simpa using hmono hij) htend.neg n
  simpa using h

theorem lintegral_atomInfo_le {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) A ≤ A)
    (hZ : μ Zᶜ = 0) :
    MeasureTheory.lintegral μ (fun x => ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x)) ≤
      @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) A) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  obtain ⟨b, hbc, hbm⟩ := hplaq.2.1
  obtain ⟨P, hPle, hPmono, hPatom⟩ :=
    exists_refining_part_seq_borel ⟨A⟩ hplaq.1 ⟨b, hbc, hbm⟩
  have hcrux := tendsto_atomCondProb (μ := μ) (U := U) (ν := ν) (X' := X') (t := t)
    hL hU hAinv ⟨A⟩ hplaq hdec hZ hPle hPmono hPatom
  -- conull sets of good points
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [ae_iff]; exact hL.conull
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [ae_iff]; exact hZ
  have hAZ : MeasurableSet Z := hplaq.1 Z hplaq.2.2.1
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by
    have h1 : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
      rw [← Set.preimage_compl, (hAinv t).measure_preimage hAZ.compl.nullMeasurableSet]
      exact hZ
    rw [ae_iff]
    exact h1
  have hnum : ∀ᵐ x ∂μ, 0 < (ν x (shape A U x)).toReal := by
    filter_upwards [hX', hZae] with x hx hz
    obtain ⟨h1, h2⟩ := shape_mass_pos_and_lt_top_of_plaque (μ := μ) hU hL hplaq hx hz
    exact ENNReal.toReal_pos (ne_of_gt h1) (ne_of_lt h2)
  have hden : ∀ᵐ x ∂μ, 0 < (ν x (shape (pullAlg t ⟨A⟩) U x)).toReal := by
    filter_upwards [hX', hTZae] with x hx hz
    obtain ⟨h1, h2⟩ := pullAlg_mass_pos_and_lt_top (μ := μ) hU hL hplaq t hx hz
    exact ENNReal.toReal_pos (ne_of_gt h1) (ne_of_lt h2)
  -- the a.e. monotonicity and convergence of the surprisals
  have hgood : ∀ᵐ x ∂μ, Monotone (fun n => atomSurprisal μ ⟨A⟩ t (P n) x) ∧
      Filter.Tendsto (fun n => atomSurprisal μ ⟨A⟩ t (P n) x) Filter.atTop
        (nhds (atomInfo A U ν t x)) := by
    filter_upwards [hcrux, hnum, hden] with x hx hn hd
    obtain ⟨hanti, hpos, hnumpos, htend⟩ := hx
    have hne : (ν x (shape A U x)).toReal
        / (ν x (shape (pullAlg t ⟨A⟩) U x)).toReal ≠ 0 := ne_of_gt (div_pos hn hd)
    constructor
    · intro m n hmn
      have h1 : Real.log (atomCondProb μ ⟨A⟩ t (P n) x)
          ≤ Real.log (atomCondProb μ ⟨A⟩ t (P m) x) :=
        Real.log_le_log (hpos n) (hanti hmn)
      simp only [atomSurprisal]
      linarith
    · have ht := (Real.continuousAt_log hne).tendsto.comp htend
      have h2 : Filter.Tendsto (fun n => -Real.log (atomCondProb μ ⟨A⟩ t (P n) x)) Filter.atTop
          (nhds (-Real.log ((ν x (shape A U x)).toReal /
            (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal))) :=
        ht.neg
      simpa only [atomSurprisal, atomInfo] using h2
  -- the pointwise identification of `ofReal (atomInfo)` with the supremum
  have hsup : ∀ᵐ x ∂μ, ENNReal.ofReal (atomInfo A U ν t x)
      = ⨆ n, ENNReal.ofReal (atomSurprisal μ ⟨A⟩ t (P n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hmono, htend⟩ := hx
    refine le_antisymm ?_ ?_
    · exact le_of_tendsto' (ENNReal.tendsto_ofReal htend)
        (fun n => le_iSup (fun n => ENNReal.ofReal (atomSurprisal μ ⟨A⟩ t (P n) x)) n)
    · refine iSup_le (fun n => ENNReal.ofReal_le_ofReal ?_)
      exact le_of_monotone_tendsto hmono htend n
  -- monotone convergence
  have hMCT : (∫⁻ x, ⨆ n, ENNReal.ofReal (atomSurprisal μ ⟨A⟩ t (P n) x) ∂μ)
      = ⨆ n, ∫⁻ x, ENNReal.ofReal (atomSurprisal μ ⟨A⟩ t (P n) x) ∂μ := by
    refine lintegral_iSup_ae (fun n => ?_) (fun n => ?_)
    · exact ENNReal.measurable_ofReal.comp (measurable_atomSurprisal μ ⟨A⟩ hplaq.1 t (P n))
    · filter_upwards [hgood] with x hx
      exact ENNReal.ofReal_le_ofReal (hx.1 (Nat.le_succ n))
  calc ∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ
      = ∫⁻ x, (⨆ n, ENNReal.ofReal (atomSurprisal μ ⟨A⟩ t (P n) x)) ∂μ :=
        lintegral_congr_ae hsup
    _ = ⨆ n, ∫⁻ x, ENNReal.ofReal (atomSurprisal μ ⟨A⟩ t (P n) x) ∂μ := hMCT
    _ = ⨆ n, ENNReal.ofReal (Hcond μ (P n) (pullAlg t ⟨A⟩)) :=
        iSup_congr (fun n => lintegral_ofReal_atomSurprisal_eq_Hcond μ ⟨A⟩ hplaq.1 t (P n))
    _ ≤ @HcondSig X3 instMeasurableSpaceX3 μ A
          (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) := by
        refine iSup_le (fun n => ?_)
        exact le_iSup (fun Q : {P : FinPart X3 // partSigma P ≤ A} =>
          ENNReal.ofReal (Hcond μ Q.1
            (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A))) ⟨P n, hPle n⟩

end Work.EKLC6Core
