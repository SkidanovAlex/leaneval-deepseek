import Mathlib
import Submission.Work.EKLC6Core.lintegral_atomInfo_le
import Submission.Work.EKLC6Core.tendsto_atomCondProb_mp

open MeasureTheory Filter Topology
open scoped ENNReal MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

private lemma le_of_monotone_tendsto_mp {u : ℕ → ℝ} (hmono : Monotone u) {L : ℝ}
    (htend : Filter.Tendsto u Filter.atTop (nhds L)) (n : ℕ) : u n ≤ L := by
  have h := Antitone.le_of_tendsto (f := fun k => -u k) (a := -L)
    (fun i j hij => by simpa using hmono hij) htend.neg n
  simpa using h

theorem lintegral_atomInfo_le_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap
      (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) A ≤ A)
    (hZ : μ Zᶜ = 0) :
    MeasureTheory.lintegral μ
        (fun x => ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x)) ≤
      @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) A) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  obtain ⟨b, hbc, hbm⟩ := hplaq.2.1
  obtain ⟨P, hPle, hPmono, hPatom⟩ :=
    exists_refining_part_seq_borel ⟨A⟩ hplaq.1 ⟨b, hbc, hbm⟩
  have hcrux := tendsto_atomCondProb_mp (μ := μ) (U := U) (ν := ν) (X' := X') (t := t)
    hL hU hmp ⟨A⟩ hplaq hdec hZ hPle hPmono hPatom
  -- conull sets of good points
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [ae_iff]; exact hL.conull
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [ae_iff]; exact hZ
  have hAZ : MeasurableSet Z := hplaq.1 Z hplaq.2.2.1
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by
    have h1 : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
      rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
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
      exact le_of_monotone_tendsto_mp hmono htend n
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
