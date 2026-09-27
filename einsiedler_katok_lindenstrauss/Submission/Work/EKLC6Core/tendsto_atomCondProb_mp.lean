import Mathlib
import Submission.Work.EKLC6Core.tendsto_atomCondProb

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped ENNReal MeasureTheory

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Work.EKLContract

theorem tendsto_atomCondProb_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (S : Work.EKLRelCross.MSAlg) {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z S.m)
    (hdec : MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) S.m ≤ S.m)
    (hZ : μ Zᶜ = 0)
    {P : ℕ → Work.EKLContract.FinPart Work.EKLContract.X3}
    (hPle : ∀ n, Work.EKLContract.partSigma (P n) ≤ S.m)
    (hPmono : ∀ n, Work.EKLContract.Refines (P (n + 1)) (P n))
    (hPatom : ∀ x : Work.EKLContract.X3,
      (⋂ n, Work.EKLContract.atom (Work.EKLContract.partSigma (P n)) x) =
        Work.EKLContract.atom S.m x) :
    ∀ᵐ x ∂μ, Antitone (fun n : ℕ => Work.EKLC6Core.atomCondProb μ S t (P n) x) ∧
      (∀ n : ℕ, 0 < Work.EKLC6Core.atomCondProb μ S t (P n) x) ∧
      0 < (ν x (Work.EKLContract.shape S.m U x)).toReal ∧
      Filter.Tendsto (fun n : ℕ => Work.EKLC6Core.atomCondProb μ S t (P n) x) Filter.atTop
        (nhds ((ν x (Work.EKLContract.shape S.m U x)).toReal /
          (ν x (Work.EKLContract.shape (MeasurableSpace.comap
            (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) S.m) U x)).toReal)) := by
  classical
  -- ### Step 0: basic a.e. facts
  have hAZ : MeasurableSet Z := hplaq.1 Z hplaq.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl]
    rw [hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have haeX' : ∀ᵐ x ∂μ, x ∈ X' := MeasureTheory.ae_iff.mpr hL.conull
  have haeZ : ∀ᵐ x ∂μ, x ∈ Z := MeasureTheory.ae_iff.mpr hZ
  have haeZ' : ∀ᵐ x ∂μ, x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z :=
    MeasureTheory.ae_iff.mpr hTZ
  -- ### Step 1: the `condexp` of the indicator of a part, as a leafwise ratio
  have hpair : ∀ (n : ℕ) (i : Fin (P n).n), ∀ᵐ x ∂μ,
      condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x =
        (ν x (shape (comapV S t) U x ∩ {u : SL3 | u • x ∈ (P n).parts i})).toReal /
          (ν x (shape (comapV S t) U x)).toReal := by
    intro n i
    have hf : Measurable (((P n).parts i).indicator (fun _ => (1 : ℝ))) :=
      Measurable.indicator measurable_const ((P n).measurable i)
    have hb : ∃ C, ∀ y, |(((P n).parts i).indicator (fun _ => (1 : ℝ))) y| ≤ C := by
      refine ⟨1, fun y => ?_⟩
      by_cases hy : y ∈ (P n).parts i
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    filter_upwards [condExp_shape_eq_pullback hU hL hplaq t hmp hZ _ hf hb,
      haeZ'] with x hx hxZ'
    have hW : MeasurableSet (shape (comapV S t) U x) :=
      measurableSet_shape_of_plaque hU (isPlaqueAlgebra_comap hU t hplaq) hxZ'
    rw [hx, setIntegral_indicator_smul hW ((P n).measurable i) x]
  have hpairall : ∀ᵐ x ∂μ, ∀ (n : ℕ) (i : Fin (P n).n),
      condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x =
        (ν x (shape (comapV S t) U x ∩ {u : SL3 | u • x ∈ (P n).parts i})).toReal /
          (ν x (shape (comapV S t) U x)).toReal := by
    have h := ae_all_iff.mpr (fun p : (Σ n : ℕ, Fin (P n).n) => hpair p.1 p.2)
    filter_upwards [h] with x hx n i
    exact hx ⟨n, i⟩
  -- ### Step 2: the master identity, atom-wise
  have hmain : ∀ᵐ x ∂μ, ∀ n : ℕ, atomCondProb μ S t (P n) x =
      (ν x (shape (comapV S t) U x
        ∩ {u : SL3 | u • x ∈ atom (partSigma (P n)) x})).toReal /
        (ν x (shape (comapV S t) U x)).toReal := by
    filter_upwards [hpairall] with x hx
    intro n
    obtain ⟨i₀, hi₀⟩ : ∃ i, x ∈ (P n).parts i := by
      have : x ∈ ⋃ i, (P n).parts i := by rw [(P n).cover]; trivial
      simpa using this
    have hsum : (∑ i : Fin (P n).n, ((P n).parts i).indicator
          (fun _ => condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x) x)
        = condExp (comapV S t) μ (((P n).parts i₀).indicator (fun _ => (1 : ℝ))) x := by
      rw [Finset.sum_eq_single_of_mem
        (f := fun i : Fin (P n).n => ((P n).parts i).indicator
          (fun _ => condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x) x)
        i₀ (Finset.mem_univ i₀) (fun i _ hne => Set.indicator_of_notMem
          (fun hxi => hne (by
            by_contra h
            exact (Set.disjoint_left.mp ((P n).disjoint h) hxi) hi₀)) _)]
      exact Set.indicator_of_mem hi₀ _
    rw [atomCondProb_apply, hsum, hx n i₀, atom_partSigma_eq_part (P n) x i₀ hi₀]
  -- ### Step 3: pointwise conclusion
  filter_upwards [hmain, haeX', haeZ, haeZ'] with x hx hxX' hxZ hxZ'
  have hWm : MeasurableSet (shape (comapV S t) U x) :=
    measurableSet_shape_of_plaque hU (isPlaqueAlgebra_comap hU t hplaq) hxZ'
  obtain ⟨hWpos, hWfin⟩ :=
    shape_mass_pos_and_lt_top_of_plaque hU hL (isPlaqueAlgebra_comap hU t hplaq) hxX' hxZ'
  obtain ⟨hSpos, hSfin⟩ := shape_mass_pos_and_lt_top_of_plaque hU hL hplaq hxX' hxZ
  have hshapeSub : shape S.m U x ⊆ shape (comapV S t) U x :=
    fun u hu => ⟨hu.1, atom_antitone hdec x hu.2⟩
  have hWcap : shape (comapV S t) U x ∩ {u : SL3 | u • x ∈ atom S.m x} = shape S.m U x := by
    ext u
    constructor
    · rintro ⟨⟨huU, -⟩, hu'⟩
      exact ⟨huU, hu'⟩
    · intro hu
      exact ⟨⟨hu.1, atom_antitone hdec x hu.2⟩, hu.2⟩
  have hTmeas : ∀ n : ℕ, MeasurableSet {u : SL3 | u • x ∈ atom (partSigma (P n)) x} := by
    intro n
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (P n).parts i := by
      have : x ∈ ⋃ i, (P n).parts i := by rw [(P n).cover]; trivial
      simpa using this
    rw [atom_partSigma_eq_part (P n) x i hi]
    exact ((P n).measurable i).preimage (by measurability)
  have hTanti : Antitone (fun n : ℕ => {u : SL3 | u • x ∈ atom (partSigma (P n)) x}) := by
    refine antitone_nat_of_succ_le (fun n u hu => ?_)
    exact atom_antitone (partSigma_mono (hPmono n)) x hu
  have hTint : (⋂ n : ℕ, {u : SL3 | u • x ∈ atom (partSigma (P n)) x})
      = {u : SL3 | u • x ∈ atom S.m x} := by
    ext u
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [← hPatom x, Set.mem_iInter]
  obtain ⟨hAntiRatio, hLimRatio⟩ :=
    antitone_tendsto_ratio (ν := ν x) (W := shape (comapV S t) U x)
      (T := fun n : ℕ => {u : SL3 | u • x ∈ atom (partSigma (P n)) x})
      (Tlim := {u : SL3 | u • x ∈ atom S.m x}) hWfin hWm hTmeas hTanti hTint
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    show atomCondProb μ S t (P b) x ≤ atomCondProb μ S t (P a) x
    rw [hx b, hx a]
    exact hAntiRatio hab
  · intro n
    rw [hx n]
    apply div_pos
    · apply ENNReal.toReal_pos
      · refine ne_of_gt (lt_of_lt_of_le hSpos (measure_mono ?_))
        intro u hu
        exact ⟨hshapeSub hu, atom_antitone (hPle n) x hu.2⟩
      · exact ne_top_of_le_ne_top hWfin.ne (measure_mono Set.inter_subset_left)
    · exact ENNReal.toReal_pos hWpos.ne' hWfin.ne
  · exact ENNReal.toReal_pos hSpos.ne' hSfin.ne
  · have hcongr : (fun n : ℕ => (ν x (shape (comapV S t) U x
          ∩ {u : SL3 | u • x ∈ atom (partSigma (P n)) x})).toReal
            / (ν x (shape (comapV S t) U x)).toReal)
        = fun n : ℕ => atomCondProb μ S t (P n) x := funext fun n => (hx n).symm
    rw [hcongr, hWcap] at hLimRatio
    exact hLimRatio

end

end Work.EKLC6Core
