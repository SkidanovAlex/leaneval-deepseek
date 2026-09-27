import Mathlib
import Submission.Work.EKLC6Core.HcondSig_le_lintegral_atomInfo
import Submission.Work.EKLC6Core.shapeAvg_lintegral_eq
import Submission.Work.EKLC6Core.uminus_isHoro

/-!
# `Work.EKLC6Core.HcondSigFree.HcondSig_le_lintegral_atomInfo_mp`

The `MeasurePreserving` (rather than `IsAErgodic`) form of
`Work.EKLC6Core.HcondSig_le_lintegral_atomInfo`:

`HcondSig μ A (comap (aDiag t ·) A) ≤ ∫⁻ x, ENNReal.ofReal (atomInfo A (Uminus t) ν t x) ∂μ`.

The ergodic form of the theorem uses the ergodicity hypothesis `hErg` only through the single
measure-preserving statement `hErg.1 t` — that the diagonal element `aDiag t` at hand preserves
`μ`.  Accordingly the proof below is the same argument run on the weaker hypothesis `hmp`.
(Helper lemmas used on the way — `hcsg_ae_condExp_eq_shape_ratio`, `ae_Wsh_inter_null`,
`shapeAvg_lintegral_eq`, `mass_Wsh`, `shape_mass_pos`, … — are already stated for an individual
measure-preserving diagonal map, so no further change is needed.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core.HcondSigFree

open Work.EKLC6Core
open Work.EKLContract

theorem HcondSig_le_lintegral_atomInfo_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A) :
    @Work.EKLC6Core.HcondSig Work.EKLContract.X3 (borel Work.EKLContract.X3) μ A
        (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
      ≤ ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hAZ : MeasurableSet Z := hplq.1 Z hplq.2.2.1
  have hTZcompl : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have haeX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have haeZ : ∀ᵐ x ∂μ, x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hZ
  have haeTZ : ∀ᵐ x ∂μ, x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z := by
    rw [MeasureTheory.ae_iff]; exact hTZcompl
  rw [HcondSig]
  refine iSup_le ?_
  rintro ⟨P, hP⟩
  set S : Work.EKLRelCross.MSAlg := ⟨A⟩ with hS
  -- the conditional probabilities of the partition pieces
  set ce : X3 → Fin P.n → ℝ := fun x i =>
    condExp (betaAlg t S) μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x with hce
  set qf : X3 → Fin P.n → ℝ := fun x i =>
    (ν x (Dpart t S (Uminus t) P i x)).toReal / (ν x (Wsh t S (Uminus t) x)).toReal with hqf
  -- ### 1. the condexp identity at a point (ratio form)
  have hcond : ∀ᵐ x ∂μ, ∀ i : Fin P.n, ce x i = qf x i := by
    rw [Filter.eventually_all]
    intro i
    have h := hcsg_ae_condExp_eq_shape_ratio hU hL hmp (P.measurable i) hplq hZ
    filter_upwards [h] with x hx
    simpa only [hce, hqf, Wsh_def, betaAlg_def, Dpart_def] using hx
  -- ### 2. a measurable null superset of the failure set, and the leafwise transfer
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := MeasureTheory.exists_measurable_superset_of_null
    (show μ {x : X3 | ¬ (∀ i : Fin P.n, ce x i = qf x i)} = 0 from by
      rw [← MeasureTheory.ae_iff]; exact hcond)
  have hleaftransfer : ∀ᵐ x ∂μ, ∀ᵐ u ∂(ν x), u ∈ Wsh t S (Uminus t) x →
      (∀ i : Fin P.n, ce (u • x) i = qf (u • x) i) := by
    filter_upwards [ae_Wsh_mem_of_null hU hL t hmp hNmeas hNnull hplq hZ] with x hx
    filter_upwards [hx] with u hu huW
    intro i
    by_contra hne
    exact hu huW (hNsub (by
      simp only [Set.mem_ofPred_eq]
      intro hall
      exact hne (hall i)))
  have hgood : ∀ᵐ x ∂μ, ∀ᵐ u ∂(ν x), u ∈ Wsh t S (Uminus t) x →
      (u • x ∈ X' ∧ u • x ∈ Z ∧ u • x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z) := by
    have hM0 : μ (X'ᶜ ∪ Zᶜ ∪ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ) = 0 :=
      measure_union_null (measure_union_null hL.conull hZ) hTZcompl
    have hMm : MeasurableSet (X'ᶜ ∪ Zᶜ ∪ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ) :=
      (hL.meas_dom.compl.union hAZ.compl).union ((hAZ.preimage hmp.measurable).compl)
    filter_upwards [ae_Wsh_mem_of_null hU hL t hmp hMm hM0 hplq hZ] with x hx
    filter_upwards [hx] with u hu huW
    have hnot := hu huW
    refine ⟨?_, ?_, ?_⟩
    · by_contra h; exact hnot (Set.mem_union_left _ (Set.mem_union_left _ h))
    · by_contra h; exact hnot (Set.mem_union_left _ (Set.mem_union_right _ h))
    · by_contra h; exact hnot (Set.mem_union_right _ h)
  -- ### 3. the measurable test function `Ψ`
  set pf : X3 → ℝ := fun y => ∑ i : Fin P.n, (P.parts i).indicator (fun _ => ce y i) y with hpf
  set Ψ : X3 → ENNReal := fun y => ENNReal.ofReal (-Real.log (pf y)) with hΨ
  have hβborel : betaAlg t S ≤ borel X3 := by
    rw [betaAlg_def]
    exact (MeasurableSpace.comap_mono hplq.1).trans
      (measurable_iff_comap_le.mp (continuous_const_smul (aDiag t)).measurable)
  have hβplaq : IsPlaqueAlgebra (Uminus t) ((fun y : X3 => aDiag t • y) ⁻¹' Z) (betaAlg t S) :=
    isPlaqueAlgebra_betaAlg hU hplq t
  have hβA : betaAlg t S ≤ A := hdec
  -- measurability of `ce`, `pf`, `Ψ`
  have hce_meas : ∀ i : Fin P.n, Measurable (fun x : X3 => ce x i) := by
    intro i
    have hsm : StronglyMeasurable[betaAlg t S]
        (fun x : X3 => condExp (betaAlg t S) μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x) :=
      stronglyMeasurable_condExp
    exact ((hsm.mono hβborel)).measurable
  have hpf_meas : Measurable pf := by
    rw [hpf]
    exact Finset.measurable_sum Finset.univ
      (fun i _ => (hce_meas i).indicator (P.measurable i))
  have hΨ_meas : Measurable Ψ := by
    rw [hΨ]
    exact ENNReal.measurable_ofReal.comp ((Real.measurable_log.comp hpf_meas).neg)
  -- measurability, disjointness and covering of the partition pieces
  have hDmeas : ∀ (x : X3), x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z → ∀ i : Fin P.n,
      MeasurableSet (Dpart t S (Uminus t) P i x) := by
    intro x hxTZ i
    exact (measurableSet_shape hU hβplaq hxTZ).inter
      ((P.measurable i).preimage (continuous_id.smul continuous_const).measurable)
  have hdisj : ∀ (x : X3) (i j : Fin P.n), i ≠ j →
      Disjoint (Dpart t S (Uminus t) P i x) (Dpart t S (Uminus t) P j x) := by
    intro x i j hij
    rw [Dpart_def, Dpart_def, Set.disjoint_left]
    intro u hu hv
    exact (Set.disjoint_left.mp (P.disjoint hij)) hu.2 hv.2
  have hcover : ∀ x : X3, (⋃ i : Fin P.n, Dpart t S (Uminus t) P i x) = Wsh t S (Uminus t) x := by
    intro x
    ext u
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hu⟩; exact hu.1
    · intro hu
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [P.cover]; exact Set.mem_univ (u • x))
      exact ⟨i, hu, hi⟩
  -- ### 4. the pointwise information inequality (Pisa 7.34)
  have hperx : ∀ᵐ x ∂μ, ENNReal.ofReal (∑ i : Fin P.n, Real.negMulLog (ce x i))
      ≤ shapeAvg t S (Uminus t) ν Ψ x := by
    filter_upwards [hcond, hleaftransfer, hgood, haeX', haeTZ] with x hxce hxleaf hxgood hxX' hxTZ
    obtain ⟨hWpos, hWlt⟩ := mass_Wsh (S := S) hU hL hplq t hxX' hxTZ
    have hpt : ∀ i : Fin P.n, ∀ᵐ u ∂(Measure.restrict (ν x) (Dpart t S (Uminus t) P i x)),
        ENNReal.ofReal (-Real.log (qf x i)) ≤ (fun u : SL3 => Ψ (u • x)) u := by
      intro i
      have h1 : ∀ᵐ u ∂(ν x), u ∈ Wsh t S (Uminus t) x → ce (u • x) i = qf (u • x) i :=
        hxleaf.mono (fun u hu => fun hW => hu hW i)
      filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae hxgood,
        MeasureTheory.ae_restrict_mem (hDmeas x hxTZ i)] with u h1u h2u hu
      rw [Dpart_def] at hu
      have huW : u ∈ Wsh t S (Uminus t) x := hu.1
      have hui : u • x ∈ P.parts i := hu.2
      obtain ⟨huX', huZ, huTZ⟩ := h2u huW
      have hl : ce (u • x) i = qf (u • x) i := h1u huW
      have hmass : qf x i = qf (u • x) i :=
        Dpart_ratio_eq_of_mem_Wsh hU hL t hplq (P := P) hxX' huX' huW hxTZ huTZ i
      have hpfval : pf (u • x) = ce (u • x) i := by
        simp only [hpf]
        rw [Finset.sum_eq_single i]
        · exact Set.indicator_of_mem hui _
        · intro j _ hji
          refine Set.indicator_of_notMem (fun hxj => ?_) _
          exact (Set.disjoint_left.mp (P.disjoint (Ne.symm hji))) hui hxj
        · intro hi; exact absurd (Finset.mem_univ i) hi
      simp only [hΨ]
      rw [hpfval, hl, hmass]
    have hbound := ofReal_sum_negMulLog_le_lintegral_div (ν := ν x) (W := Wsh t S (Uminus t) x)
      (D := fun i : Fin P.n => Dpart t S (Uminus t) P i x)
      (measurableSet_shape hU hβplaq hxTZ) (ne_of_gt hWpos) (ne_of_lt hWlt)
      (fun i => hDmeas x hxTZ i) (fun i j hij => hdisj x i j hij) (hcover x)
      (Φ := fun u : SL3 => Ψ (u • x)) hpt
    rw [Finset.sum_congr rfl (fun i _ => by rw [hxce i])]
    simpa only [shapeAvg_def] using hbound
  -- ### 5. `Ψ ≤ ofReal ∘ atomInfo` a.e.
  have hΦ : ∀ᵐ x ∂μ, Ψ x ≤ ENNReal.ofReal (atomInfo A (Uminus t) ν t x) := by
    filter_upwards [hcond, haeX', haeZ, haeTZ] with x hxce hxX' hxZ hxTZ
    obtain ⟨ix, hix⟩ := Set.mem_iUnion.mp (by rw [P.cover]; exact Set.mem_univ x)
    have hpfx : pf x = ce x ix := by
      simp only [hpf]
      rw [Finset.sum_eq_single ix]
      · exact Set.indicator_of_mem hix _
      · intro j _ hji
        refine Set.indicator_of_notMem (fun hxj => ?_) _
        exact (Set.disjoint_left.mp (P.disjoint (Ne.symm hji))) hix hxj
      · intro hi; exact absurd (Finset.mem_univ ix) hi
    have hsub : shape A (Uminus t) x ⊆ Dpart t S (Uminus t) P ix x := by
      intro u hu
      exact ⟨⟨hu.1, hcsg_atom_mono hβA x hu.2⟩,
        hcsg_atom_subset_of_mem (hP (P.parts ix) (hcsg_partSigma_mem P ix)) hix hu.2⟩
    obtain ⟨hVpos, hVlt⟩ := shape_mass_pos hL hplq hxX' hxZ
    obtain ⟨hWposx, hWltx⟩ := mass_Wsh (S := S) hU hL hplq t hxX' hxTZ
    have hratio : (ν x (shape A (Uminus t) x)).toReal / (ν x (Wsh t S (Uminus t) x)).toReal
        ≤ qf x ix := by
      rw [hqf]
      refine div_le_div_of_nonneg_right ?_ ENNReal.toReal_nonneg
      refine ENNReal.toReal_mono (ne_of_lt ?_) (measure_mono hsub)
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hWltx
    have hden : 0 < (ν x (Wsh t S (Uminus t) x)).toReal := ENNReal.toReal_pos (ne_of_gt hWposx) (ne_of_lt hWltx)
    have hpos : 0 < (ν x (shape A (Uminus t) x)).toReal / (ν x (Wsh t S (Uminus t) x)).toReal :=
      div_pos (ENNReal.toReal_pos (ne_of_gt hVpos) (ne_of_lt hVlt)) hden
    have hlog : -Real.log (qf x ix) ≤ -Real.log ((ν x (shape A (Uminus t) x)).toReal
        / (ν x (Wsh t S (Uminus t) x)).toReal) :=
      neg_le_neg (Real.log_le_log hpos hratio)
    have hatom : atomInfo A (Uminus t) ν t x = -Real.log ((ν x (shape A (Uminus t) x)).toReal
        / (ν x (Wsh t S (Uminus t) x)).toReal) := by
      rw [atomInfo]
      rfl
    simp only [hΨ]
    rw [hpfx, hxce ix, hatom]
    exact ENNReal.ofReal_le_ofReal hlog
  -- ### 6. assembly
  change ENNReal.ofReal (@Hcond X3 (borel X3) μ P (betaAlg t S)) ≤ _
  rw [Hcond]
  calc ENNReal.ofReal (∫ x, ∑ i : Fin P.n, Real.negMulLog (ce x i) ∂μ)
      ≤ ∫⁻ x, ENNReal.ofReal (∑ i : Fin P.n, Real.negMulLog (ce x i)) ∂μ :=
        ofReal_integral_le_lintegral_ofReal' _
    _ ≤ ∫⁻ x, shapeAvg t S (Uminus t) ν Ψ x ∂μ := lintegral_mono_ae hperx
    _ = ∫⁻ x, Ψ x ∂μ := shapeAvg_lintegral_eq hU hL t hmp hplq hZ Ψ hΨ_meas
    _ ≤ ∫⁻ x, ENNReal.ofReal (atomInfo A (Uminus t) ν t x) ∂μ := lintegral_mono_ae hΦ



end Work.EKLC6Core.HcondSigFree

end
