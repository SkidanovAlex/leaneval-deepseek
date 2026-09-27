import Mathlib
import Submission.Work.EKLC6Core.AtomInfoSetup
import Submission.Work.EKLC6Core.ShapeAvgDefs
import Submission.Work.EKLC6Core.ae_Wsh_inter_null
import Submission.Work.EKLC6Core.shapeAvg_lintegral_eq
import Submission.Work.EKLC6Core.ofReal_sum_negMulLog_le_lintegral_div
import Submission.Work.EKLC6Core.HcondSig_aux
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.growth_le_atomInfo

/-!
# `EKLC6Core.HcondSig_le_lintegral_atomInfo`

`HcondSig μ A (comap (aDiag t ·) A) ≤ ∫⁻ x, ENNReal.ofReal (atomInfo A (Uminus t) ν t x) ∂μ`

for an `A`-ergodic probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a leaf-wise system `ν = μ_x^U` for
the contracted horospherical subgroup `U = Uminus t`, and an `aDiag t ·`-descending plaque
algebra `A` (Pisa 7.34/7.35, `≤` half of the shape comparison).

## Structure of the proof

Fix a finite partition `P` with `partSigma P ≤ A`; we must bound `ofReal (Hcond μ P β)` by the
integral of the pointwise surprisal, where `β = comap (aDiag t ·) A`.

* `Hcond μ P β = ∫ x, Σᵢ -𝔼[1_{Pᵢ}|β](x) log 𝔼[1_{Pᵢ}|β](x) dμ` (the definition), so it is at most
  `∫⁻ x, ofReal (Hx x)`, by the elementary `ofReal_integral_le_lintegral_ofReal`.
* The *pointwise* information inequality (Pisa 7.34), for a.e. `x`:
  `ofReal (Hx x) ≤ shapeAvg t S U ν Ψ x`, where `S = ⟨A⟩`, `Ψ y = ofReal (-log (pf y))` is the
  **measurable** function whose value at `y` is the negative logarithm of the conditional
  probability (given `β`) of the `P`-piece containing `y`.
  This is `ofReal_sum_negMulLog_le_lintegral_div` (an abstract entropy bound) applied to the
  finite partition `{Dpart t S U P i x}ᵢ` of the pull-back shape `Wsh t S U x`, with the a.e.
  comparison `qᵢ(x) ≥ pf(u • x)` for `ν x`-a.e. `u ∈ Dpart t S U P i x`.  The latter comes from
  * the leafwise constancy of the pull-back conditional probability (`Dpart_ratio_eq_of_mem_Wsh`,
    from `hcsg_equivariant_shape_mass`, Pisa 7.16), which says
    `qᵢ(x) = ν y(Dpart t S U P i y)/ν y(Wsh t S U y)` for `y = u • x`;
  * the `condexp` field of `IsLeafwise` (`hcsg_ae_condExp_eq_shape_ratio`), transferred to the
    leaves by `ae_Wsh_inter_null` — the transfer needs a *measurable* null set, supplied by
    `MeasureTheory.exists_measurable_superset_of_null` applied to the a.e. equality.
* `∫⁻ x, shapeAvg t S U ν Ψ x ∂μ = ∫⁻ x, Ψ x ∂μ` (`lintegral_shapeAvg_eq`: the shape average is
  the conditional expectation w.r.t. the pull-back plaque algebra).
* `Ψ ≤ ofReal ∘ atomInfo` a.e., because the `A`-atom of `x` is contained in the `P`-piece of `x`
  and `β ≤ A`; hence the last integral is at most the target's right-hand side.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- Unconditional form of `ofReal_integral_le_lintegral_ofReal`: when `f` is not integrable the
Bochner integral is `0` and the inequality is trivial. -/
theorem ofReal_integral_le_lintegral_ofReal' {μ : Measure X3} (f : X3 → ℝ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · exact ofReal_integral_le_lintegral_ofReal h
  · rw [integral_undef h]
    simp

/-! ## The leafwise constancy of the pull-back conditional probability -/

/-- **Pisa 7.16 in ratio form.**  If `u` lies in the pull-back shape `Wsh t S U x`, then the
`ν`-mass ratio of the piece `P.parts i` inside the pull-back atom is the same at `x` and at
`u • x` (`Dpart` is the shape of the pull-back atom intersected with the preimage of `P.parts i`).

This is the ratio form of `hcsg_equivariant_shape_mass`: the two sides are the `ν`-conditional
probabilities of `P.parts i` at the two points of the same leaf. -/
theorem Dpart_ratio_eq_of_mem_Wsh {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (t : Fin 3 → ℝ) {S : Work.EKLRelCross.MSAlg} {Z : Set X3}
    (hA : IsPlaqueAlgebra U Z S.m) {P : FinPart X3}
    {x : X3} (hxX' : x ∈ X') {u : SL3} (hyX' : u • x ∈ X')
    (huW : u ∈ Wsh t S U x) (hxTZ : x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z)
    (hyTZ : u • x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z) (i : Fin P.n) :
    (ν x (Dpart t S U P i x)).toReal / (ν x (Wsh t S U x)).toReal
      = (ν (u • x) (Dpart t S U P i (u • x))).toReal
        / (ν (u • x) (Wsh t S U (u • x))).toReal := by
  have huU : u ∈ U := huW.1
  have hβA : IsPlaqueAlgebra U ((fun y : X3 => aDiag t • y) ⁻¹' Z) (betaAlg t S) :=
    isPlaqueAlgebra_betaAlg hU hA t
  -- equivariance of the leafwise system along the leaf
  obtain ⟨c, hc0, hctop, hceq⟩ := hL.equivariant x hxX' u huU hyX'
  -- measurability
  have hWmeas : MeasurableSet (Wsh t S U x) :=
    measurableSet_shape hU hβA hxTZ
  have hcont : Continuous (fun g : SL3 => g • x) := continuous_id.smul continuous_const
  have hDmeas : MeasurableSet (Dpart t S U P i x) :=
    hWmeas.inter ((P.measurable i).preimage hcont.measurable)
  -- the two preimage identities along `g ↦ g * u`
  have hshape : ∀ g : SL3, g • u • x = (g * u) • x := fun g => by rw [mul_smul]
  have hmem : ∀ g : SL3, (g * u ∈ U ↔ g ∈ U) := fun g => by
    constructor
    · intro h
      have := U.mul_mem h (U.inv_mem huU)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at this
    · intro h; exact U.mul_mem h huU
  have hatom : atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) (u • x)
      = atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) x :=
    hcsg_atom_eq_of_mem (show u • x ∈ atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) x
      from huW.2)
  have hsetW : (fun g : SL3 => g * u) ⁻¹' (Wsh t S U x) = Wsh t S U (u • x) := by
    ext g
    simp only [Wsh_def, betaAlg_def, shape, Set.mem_preimage, Set.mem_ofPred_eq, hshape g, hatom,
      hmem g]
  have hsetD : (fun g : SL3 => g * u) ⁻¹' (Dpart t S U P i x) = Dpart t S U P i (u • x) := by
    rw [Dpart_def, Dpart_def, Set.preimage_inter, hsetW]
    congr 1
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hshape g]
  -- the two mass identities
  have hf : Measurable (fun g : SL3 => g * u) := (continuous_id.mul continuous_const).measurable
  have hmassW : ν x (Wsh t S U x) = c * ν (u • x) (Wsh t S U (u • x)) := by
    rw [hceq, Measure.smul_apply, Measure.map_apply hf hWmeas, hsetW, smul_eq_mul]
  have hmassD : ν x (Dpart t S U P i x) = c * ν (u • x) (Dpart t S U P i (u • x)) := by
    rw [hceq, Measure.smul_apply, Measure.map_apply hf hDmeas, hsetD, smul_eq_mul]
  have hdiv : ν x (Dpart t S U P i x) / ν x (Wsh t S U x)
      = ν (u • x) (Dpart t S U P i (u • x)) / ν (u • x) (Wsh t S U (u • x)) := by
    rw [hmassW, hmassD, ENNReal.mul_div_mul_left _ _ hc0 hctop]
  rw [← ENNReal.toReal_div, ← ENNReal.toReal_div, hdiv]


/-- **Transfer of a `μ`-null measurable set to the leaves, membership form**: for `μ`-a.e. `x`,
`ν x`-a.e. point of the pull-back shape `Wsh t S U x` lands *outside* `M`. -/
theorem ae_Wsh_mem_of_null {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (t : Fin 3 → ℝ) (hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    {M : Set X3} (hM : MeasurableSet M) (hM0 : μ M = 0)
    {S : Work.EKLRelCross.MSAlg} {Z : Set X3} (hA : IsPlaqueAlgebra U Z S.m) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ u ∂(ν x), u ∈ Wsh t S U x → u • x ∉ M := by
  have hnull := ae_Wsh_inter_null hU hL t hmp hM hM0 hA hZ
  filter_upwards [hnull] with x hx
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun u hu => ?_) hx
  refine ⟨?_, ?_⟩
  · by_contra hW; exact hu fun hW' => absurd hW' hW
  · by_contra hMx; exact hu fun _ => hMx

/-! ## The target theorem -/

theorem HcondSig_le_lintegral_atomInfo {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
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
  have hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ := hErg.1 t
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

end Work.EKLC6Core

end
