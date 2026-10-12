import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.Measure.ae_measure_section_right_null
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal BigOperators

-- NOTE: `ℝ³` (and hence every use below) is the *global* notation
-- `notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` of `Submission/Work/BoseKinLoc/Defs.lean`, which is
-- already in the import cone; a second `local notation` would be ambiguous.

/-- **The box projection of an a.e.-vanishing state vanishes a.e.**  (`P_i` = `boxPInd`.)
Route: `P_iΨ(x) = 1_A(x_i)·volA⁻¹∫_A Ψ(update x i z)dz`; peel the integral `∫_{abox N ℓ}|Ψ| = 0`
with `Work.BoseFixB1S.Q0C.abox_peel_transport` (for `N = n+1`; `N = 0` is vacuous) to get the
slice `z ↦ Ψ(kcInsN n i (z,r))` vanishing a.e. for a.e. `r`, hence the slot mean vanishing for
a.e. `x`. -/
theorem boxPInd_ae_eq_zero_of_ae_eq_zero {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ)
    (hΨ : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
    Work.UBBInputs8.boxPInd volA A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
  classical
  rcases N with _ | n
  · exact i.elim0
  -- ### the measure-preserving peel at slot `i`, and its inverse (`kcInsN n i`)
  have hmp : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    Submission.BoseGases.abox_peel_mp (n := n) ℓ i
  have hkc : ∀ x : Submission.BoseGases.X (n + 1),
      Submission.BoseGases.kcInsN n i
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) x) = x := by
    intro x
    simp only [Submission.BoseGases.kcInsN, MeasurableEquiv.symm_apply_apply]
  -- ### the a.e.-zero set in the product space `ℝ³ × X n` is measurable …
  have hZmeas : MeasurableSet {q : ℝ³ × Submission.BoseGases.X n |
      Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0} := by
    have h : MeasurableSet ((fun q : ℝ³ × Submission.BoseGases.X n =>
        Ψ (Submission.BoseGases.kcInsN n i q)) ⁻¹' ({0}ᶜ : Set ℝ)) :=
      (hΨm.comp (Submission.BoseGases.kcInsN n i).measurable) (measurableSet_singleton 0).compl
    convert h using 1
    ext q
    simp
  -- … and the a.e.-zero set in the box is null
  have hnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      {x : Submission.BoseGases.X (n + 1) | Ψ x ≠ 0} = 0 := by
    have hΨ' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)),
        Ψ x = 0 := hΨ
    simpa using MeasureTheory.ae_iff.mp hΨ'
  -- ### … hence the product space set is null
  have hZnull :
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
      {q : ℝ³ × Submission.BoseGases.X n | Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0} = 0 := by
    have hpre : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
        {q : ℝ³ × Submission.BoseGases.X n | Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}
        = {x : Submission.BoseGases.X (n + 1) | Ψ x ≠ 0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [hkc x]
    calc (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
            {q : ℝ³ × Submission.BoseGases.X n | Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}
        = (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
              {q : ℝ³ × Submission.BoseGases.X n |
                Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}) :=
          (hmp.measure_preimage hZmeas.nullMeasurableSet).symm
      _ = (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
            {x : Submission.BoseGases.X (n + 1) | Ψ x ≠ 0} := by rw [hpre]
      _ = 0 := hnull
  -- ### the section function `r ↦ μA {t | Ψ (kcInsN n i (t,r)) ≠ 0}` is measurable …
  have hφmeas : Measurable (fun r : Submission.BoseGases.X n =>
      ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0}) :=
    measurable_measure_prodMk_right
      (μ := (MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)) hZmeas
  -- … so the set of slots whose section does not vanish is measurable …
  have hBadmeas : MeasurableSet {r : Submission.BoseGases.X n |
      ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} := by
    have h : MeasurableSet ((fun r : Submission.BoseGases.X n =>
        ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0}) ⁻¹'
            ({0}ᶜ : Set ℝ≥0∞)) :=
      hφmeas (measurableSet_singleton 0).compl
    convert h using 1
    ext r
    simp
  -- ### Fubini: for a.e. slot the section is null
  have hsec : ∀ᵐ r ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)),
      ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0 :=
    Work.Measure.ae_measure_section_right_null
      ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) hZmeas hZnull
  -- … and hence that set is null
  have hBadnull : ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ))
      {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} = 0 :=
    MeasureTheory.ae_iff.mp hsec
  -- ### the slot mean of `Ψ` over `A` vanishes whenever the section is null
  have hgood : ∀ r : Submission.BoseGases.X n,
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0) →
      (∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))) = 0 := by
    intro r hr
    have h1 : (fun t : ℝ³ => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        =ᵐ[(MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)] 0 :=
      MeasureTheory.ae_iff.mpr (by simpa using hr)
    have h2 : (fun t : ℝ³ => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        =ᵐ[(MeasureTheory.volume : Measure ℝ³).restrict A] 0 := by
      have h := h1.filter_mono (MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_le_self (s := A)))
      rwa [MeasureTheory.Measure.restrict_restrict_of_subset hAc] at h
    rw [MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero]
    rwa [← MeasureTheory.ae_restrict_iff' hA]
  -- ### peels apart `P_iΨ`: it vanishes as soon as the section is null
  have hcover : {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}
      ⊆ Set.univ ×ˢ {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} := by
    rintro ⟨t, r⟩ hq
    exact ⟨Set.mem_univ _, by
      by_contra hcon
      refine hq ?_
      rw [Q0C.boxPInd_kcInsN volA A i Ψ t r, hgood r (by simpa using hcon)]
      ring⟩
  -- ### so `P_iΨ ∘ kcInsN` vanishes `μA ⊗ ν`-a.e. on the product space
  have hSnull : (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)))
      {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0} = 0 := by
    refine le_antisymm ?_ (by simp)
    calc (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
            {q : ℝ³ × Submission.BoseGases.X n |
              Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}
        ≤ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
            (Set.univ ×ˢ {r : Submission.BoseGases.X n |
              ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
                {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)}) :=
          measure_mono hcover
      _ = ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)) Set.univ
            * ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ))
              {r : Submission.BoseGases.X n |
                ¬ (((MeasureTheory.volume : Measure ℝ³).restrict
                    (Submission.BoseGases.acube ℓ))
                  {t : ℝ³ | Ψ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} :=
          Measure.prod_prod _ _
      _ = 0 := by rw [hBadnull, mul_zero]
  -- ### transport back to the box
  have hSnullmeas : NullMeasurableSet
      {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    NullMeasurableSet.of_null hSnull
  have hsetpre : {x : Submission.BoseGases.X (n + 1) |
        Work.UBBInputs8.boxPInd volA A i Ψ x ≠ 0}
      = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
        {q : ℝ³ × Submission.BoseGases.X n |
          Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hkc x]
  have hboxnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      {x : Submission.BoseGases.X (n + 1) | Work.UBBInputs8.boxPInd volA A i Ψ x ≠ 0} = 0 := by
    rw [hsetpre, hmp.measure_preimage hSnullmeas]
    exact hSnull
  exact MeasureTheory.ae_iff.mpr hboxnull

end Work.BoseFixB1S
