import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.Measure.ae_measure_section_right_null
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.boxWords_eq_zero_of_ae_eq_zero`

A state `Ψ : X N → ℝ` that vanishes **almost everywhere** on the analysis box `abox N ℓ`
(no measurability of `Ψ` is assumed) has all four localised box words vanishing:

* `boxFlatCount V ℓ A Ψ = Σᵢ ∫_{abox} (PᵢΨ)²`,
* `boxQCount V ℓ A Ψ = Σᵢ ∫_{abox} (QᵢΨ)²`,
* FS's pairing word `boxA2 ℓ V A w₁ Ψ`,
* the five-word sum `boxQSum V ℓ μ A w w₁ w₂ om Ψ`.

The point is that the box projections `Pᵢ`, `Qᵢ` (`Work.UBBInputs8.boxPInd/boxQInd`) do **not**
preserve almost-everywhere vanishing: `PᵢΨ(x) = (1/V)·1_A(x i)·∫_{z∈A} Ψ(x|i↦z) dz` integrates `Ψ`
over the box, so a.e. vanishing of `Ψ` gives a.e. vanishing of `PᵢΨ` only through a Fubini
argument along the `i`-th coordinate (`boxPInd_ae_eq_zero` below: peel
`abox (n+1) ℓ ≃ acube ℓ × abox n ℓ`, transport a *measurable* null superset of `{Ψ ≠ 0}` and
section it).  Once `PᵢΨ` and `QᵢΨ` vanish a.e. on the box, so do all iterated projections
(`Pᵢ`/`Qᵢ` applied to `P_jΨ`, `Q_jΨ`), every integrand of the words above is pointwise zero off a
null set, and each Bochner integral vanishes by `integral_congr_ae` — no measurability or
integrability of the integrands is needed for that last step.

Nothing here uses any property of the parameters `V = volA`, `ℓ`, `μ` or of the kernels
`w, w₁, w₂, om`: `V` enters only through the scalar `1/V` in `Pᵢ` (any real `V` is allowed,
including `V = 0`), and `ℓ` is unrestricted (for `ℓ ≤ 0` the box `abox N ℓ` is null, so every
integral over it vanishes and the assertion is trivially true).

The Fubini core (`boxPInd_ae_eq_zero` below) is proved here in full; the same statement is also
independently available as `Work.BoseFixB1.SectorAux.boxPInd_ae_eq_zero_of_ae_eq_zero`
(`Submission/Work/BoseFixB1/SectorAux/boxPInd_ae_eq_zero_of_ae_eq_zero.lean`).
-/

namespace Work.BoseFixB1.SectorAux

open MeasureTheory
open scoped ENNReal

/-- **The box condensate projection of an a.e.-vanishing state vanishes a.e.**

`PᵢΨ(x) = (1/V)·1_A(x i)·∫_{z∈A} Ψ(x|i↦z) dz`; the inner integral is `0` as soon as the section
`{z ∈ A | x|i↦z ∈ M}` of a null set `M ⊇ {Ψ ≠ 0}` is null, and by Fubini (after peeling
`abox (n+1) ℓ ≃ acube ℓ × abox n ℓ`) that happens for a.e. `x`.  The null set `M` is made
*measurable* with `toMeasurable`, so no measurability of `Ψ` is required. -/
theorem boxPInd_ae_eq_zero {N : ℕ} {ℓ V : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
    Work.UBBInputs8.boxPInd V A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
  classical
  rcases N with _ | n
  · exact i.elim0
  -- ### the measure-preserving peel at slot `i`, and the identity `kcInsN ∘ e = id`
  have hmp : MeasureTheory.MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    Submission.BoseGases.abox_peel_mp (n := n) ℓ i
  have hkc : ∀ x : Submission.BoseGases.X (n + 1),
      Submission.BoseGases.kcInsN n i
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) x) = x := by
    intro x
    simp only [Submission.BoseGases.kcInsN, MeasurableEquiv.symm_apply_apply]
  -- ### a *measurable* null superset `M` of the set where `Ψ` is nonzero
  set M : Set (Submission.BoseGases.X (n + 1)) :=
    MeasureTheory.toMeasurable
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      {x : Submission.BoseGases.X (n + 1) | Ψ x ≠ 0} with hM
  have hMmeas : MeasurableSet M := MeasureTheory.measurableSet_toMeasurable _ _
  have hMnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) M = 0 := by
    rw [hM, MeasureTheory.measure_toMeasurable]
    simpa using MeasureTheory.ae_iff.mp hΨ
  have hMsub : ∀ x, Ψ x ≠ 0 → x ∈ M := fun x hx => by
    rw [hM]; exact MeasureTheory.subset_toMeasurable _ _ hx
  -- ### its image under the peel is a measurable null set of the product space
  set P : Set (ℝ³ × Submission.BoseGases.X n) :=
    ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) '' M with hP
  have hPmeas : MeasurableSet P := (MeasurableEquiv.measurableSet_image _).2 hMmeas
  have hPnull : (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
        (Submission.BoseGases.acube ℓ)).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))) P = 0 := by
    have hpre : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹' P = M := by
      rw [hP]; exact Set.preimage_image_eq _ (MeasurableEquiv.injective _)
    rw [← hmp.measure_preimage hPmeas.nullMeasurableSet, hpre]
    exact hMnull
  -- ### Fubini: the sections of `P` are a.e. null
  have hsec : ∀ᵐ r ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)),
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | (t, r) ∈ P} = 0 :=
    Work.Measure.ae_measure_section_right_null _ _ hPmeas hPnull
  -- ### so the slot mean of `Ψ` over `A` vanishes for a.e. slot
  have hgood : ∀ r : Submission.BoseGases.X n,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | (t, r) ∈ P} = 0 →
      (∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))) = 0 := by
    intro r hr
    have h1 : (fun t : ℝ³ => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ))] 0 := by
      refine MeasureTheory.ae_iff.mpr (MeasureTheory.measure_mono_null ?_ hr)
      intro t ht
      exact ⟨Submission.BoseGases.kcInsN n i (t, r), hMsub _ ht,
        MeasurableEquiv.apply_symm_apply
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) (t, r)⟩
    have h2 : (fun t : ℝ³ => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict A)] 0 := by
      have h := h1.filter_mono (MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_le_self (s := A)))
      rwa [MeasureTheory.Measure.restrict_restrict_of_subset hAc] at h
    rw [MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero]
    rwa [← MeasureTheory.ae_restrict_iff' hA]
  -- ### the bad set of the projection is contained in `univ × (bad slots)`
  have hcover : {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd V A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0}
      ⊆ Set.univ ×ˢ {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
              (Submission.BoseGases.acube ℓ)) {t : ℝ³ | (t, r) ∈ P} = 0)} := by
    rintro ⟨t, r⟩ hq
    refine ⟨Set.mem_univ _, fun hcon => hq ?_⟩
    rw [Work.BoseFixB1S.Q0C.boxPInd_kcInsN V A i Ψ t r, hgood r hcon]
    ring
  have hBadmeas : MeasurableSet ((Set.univ : Set ℝ³) ×ˢ {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
              (Submission.BoseGases.acube ℓ)) {t : ℝ³ | (t, r) ∈ P} = 0)}) := by
    refine MeasurableSet.univ.prod ?_
    have hφmeas : Measurable (fun r : Submission.BoseGases.X n =>
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | (t, r) ∈ P}) := measurable_measure_prodMk_right hPmeas
    have h := hφmeas (measurableSet_singleton (0 : ℝ≥0∞)).compl
    convert h using 1
    ext r
    simp
  have hBadnull : ((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
      {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
              (Submission.BoseGases.acube ℓ)) {t : ℝ³ | (t, r) ∈ P} = 0)} = 0 :=
    MeasureTheory.ae_iff.mp hsec
  have hBadprod : (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
        (Submission.BoseGases.acube ℓ)).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)))
      (Set.univ ×ˢ {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
              (Submission.BoseGases.acube ℓ)) {t : ℝ³ | (t, r) ∈ P} = 0)}) = 0 := by
    rw [MeasureTheory.Measure.prod_prod, hBadnull, mul_zero]
  -- ### transport back to the box: the preimage of the bad set is null
  have hboxnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      {x : Submission.BoseGases.X (n + 1) | Work.UBBInputs8.boxPInd V A i Ψ x ≠ 0} = 0 := by
    have hsetpre : {x : Submission.BoseGases.X (n + 1) | Work.UBBInputs8.boxPInd V A i Ψ x ≠ 0}
        = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
          {q : ℝ³ × Submission.BoseGases.X n |
            Work.UBBInputs8.boxPInd V A i Ψ (Submission.BoseGases.kcInsN n i q) ≠ 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [hkc x]
    rw [hsetpre]
    refine MeasureTheory.measure_mono_null (Set.preimage_mono hcover) ?_
    rw [hmp.measure_preimage hBadmeas.nullMeasurableSet]
    exact hBadprod
  exact MeasureTheory.ae_iff.mpr hboxnull

/-- **The box mean-free projection of an a.e.-vanishing state vanishes a.e.**:
`QᵢΨ = 1_A(x i)·Ψ − PᵢΨ` and both terms vanish a.e. on the box. -/
theorem boxQInd_ae_eq_zero {N : ℕ} {ℓ V : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
    Work.UBBInputs8.boxQInd V A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
  filter_upwards [hΨ, boxPInd_ae_eq_zero (V := V) hA hAc i hΨ] with x hx hpx
  rw [Work.UBBInputs8.boxQInd, hx, hpx]
  simp only [Pi.zero_apply]
  ring

/-! ## Shaping lemmas for the five-word sum -/

private lemma mul_sub_mul_eq_zero {a b S T : ℝ} (hS : S = 0) (hT : T = 0) : a * S - b * T = 0 := by
  rw [hS, hT]; ring

private lemma add_add_sub_add_eq_zero {a b c d : ℝ} (ha : a = 0) (hb : b = 0) (hc : c = 0)
    (hd : d = 0) : (a + b - c) + d = 0 := by
  rw [ha, hb, hc, hd]; ring

private lemma two_mul_aux {a : ℝ} (ha : a = 0) : (2 : ℝ) * a = 0 := by rw [ha]; ring

private lemma half_mul_aux {a : ℝ} (ha : a = 0) : (1 / 2 : ℝ) * a = 0 := by rw [ha]; ring

theorem boxWords_eq_zero_of_ae_eq_zero {N : ℕ} (ℓ V μ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (w w₁ w₂ om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (h : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
    Work.BoseFixB1S.boxFlatCount V ℓ A Ψ = 0
      ∧ Work.BoseFixB1S.boxQCount V ℓ A Ψ = 0
      ∧ Work.BoseFixB1.boxA2 ℓ V A w₁ Ψ = 0
      ∧ Work.BoseFixB1S.boxQSum V ℓ μ A w w₁ w₂ om Ψ = 0 := by
  classical
  rcases N with _ | n
  · -- no particles: every word is an empty sum
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_eq_zero (fun i _ => i.elim0)
    · rw [Work.BoseFixB1S.boxQCount]
      exact Finset.sum_eq_zero (fun i _ => i.elim0)
    · rw [Work.BoseFixB1.boxA2]
      exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
    · rw [Work.BoseFixB1S.boxQSum]
      have h0 : Work.BoseFixB1S.boxQ0 V ℓ μ A w₁ w₂ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ0]
        refine mul_sub_mul_eq_zero ?_ ?_
        · exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
        · exact Finset.sum_eq_zero (fun i _ => i.elim0)
      have h1 : Work.BoseFixB1S.boxQ1 V ℓ μ A w₁ w₂ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ1]
        refine mul_sub_mul_eq_zero ?_ ?_
        · exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
        · exact Finset.sum_eq_zero (fun i _ => i.elim0)
      have h2 : Work.BoseFixB1S.boxQ2 V ℓ μ A w₁ w₂ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ2]
        refine add_add_sub_add_eq_zero ?_ ?_ ?_ ?_
        · exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
        · exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
        · rw [Finset.sum_eq_zero (fun i _ => i.elim0)]
          ring
        · exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
      have h3 : Work.BoseFixB1S.boxQ3 V ℓ A w₁ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ3]
        refine two_mul_aux ?_
        exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
      have h4 : Work.BoseFixB1S.boxQ4 V ℓ A w om Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ4]
        refine half_mul_aux ?_
        exact Finset.sum_eq_zero (fun p _ => p.1.elim0)
      rw [h0, h1, h2, h3, h4]
      ring
  · -- at least one particle
    have hP : ∀ i : Fin (n + 1), Work.UBBInputs8.boxPInd V A i Ψ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 :=
      fun i => boxPInd_ae_eq_zero (V := V) hA hAc i h
    have hQ : ∀ i : Fin (n + 1), Work.UBBInputs8.boxQInd V A i Ψ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 :=
      fun i => boxQInd_ae_eq_zero (V := V) hA hAc i h
    have hPP : ∀ i j : Fin (n + 1),
        Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Ψ)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 :=
      fun i j => boxPInd_ae_eq_zero (V := V) hA hAc i (hP j)
    have hPQ : ∀ i j : Fin (n + 1),
        Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Ψ)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 :=
      fun i j => boxPInd_ae_eq_zero (V := V) hA hAc i (hQ j)
    have hQP : ∀ i j : Fin (n + 1),
        Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxPInd V A j Ψ)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 :=
      fun i j => boxQInd_ae_eq_zero (V := V) hA hAc i (hP j)
    have hQQ : ∀ i j : Fin (n + 1),
        Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxQInd V A j Ψ)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 :=
      fun i j => boxQInd_ae_eq_zero (V := V) hA hAc i (hQ j)
    -- every integral over the box of an a.e.-vanishing integrand vanishes
    have key : ∀ f : Submission.BoseGases.X (n + 1) → ℝ,
        f =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)] 0 →
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ, f x) = 0 := by
      intro f hf
      rw [MeasureTheory.integral_congr_ae hf]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_eq_zero (fun i _ => key _ (by
        filter_upwards [hP i] with x hx
        simp [hx]))
    · rw [Work.BoseFixB1S.boxQCount]
      exact Finset.sum_eq_zero (fun i _ => key _ (by
        filter_upwards [hQ i] with x hx
        simp [hx]))
    · rw [Work.BoseFixB1.boxA2]
      exact Finset.sum_eq_zero (fun p _ => key _ (by
        filter_upwards [hPP p.1 p.2, hQQ p.2 p.1] with x hx hy
        simp [hx, hy]))
    · rw [Work.BoseFixB1S.boxQSum]
      have h0 : Work.BoseFixB1S.boxQ0 V ℓ μ A w₁ w₂ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ0]
        refine mul_sub_mul_eq_zero ?_ ?_
        · exact Finset.sum_eq_zero (fun p _ => key _ (by
            filter_upwards [hPP p.1 p.2] with x hx
            simp [hx]))
        · exact Finset.sum_eq_zero (fun i _ => key _ (by
            filter_upwards [hP i] with x hx
            simp [hx]))
      have h1 : Work.BoseFixB1S.boxQ1 V ℓ μ A w₁ w₂ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ1]
        refine mul_sub_mul_eq_zero ?_ ?_
        · exact Finset.sum_eq_zero (fun p _ => key _ (by
            filter_upwards [hPQ p.1 p.2, hPP p.1 p.2] with x hx hy
            simp [hx, hy]))
        · exact Finset.sum_eq_zero (fun i _ => key _ (by
            filter_upwards [hQ i, hP i] with x hx hy
            simp [hx, hy]))
      have h2 : Work.BoseFixB1S.boxQ2 V ℓ μ A w₁ w₂ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ2]
        refine add_add_sub_add_eq_zero ?_ ?_ ?_ ?_
        · exact Finset.sum_eq_zero (fun p _ => key _ (by
            filter_upwards [hPQ p.1 p.2, hPQ p.2 p.1] with x hx hy
            simp [hx, hy]))
        · exact Finset.sum_eq_zero (fun p _ => key _ (by
            filter_upwards [hPQ p.1 p.2, hQP p.2 p.1] with x hx hy
            simp [hx, hy]))
        · rw [Finset.sum_eq_zero (fun i _ => key _ (by
            filter_upwards [hQ i] with x hx
            simp [hx]))]
          ring
        · exact Finset.sum_eq_zero (fun p _ => key _ (by
            filter_upwards [hPP p.1 p.2, hQQ p.2 p.1] with x hx hy
            simp [hx, hy]))
      have h3 : Work.BoseFixB1S.boxQ3 V ℓ A w₁ Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ3]
        refine two_mul_aux ?_
        exact Finset.sum_eq_zero (fun p _ => key _ (by
          filter_upwards [hPQ p.1 p.2, hQQ p.2 p.1] with x hx hy
          simp [hx, hy]))
      have h4 : Work.BoseFixB1S.boxQ4 V ℓ A w om Ψ = 0 := by
        rw [Work.BoseFixB1S.boxQ4]
        refine half_mul_aux ?_
        exact Finset.sum_eq_zero (fun p _ => key _ (by
          filter_upwards [hQQ p.2 p.1, hPP p.2 p.1, hPQ p.2 p.1, hQP p.2 p.1] with x ha hb hc hd
          simp only [Pi.zero_apply] at ha hb hc hd
          have hb4 : Work.BoseFixB1S.boxQ4B V A om Ψ p x = 0 := by
            rw [Work.BoseFixB1S.boxQ4B, ha, hb, hc, hd]
            ring
          rw [hb4]
          simp))
      rw [h0, h1, h2, h3, h4]
      ring

end Work.BoseFixB1.SectorAux
