import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slice_Xpow_fubini_bdd_cb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slice_Xpow_fubini_bdd_cb_weak`

The Fubini identity splitting the box integral of a sector's excited-count moment into the
complement configuration times the slice, under the **weak** hypotheses on the state:
`Φ` is only assumed measurable, bounded, and supported in the box `abox n ℓ`
(no continuity, and only `Function.support Φ ⊆ abox n ℓ`, not `tsupport`), while the modes `e`
carry the standing regularity `MemLp (e l) ⊤` and `support (e l) ⊆ boxL ℓ`.

This is the statement `Work.BoseBoxFock.slice_Xpow_fubini_bdd_cb` of
`Submission/Work/BoseBoxFock/slice_Xpow_fubini_bdd_cb.lean` (where `Φ` is required to be
*continuous* with `tsupport Φ ⊆ abox n ℓ`), in the form the sector selection actually consumes.

Two points differ from the continuous version, and both are cheap:

* **`MemLp Ψc ⊤` for `Ψc = ((Φ : ℝ) : ℂ)`**: boundedness is `hΦb`, a.e. strong measurability is
  `hΦm`, and the box has finite measure, so the support condition `hΦsupp` upgrades the bound on
  the (finite-measure) box to a global membership: `Ψc` agrees a.e. with the box-indicator of
  `Ψc`, and `memLp_indicator_iff_restrict` together with `MemLp.of_bound` gives the claim.
* **`tsupport Φ ⊆ abox n ℓ`**: `abox n ℓ` is compact (`abox_compact`) for `ℓ > 0`, hence closed,
  and `closure_minimal` upgrades the support hypothesis to the closure hypothesis required by
  `XSpow_slotExact_compl_vanish`.

Everything else (the a.e. boundedness of the sector, the pointwise slice identity of
`XSpow_sliceF_pointwise`, and the Fubini computation along `pairCoord`) is verbatim the
continuous proof, whose cone-free helpers (`psiECb`, `aboxSCb`, `sliceFubiniPairCoord_split_real_cb`,
`integrable_integral_pairCoord_cb`, …) live in `slice_Xpow_fubini_bdd_cb`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

theorem slice_Xpow_fubini_bdd_cb_weak {n m : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (S : Finset (Fin n)) {Φ : Submission.BoseGases.X n → ℝ} (hΦm : Measurable Φ)
    (hΦb : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    (hΦsupp : Function.support Φ ⊆ Submission.BoseGases.abox n ℓ) (j : ℕ) :
    ((∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
        ∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.abox S.card ℓ,
          ‖Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
            (Work.BoseBoxFock.sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.BoseBoxFock.XSpow ℓ S j
            (Work.BoseBoxFock.slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
    ∧ MeasureTheory.Integrable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
        ∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.abox S.card ℓ,
          ‖Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
            (Work.BoseBoxFock.sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2) := by
  classical
  set Ψc : (Fin n → Ω) → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΨc
  obtain ⟨Cb, hCb⟩ := hΦb
  -- the state is `L^∞`: measurable, bounded, and supported in a finite-measure box
  have hΨmem : MeasureTheory.MemLp Ψc ⊤ := by
    have hfin : MeasureTheory.MemLp Ψc ⊤
        ((volume : Measure (Fin n → Ω)).restrict (Submission.BoseGases.abox n ℓ)) := by
      haveI : IsFiniteMeasure
          ((volume : Measure (Fin n → Ω)).restrict (Submission.BoseGases.abox n ℓ)) :=
        ⟨by rw [Measure.restrict_apply_univ]
            exact Submission.BoseGases.abox_lt_top n ℓ hℓ.le⟩
      refine MeasureTheory.MemLp.of_bound ?_ Cb ?_
      · exact ((Complex.measurable_ofReal.comp hΦm).aestronglyMeasurable).mono_measure
          Measure.restrict_le_self
      · filter_upwards with x
        simpa [Ψc] using hCb x
    have hind : MeasureTheory.MemLp
        ((Submission.BoseGases.abox n ℓ).indicator Ψc) ⊤
        (volume : Measure (Fin n → Ω)) :=
      (MeasureTheory.memLp_indicator_iff_restrict
        (Submission.BoseGases.abox_measurable n ℓ)).mpr hfin
    refine hind.ae_eq ?_
    filter_upwards with x
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hx0 : Φ x = 0 := by
        by_contra hne
        exact hx (hΦsupp hne)
      simp [Ψc, hx0]
  -- the box is closed, so the support hypothesis upgrades to the closure hypothesis
  have htsupp : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ :=
    closure_minimal hΦsupp (Submission.BoseGases.abox_compact n hℓ).isClosed
  obtain ⟨hΘmeas0, C0, hΘbdd0⟩ :=
    slotExact_ae_bounded_of_bounded (ℓ := ℓ) (e := e) hbdd hsupp S hΨmem
  set Θ : (Fin n → Ω) → ℂ := slotExact e S Ψc with hΘ
  have hΘmeas : AEStronglyMeasurable Θ (volume : Measure (Fin n → Ω)) := by
    simpa only [hΘ, hΨc] using hΘmeas0
  have hΘbdd : ∃ C, ∀ᵐ x ∂(volume : Measure (Fin n → Ω)), ‖Θ x‖ ≤ C := by
    refine ⟨C0, ?_⟩
    filter_upwards [hΘbdd0] with x hx
    simpa only [hΘ, hΨc] using hx
  obtain ⟨hΘjmeas, Cj, hΘjbdd⟩ := XSpow_aeStronglyMeasurable_ae_bounded ℓ hℓ S hΘmeas hΘbdd j
  have hvan : ∀ x : Fin n → Ω,
      (∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) →
        XSpow ℓ S j Θ x = 0 := by
    intro x hx
    have h := XSpow_slotExact_compl_vanish ℓ hℓ hsupp htsupp S j x hx
    rw [← hΨc, ← hΘ] at h
    exact h
  have hpt : ∀ (y : {i // i ∉ S} → Ω) (u : Fin S.card → Ω),
      XSpow ℓ (Finset.univ : Finset (Fin S.card)) j (sliceF e S Ψc y) u
        = XSpow ℓ S j Θ (pairCoord S (fun i => u (S.equivFin i)) y) := by
    intro y u
    have h := XSpow_sliceF_pointwise (e := e) ℓ S Ψc j y u
    rw [← hΘ] at h
    exact h
  set g : (Fin n → Ω) → ℝ := fun x => ‖XSpow ℓ S j Θ x‖ ^ 2 with hg
  -- integrability of the box-restricted joint integrand
  have hF0int : Integrable (fun x : Fin n → Ω =>
      (Submission.BoseGases.abox n ℓ).indicator g x) := by
    set C' : ℝ := max Cj 0 with hC'def
    have hC'nn : 0 ≤ C' := le_max_right _ _
    have hCb' : ∀ᵐ x ∂(volume : Measure (Fin n → Ω)), ‖XSpow ℓ S j Θ x‖ ≤ C' :=
      hΘjbdd.mono (fun x hx => le_trans hx (le_max_left _ _))
    have haesm : AEStronglyMeasurable (fun x : Fin n → Ω =>
        (Submission.BoseGases.abox n ℓ).indicator g x) volume := by
      refine AEStronglyMeasurable.indicator ?_ (Submission.BoseGases.abox_measurable n ℓ)
      exact hΘjmeas.norm.pow 2
    have hIntC : Integrable (fun x : Fin n → Ω =>
        (Submission.BoseGases.abox n ℓ).indicator (fun _ => C' ^ 2) x) := by
      refine (integrable_indicator_iff (Submission.BoseGases.abox_measurable n ℓ)).mpr ?_
      haveI : IsFiniteMeasure (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n ℓ hℓ.le⟩
      exact integrable_const (C' ^ 2)
    refine Integrable.mono' hIntC haesm ?_
    filter_upwards [hCb'] with x hx
    by_cases hx' : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx', hg]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hx, hC'nn, norm_nonneg (XSpow ℓ S j Θ x)]
    · rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx']
      simp
  -- (1) transport the inner integral from `Fin S.card` to `↥S`
  have hInner : ∀ y : {i // i ∉ S} → Ω,
      (∫ u : Fin S.card → Ω in Submission.BoseGases.abox S.card ℓ,
          ‖XSpow ℓ S j Θ (pairCoord S (fun i => u (S.equivFin i)) y)‖ ^ 2)
        = ∫ ũ : ↥S → Ω in aboxSCb ℓ S, g (pairCoord S ũ y) := by
    intro y
    have hpre : (psiECb S) ⁻¹' (aboxSCb ℓ S) = Submission.BoseGases.abox S.card ℓ := by
      ext u
      simp only [Set.mem_preimage, mem_aboxSCb, Submission.BoseGases.mem_abox_iff]
      rw [psiECb_apply]
      exact ⟨fun h i => by simpa using h (S.equivFin.symm i),
             fun h i => h (S.equivFin i)⟩
    have key := (psiECb_mp S).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding (psiECb S))
      (fun ũ : ↥S → Ω => g (pairCoord S ũ y)) (aboxSCb ℓ S)
    rw [hpre] at key
    rw [← key]
    exact setIntegral_congr_fun (Submission.BoseGases.abox_measurable _ _)
      (fun u _ => by rw [psiECb_apply])
  -- (2) the unrestricted integral over the `S`-slots equals the box-restricted one
  have hA2 : ∀ y : {i // i ∉ S} → Ω,
      (∫ ũ : ↥S → Ω, (Submission.BoseGases.abox n ℓ).indicator g (pairCoord S ũ y))
        = ∫ ũ : ↥S → Ω in aboxSCb ℓ S, g (pairCoord S ũ y) := by
    intro y
    rw [← integral_indicator (measurableSet_aboxSCb ℓ S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ũ => ?_))
    show (Submission.BoseGases.abox n ℓ).indicator g (pairCoord S ũ y)
      = (aboxSCb ℓ S).indicator (fun ũ => g (pairCoord S ũ y)) ũ
    by_cases hmem : pairCoord S ũ y ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem ((pairCoord_mem_abox_cb ũ y).mp hmem).1]
    · by_cases hB : ũ ∈ aboxSCb ℓ S
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem hB]
        change (0 : ℝ) = ‖XSpow ℓ S j Θ (pairCoord S ũ y)‖ ^ 2
        have hy : y ∉ aboxYCb ℓ S :=
          fun hy => hmem ((pairCoord_mem_abox_cb ũ y).mpr ⟨hB, hy⟩)
        rw [mem_aboxYCb] at hy
        simp only [not_forall] at hy
        obtain ⟨i, hi⟩ := hy
        have hzero := hvan (pairCoord S ũ y) ⟨i.1, i.2, by
          rw [pairCoord_notMem S ũ y i.1 i.2]; exact hi⟩
        rw [hzero]; simp
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hB]
  -- (3) the section as a marginal of the box-restricted `XSpow`
  have hsec : ∀ y : {i // i ∉ S} → Ω,
      (∫ u : Fin S.card → Ω in Submission.BoseGases.abox S.card ℓ,
          ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j (sliceF e S Ψc y) u‖ ^ 2)
        = ∫ ũ : ↥S → Ω, (Submission.BoseGases.abox n ℓ).indicator g (pairCoord S ũ y) := by
    intro y
    calc (∫ u : Fin S.card → Ω in Submission.BoseGases.abox S.card ℓ,
          ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j (sliceF e S Ψc y) u‖ ^ 2)
        = ∫ u : Fin S.card → Ω in Submission.BoseGases.abox S.card ℓ,
            ‖XSpow ℓ S j Θ (pairCoord S (fun i => u (S.equivFin i)) y)‖ ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          simp only [hpt y u]
      _ = ∫ ũ : ↥S → Ω in aboxSCb ℓ S, g (pairCoord S ũ y) := hInner y
      _ = ∫ ũ : ↥S → Ω, (Submission.BoseGases.abox n ℓ).indicator g (pairCoord S ũ y) :=
          (hA2 y).symm
  refine ⟨?_, ?_⟩
  · calc (∫ y : {i // i ∉ S} → Ω,
          ∫ u : Fin S.card → Ω in Submission.BoseGases.abox S.card ℓ,
            ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j (sliceF e S Ψc y) u‖ ^ 2)
        = ∫ y : {i // i ∉ S} → Ω,
            ∫ ũ : ↥S → Ω, (Submission.BoseGases.abox n ℓ).indicator g (pairCoord S ũ y) :=
          integral_congr_ae (Filter.Eventually.of_forall hsec)
      _ = ∫ x : Fin n → Ω, (Submission.BoseGases.abox n ℓ).indicator g x :=
          (sliceFubiniPairCoord_split_real_cb S ((Submission.BoseGases.abox n ℓ).indicator g)
            hF0int).symm
      _ = ∫ x in Submission.BoseGases.abox n ℓ, g x :=
          integral_indicator (Submission.BoseGases.abox_measurable n ℓ)
  · refine (integrable_integral_pairCoord_cb S ((Submission.BoseGases.abox n ℓ).indicator g)
      hF0int).congr ?_
    exact Filter.Eventually.of_forall (fun y => (hsec y).symm)

end Work.BoseBoxFock
