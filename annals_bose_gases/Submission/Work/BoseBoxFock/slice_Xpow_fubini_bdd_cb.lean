import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded
import Submission.Work.BoseBoxFock.XSpow_sliceF_pointwise
import Submission.Work.BoseBoxFock.XSpow_slotExact_compl_vanish
import Submission.Work.BoseBoxFock.slotExact_ae_bounded_of_bounded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Cone-free copies of the Fubini helpers of `slice_Xpow_fubini_bdd`

The modules `Submission.Work.BoseBoxFock.slice_Xpow_fubini_bdd` and
`…/slice_XSpow_iterate_integrable` cannot be imported here (their cone contains
`slotExact_aeStronglyMeasurable_ae_bounded`, whose `slotExactAux_ae_forall_eval_le` clashes with
the copy in `slotExact_ae_bounded_of_bounded`), so the (cone-free) auxiliary results they use are
reproduced below under fresh names. -/

/-- The index permutation `Fin S.card ≃ ↥S` (copy of `psiE`). -/
noncomputable def psiECb {n : ℕ} (S : Finset (Fin n)) : (Fin S.card → Ω) ≃ᵐ (↥S → Ω) :=
  MeasurableEquiv.piCongrLeft (fun _ : ↥S => Ω) (S.equivFin.symm)

lemma psiECb_apply {n : ℕ} (S : Finset (Fin n)) (u : Fin S.card → Ω) :
    psiECb S u = fun i : ↥S => u (S.equivFin i) := by
  funext i
  have h := Equiv.piCongrLeft_apply_apply (fun _ : ↥S => Ω) (S.equivFin.symm) u (S.equivFin i)
  simpa [psiECb, MeasurableEquiv.coe_piCongrLeft] using h

lemma psiECb_mp {n : ℕ} (S : Finset (Fin n)) :
    MeasurePreserving (⇑(psiECb S)) (volume : Measure (Fin S.card → Ω))
      (volume : Measure (↥S → Ω)) :=
  volume_measurePreserving_piCongrLeft (fun _ : ↥S => Ω) (S.equivFin.symm)

/-- The box on the `S`-slots. -/
def aboxSCb {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) : Set (↥S → Ω) :=
  Set.univ.pi (fun _ : ↥S => Submission.BoseGases.acube ℓ)

/-- The box on the complement slots. -/
def aboxYCb {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) : Set ({i // i ∉ S} → Ω) :=
  Set.univ.pi (fun _ : {i // i ∉ S} => Submission.BoseGases.acube ℓ)

lemma mem_aboxSCb {n : ℕ} {S : Finset (Fin n)} {ℓ : ℝ} {ũ : ↥S → Ω} :
    ũ ∈ aboxSCb ℓ S ↔ ∀ i : ↥S, ũ i ∈ Submission.BoseGases.acube ℓ := by
  simp [aboxSCb, Set.mem_pi]

lemma mem_aboxYCb {n : ℕ} {S : Finset (Fin n)} {ℓ : ℝ} {y : {i // i ∉ S} → Ω} :
    y ∈ aboxYCb ℓ S ↔ ∀ i : {i // i ∉ S}, y i ∈ Submission.BoseGases.acube ℓ := by
  simp [aboxYCb, Set.mem_pi]

lemma measurableSet_aboxSCb {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) :
    MeasurableSet (aboxSCb ℓ S) := by
  rw [aboxSCb]
  exact MeasurableSet.pi Set.countable_univ
    (fun i _ => Submission.BoseGases.acube_measurable ℓ)

lemma pairCoord_mem_abox_cb {n : ℕ} {S : Finset (Fin n)} {ℓ : ℝ}
    (ũ : ↥S → Ω) (y : {i // i ∉ S} → Ω) :
    pairCoord S ũ y ∈ Submission.BoseGases.abox n ℓ ↔ ũ ∈ aboxSCb ℓ S ∧ y ∈ aboxYCb ℓ S := by
  rw [mem_aboxSCb, mem_aboxYCb, Submission.BoseGases.mem_abox_iff]
  constructor
  · intro h
    exact ⟨fun i => by rw [← pairCoord_mem S ũ y i.1 i.2]; exact h i.1,
           fun i => by rw [← pairCoord_notMem S ũ y i.1 i.2]; exact h i.1⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i ∈ S
    · rw [pairCoord_mem S ũ y i hi]; exact h1 ⟨i, hi⟩
    · rw [pairCoord_notMem S ũ y i hi]; exact h2 ⟨i, hi⟩

/-- The inverse of the slot-splitting equivalence is `pairCoord`. -/
lemma sliceFubiniPairCoord_symm_cb {n : ℕ} (S : Finset (Fin n)) :
    ⇑((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm)
      = fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) => pairCoord S q.1 q.2 := by
  funext q
  obtain ⟨u, y⟩ := q
  funext i
  by_cases h : i ∈ S <;> simp [pairCoord, h]

/-- **The Fubini splitting of a configuration-space integral along the slot set `S`**
(`ℝ`-valued copy of `sliceFubiniPairCoord_split_real`). -/
theorem sliceFubiniPairCoord_split_real_cb {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℝ)
    (hF : MeasureTheory.Integrable F) :
    ∫ x, F x = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω, F (pairCoord S u y) := by
  classical
  have hinst : (Finset.Subtype.fintype S : Fintype {i // i ∈ S}) =
      Subtype.fintype (fun i : Fin n => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S))
      (volume : Measure (Fin n → Ω))
      (volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
  have hF' : MeasureTheory.Integrable (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) =>
      F (pairCoord S q.1 q.2)) := by
    have h := (hmp.symm.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm)).mpr hF
    refine h.congr ?_
    filter_upwards with q
    rw [Function.comp_apply, sliceFubiniPairCoord_symm_cb]
  calc ∫ x, F x
      = ∫ q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω),
          F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω)
            (fun i => i ∈ S)).symm q) := (hmp.symm.integral_comp' F).symm
    _ = ∫ q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω), F (pairCoord S q.1 q.2) := by
        apply integral_congr_ae
        filter_upwards with q
        rw [sliceFubiniPairCoord_symm_cb]
    _ = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω, F (pairCoord S u y) :=
        integral_prod_symm _ hF'

/-- **`pairCoord` transports integrability** (copy of `integrable_pairCoord_prod`). -/
lemma integrable_pairCoord_prod_cb {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℝ)
    (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable
      (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) => F (pairCoord S q.1 q.2)) := by
  classical
  have hinst : (Finset.Subtype.fintype S : Fintype {i // i ∈ S}) =
      Subtype.fintype (fun i : Fin n => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S))
      (volume : Measure (Fin n → Ω))
      (volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
  have h := (hmp.symm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm)).mpr hF
  refine h.congr ?_
  filter_upwards with q
  rw [Function.comp_apply, sliceFubiniPairCoord_symm_cb]

/-- **The marginal of an integrable function along the slot splitting is integrable**
(copy of `integrable_integral_pairCoord`). -/
lemma integrable_integral_pairCoord_cb {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℝ)
    (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
      ∫ u : {i // i ∈ S} → Ω, F (pairCoord S u y)) :=
  (integrable_pairCoord_prod_cb S F hF).integral_prod_right

/-- **A cone-independent copy of the Fubini identity `slice_Xpow_fubini_bdd` together with its
`Integrable` refinement `slice_XSpow_iterate_integrable`.**

`Submission/Work/BoseBoxFock/slice_Xpow_fubini_bdd.lean` and
`…/slice_XSpow_iterate_integrable.lean` prove exactly these two facts, but their proofs use
`Work.BoseBoxFock.slotExact_aeStronglyMeasurable_ae_bounded`, which declares
`Work.BoseBoxFock.slotExactAux_ae_forall_eval_le` — a name that is *also* declared by
`Work.BoseBoxFock.slotExact_ae_bounded_of_bounded`, so those two modules can never be imported
together. The present result is the copy in the *other* cone: it may only import the modules listed
in `depends_on` (in particular NOT `slice_Xpow_fubini_bdd`, `slice_XSpow_iterate_integrable`, or
`slotExact_aeStronglyMeasurable_ae_bounded`), and must obtain the a.e. strong measurability and
a.e. boundedness of `Θ = slotExact e S (fun x => ((Φ x : ℝ) : ℂ))` from
`Work.BoseBoxFock.slotExact_ae_bounded_of_bounded` instead (feeding it `MemLp Ψ ⊤`, which follows
from `hΦ` continuous, `hΦc`, and the compactness of `abox n ℓ`).

The proof of the first conjunct is a copy of the proof of `slice_Xpow_fubini_bdd` (the auxiliary
results `psiE`, `psiE_apply`, `psiE_mp`, `aboxS`, `aboxY`, `mem_aboxS`, `mem_aboxY`,
`measurableSet_aboxS`, `pairCoord_mem_abox`, `sliceFubiniPairCoord_symm`,
`sliceFubiniPairCoord_split_real` in that file are all cone-free and should be copied under fresh
names); the second conjunct is a copy of the proof of `slice_XSpow_iterate_integrable`. -/
theorem slice_Xpow_fubini_bdd_cb {n m : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (S : Finset (Fin n)) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) (j : ℕ) :
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
  -- the state is `L^∞`: it is continuous with compact support
  have hΨmem : MeasureTheory.MemLp Ψc ⊤ := by
    rw [hΨc]
    have hK : IsCompact (Submission.BoseGases.abox n ℓ) :=
      Submission.BoseGases.abox_compact n hℓ
    have hts : IsCompact (tsupport Φ) := hK.of_isClosed_subset isClosed_closure hΦc
    have hcs : HasCompactSupport Φ := hts
    exact (Complex.continuous_ofReal.comp hΦ).memLp_of_hasCompactSupport
      (hcs.comp_left (by simp))
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
    have h := XSpow_slotExact_compl_vanish ℓ hℓ hsupp hΦc S j x hx
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
    have hCb : ∀ᵐ x ∂(volume : Measure (Fin n → Ω)), ‖XSpow ℓ S j Θ x‖ ≤ C' :=
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
    filter_upwards [hCb] with x hx
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
