import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.ThetaDefs
import Submission.Work.SlotWord.qLHSden_slotComb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.qLHSword_slotFibre` — the potential word factorises at the fibre

The hypothesis `Submission.BoseGases.qLHSword` is a *multiplication form*
(`Submission.BoseGases.qLHSword_eq_integral_qLHSden`): it is the `abox N L`-integral of the square
of the state against the diagonal density `qLHSden`.  Both the density and the state split along the
slot reassembly `slotTheta S e` of `ThetaDefs.lean`:

* the state: `slotPiece (dlBox L d u) S Φ (slotTheta S e (x, y))` is, by definition, the fibre
  `slotFibreState S e (slotPiece …) y x`;
* the density: the truncation hypotheses `hsupp1`, `hsupp2` kill every one-body integral and every
  pair term containing a coordinate outside the sliding box `dlBox L d u`, so the `N`-particle
  density at the reassembled configuration is the `|S|`-particle density of `x`
  (`Work.SlotWord.qLHSden_slotComb`).

`slotTheta` is measure preserving and pulls `abox N L` back to
`abox |S| L × slotOutside L (dlBox L d u) S`, so the `abox N L`-integral is the iterated integral
over the outside configurations and the `|S|`-particle box, which is exactly the fibre factorisation.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector
open Work.PerSector.Work.PerSector (slotBox_measurable slotBox_mono)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- The fibre factorisation of the potential word, for an arbitrary state `Ψ` supported on the slot
set of `S`. -/
theorem qLHSword_slotFibre_aux {N : ℕ} (L d μ : ℝ) (u : ℝ³) (S : Finset (Fin N))
    (Ψ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (w w1 : ℝ³ → ℝ³ → ℝ)
    (hsupp1 : ∀ x : ℝ³, x ∉ dlBox L d u → ∀ y : ℝ³, w1 x y = 0)
    (hsupp2 : ∀ x y : ℝ³, (x ∉ dlBox L d u ∨ y ∉ dlBox L d u) → w x y = 0)
    (hΨ : ∀ x : X N, x ∉ slotSet (dlBox L d u) S → Ψ x = 0)
    (hint : IntegrableOn (fun x : X N => (Ψ x) ^ 2 * qLHSden N L μ w w1 x) (abox N L)) :
    qLHSword (N := N) L μ w w1 Ψ
      = ∫ y in slotOutside L (dlBox L d u) S,
          qLHSword (N := S.card) L μ w w1 (slotFibreState S e Ψ y) := by
  classical
  let B : Set ℝ³ := dlBox L d u
  let t : Set (X S.card × (SlotOut N S → ℝ³)) :=
    abox S.card L ×ˢ slotBox (ι := SlotOut N S) (acube L)
  let U : Set (X S.card × (SlotOut N S → ℝ³)) :=
    abox S.card L ×ˢ slotOutside L B S
  let F : X N → ℝ := fun x => (Ψ x) ^ 2 * qLHSden N L μ w w1 x
  let G : X S.card × (SlotOut N S → ℝ³) → ℝ :=
    fun p => (slotFibreState S e Ψ p.2 p.1) ^ 2 * qLHSden S.card L μ w w1 p.1
  rw [qLHSword_eq_integral_qLHSden (N := N) L μ w w1 Ψ]
  simp_rw [qLHSword_eq_integral_qLHSden]
  change ∫ x in abox N L, F x
      = ∫ y in slotOutside L B S, ∫ x in abox S.card L, G (x, y)
  -- Change of variables along the slot reassembly.
  have hmp := slotTheta_measurePreserving S e
  have hcv : ∫ x in abox N L, F x
      = ∫ p in (slotTheta S e) ⁻¹' (abox N L), F (slotTheta S e p) :=
    (hmp.setIntegral_preimage_emb (slotTheta S e).measurableEmbedding F (abox N L)).symm
  rw [slotTheta_preimage_abox S e L] at hcv
  have hInt : IntegrableOn (fun p : X S.card × (SlotOut N S → ℝ³) => F (slotTheta S e p))
      ((slotTheta S e) ⁻¹' (abox N L)) volume :=
    (hmp.integrableOn_comp_preimage (slotTheta S e).measurableEmbedding (f := F)
      (s := abox N L)).mpr hint
  rw [slotTheta_preimage_abox S e L] at hInt
  -- The two domains.
  have hUt : U ⊆ t := by
    intro p hp
    dsimp only [U, t] at hp ⊢
    exact ⟨hp.1, slotBox_mono Set.inter_subset_left hp.2⟩
  have hUmeas : MeasurableSet U := by
    dsimp only [U, B]
    refine MeasurableSet.prod (abox_measurable S.card L) ?_
    rw [slotOutside]
    exact slotBox_measurable
      ((acube_measurable L).inter (Work.SmallBoxSliding.measurableSet_dlBox L d u).compl)
  have hIntU : IntegrableOn (fun p => F (slotTheta S e p)) U volume := hInt.mono_set hUt
  -- The pointwise identity on the reduced domain.
  have hpt : Set.EqOn (fun p => F (slotTheta S e p)) G U := by
    intro p hp
    have hfib : slotFibreState S e Ψ p.2 p.1 = Ψ (slotTheta S e p) := by
      rw [slotFibreState_apply, slotTheta_apply]
    dsimp only [F, G]
    rw [hfib]
    by_cases h0 : Ψ (slotTheta S e p) = 0
    · simp only [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · have hmem : slotTheta S e p ∈ slotSet B S := by
        by_contra hc
        exact h0 (hΨ _ hc)
      have hy : ∀ j : SlotOut N S, p.2 j ∉ B := ((slotTheta_mem_slotSet_iff S e p).mp hmem).2
      have hden : qLHSden N L μ w w1 (slotTheta S e p)
          = qLHSden S.card L μ w w1 p.1 := by
        rw [slotTheta_apply]
        exact qLHSden_slotComb L d μ u S e w w1 hsupp1 hsupp2 p.1 p.2 hy
      rw [hden]
  have hIntG : IntegrableOn G U volume := hIntU.congr_fun hpt hUmeas
  -- The reassembled integrand vanishes off the reduced domain.
  have hzero : ∫ p in t \ U, F (slotTheta S e p) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro p hp
    rw [Set.mem_sdiff] at hp
    obtain ⟨hpt, hpU⟩ := hp
    dsimp only [t] at hpt
    have hyB : ∃ j : SlotOut N S, p.2 j ∈ B := by
      by_contra hc
      apply hpU
      dsimp only [U]
      refine ⟨hpt.1, ?_⟩
      rw [mem_slotOutside_iff]
      exact ⟨fun j => mem_slotBox_iff.mp hpt.2 j, fun j hmem => hc ⟨j, hmem⟩⟩
    obtain ⟨j, hj⟩ := hyB
    have hnotmem : slotTheta S e p ∉ slotSet B S := by
      intro hcon
      exact ((slotTheta_mem_slotSet_iff S e p).mp hcon).2 j hj
    have hΨ0 : Ψ (slotTheta S e p) = 0 := hΨ _ hnotmem
    dsimp only [F]
    rw [hΨ0]
    ring
  -- Split the integral: the reduced domain carries everything.
  have hsplit := integral_inter_add_sdiff (f := fun p => F (slotTheta S e p))
    (s := t) (t := U) hUmeas hInt
  rw [Set.inter_eq_right.mpr hUt, hzero, add_zero] at hsplit
  -- Fubini on the reduced domain, in the outside-configuration-outer order.
  have hIntG' : Integrable G (((volume : Measure (X S.card)).restrict (abox S.card L)).prod
      ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L (dlBox L d u) S))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod (X S.card) (SlotOut N S → ℝ³)]
    exact hIntG
  have hFub : ∫ p in U, G p = ∫ y in slotOutside L B S, ∫ x in abox S.card L, G (x, y) := by
    dsimp only [U, B]
    rw [Measure.volume_eq_prod (X S.card) (SlotOut N S → ℝ³)]
    rw [← Measure.prod_restrict (μ := (volume : Measure (X S.card)))
      (ν := (volume : Measure (SlotOut N S → ℝ³))) (abox S.card L) (slotOutside L (dlBox L d u) S)]
    exact integral_prod_symm G hIntG'
  rw [hcv, ← hsplit, setIntegral_congr_fun hUmeas hpt, hFub]

/-- **The potential word factorises at the fibre.**  The `N`-particle sliding-box potential word of
the slot piece of `S` is the integral, over the outside configurations `y` (`slotOutside`), of the
`|S|`-particle word of the fibre `slotFibreState S e (slotPiece …) y`. -/
theorem qLHSword_slotFibre {N : ℕ} (L d μ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (S : Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hsupp1 : ∀ x : EuclideanSpace ℝ (Fin 3), x ∉ Submission.BoseGases.dlBox L d u →
      ∀ y : EuclideanSpace ℝ (Fin 3), w1 x y = 0)
    (hsupp2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox L d u ∨ y ∉ Submission.BoseGases.dlBox L d u) → w x y = 0)
    (hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ x) ^ 2
        * (Submission.BoseGases.qLHSden N L μ w w1 x)) (Submission.BoseGases.abox N L)) :
    Submission.BoseGases.qLHSword (N := N) L μ w w1
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
      = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
          Submission.BoseGases.qLHSword (N := S.card) L μ w w1
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y) := by
  exact qLHSword_slotFibre_aux L d μ u S
    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) e w w1
    hsupp1 hsupp2
    (fun x hx => Set.indicator_of_notMem hx Φ)
    hint

end Work.SlotWord
