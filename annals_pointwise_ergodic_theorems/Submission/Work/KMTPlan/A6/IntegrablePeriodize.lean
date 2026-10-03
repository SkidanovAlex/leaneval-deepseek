/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# Integrability of the periodisation of an integrable function

The periodisation `periodize φ ξ = ∑' k : ℤ, φ (x_ξ + k)` (where `x_ξ ∈ [0,1)` is the canonical
representative of `ξ ∈ ℝ/ℤ`) of an integrable function `φ : ℝ → ℂ` is integrable with respect to
Haar measure `circleMeasure` on the circle, with `∫ |periodize φ| ≤ ∫ |φ|`.

The proof is Fubini (Tonelli) over the disjoint unit intervals `Ioc n (n+1)`, `n : ℤ`, which cover
the line:

`∫⁻_circle ‖periodize φ‖ ≤ ∫⁻_{x ∈ Ioc 0 1} ∑'_k ‖φ (x+k)‖ = ∑'_k ∫⁻_{x ∈ Ioc 0 1} ‖φ (x+k)‖
   = ∑'_k ∫⁻_{y ∈ Ioc k (k+1)} ‖φ y‖ = ∫⁻_ℝ ‖φ‖`.

We implement this on the "interval side": `periodize φ = liftIco 1 0 G` with
`G x = ∑' k, φ (x + k)` by definition, and integrate `G` over `(0,1]` using the a.e. equality of
`Ioc 0 1` and `Ico 0 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal Topology

namespace Work.KMTPlan.A6

open MeasureTheory Filter

/-- The line is the disjoint union of the unit intervals `Ioc n (n+1)`, so the lower integral of a
nonnegative function over `ℝ` is the sum of its lower integrals over the unit intervals. -/
private lemma lintegral_eq_tsum_Ioc (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x = ∑' n : ℤ, ∫⁻ x in Set.Ioc (n:ℝ) (n+1), g x := by
  have key : ∫⁻ x in Set.univ, g x = ∑' n : ℤ, ∫⁻ x in Set.Ioc (n:ℝ) (n+1), g x := by
    rw [← iUnion_Ioc_intCast ℝ]
    rw [lintegral_iUnion (fun n => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_intCast ℝ)]
  rwa [Measure.restrict_univ] at key

/-- Translating the restriction of Lebesgue measure to `(0,1]` by `k` gives the restriction to
`(k, k+1]`. -/
private lemma map_addRight_restrict (k : ℤ) :
    (volume.restrict (Set.Ioc (0:ℝ) 1)).map (fun x : ℝ => x + (k:ℝ))
      = volume.restrict (Set.Ioc (k:ℝ) ((k:ℝ)+1)) := by
  have hf : MeasurableEmbedding (fun x : ℝ => x + (k:ℝ)) :=
    (MeasurableEquiv.addRight (k:ℝ)).measurableEmbedding
  have h := hf.restrict_map (volume : Measure ℝ) (Set.Ioc (k:ℝ) ((k:ℝ)+1))
  rw [(measurePreserving_add_right volume (k:ℝ)).map_eq] at h
  rw [show (fun x : ℝ => x + (k:ℝ)) ⁻¹' Set.Ioc (k:ℝ) ((k:ℝ)+1) = Set.Ioc (0:ℝ) 1 from by
    ext x; simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]] at h
  exact h.symm

/-- Change of variables for the translation by an integer, in lower integrals over unit intervals:
`∫_{Ioc k (k+1)} g = ∫_{Ioc 0 1} g (· + k)`. -/
private lemma lintegral_map_addRight (k : ℤ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(volume.restrict (Set.Ioc (k:ℝ) ((k:ℝ)+1)))
      = ∫⁻ x, g (x + (k:ℝ)) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  rw [← map_addRight_restrict k]
  exact lintegral_map_equiv g (MeasurableEquiv.addRight (k:ℝ))

/-- The periodised sum `G x = ∑' k, φ (x + k)` of an integrable `φ` is integrable on a fundamental
domain `(0,1]`.  This is Tonelli's theorem together with the fact that the translates
`Ioc k (k+1)`, `k : ℤ`, tile the line. -/
private lemma integrable_tsum_add {φ : ℝ → ℂ} (hφ : Integrable φ) :
    Integrable (fun x : ℝ => ∑' k : ℤ, φ (x + k)) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  have hae : ∀ k : ℤ, AEMeasurable (fun x : ℝ => φ (x + k))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro k
    refine AEMeasurable.restrict ?_
    simpa only [Function.comp_def] using
      hφ.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (k:ℝ)).quasiMeasurePreserving
  have hG : AEMeasurable (fun x : ℝ => ∑' k : ℤ, φ (x + k))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    AEMeasurable.tsum hae
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖∑' k : ℤ, φ (x + k)‖ₑ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) < ⊤
  calc ∫⁻ x, ‖∑' k : ℤ, φ (x + k)‖ₑ ∂(volume.restrict (Set.Ioc (0:ℝ) 1))
      ≤ ∫⁻ x, ∑' k : ℤ, ‖φ (x + k)‖ₑ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' k : ℤ, ∫⁻ x, ‖φ (x + k)‖ₑ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        lintegral_tsum fun k => (hae k).enorm
    _ = ∑' k : ℤ, ∫⁻ x, ‖φ x‖ₑ ∂(volume.restrict (Set.Ioc (k:ℝ) ((k:ℝ)+1))) :=
        tsum_congr fun k => (lintegral_map_addRight k (fun x => ‖φ x‖ₑ)).symm
    _ = ∫⁻ x, ‖φ x‖ₑ ∂volume := (lintegral_eq_tsum_Ioc (fun x => ‖φ x‖ₑ)).symm
    _ < ⊤ := hφ.hasFiniteIntegral

/-- Every singleton of the additive circle `ℝ/ℤ` is null, since `(0,1]` is a fundamental domain and
contains at most one representative of each class modulo `ℤ`. -/
private lemma volume_singleton_addCircle_one (x : AddCircle (1:ℝ)) :
    volume ({x} : Set (AddCircle (1:ℝ))) = 0 := by
  rw [AddCircle.add_projection_respects_measure (T := 1) (U := {x}) 0
    (measurableSet_singleton x)]
  rcases Set.eq_empty_or_nonempty
      (QuotientAddGroup.mk ⁻¹' ({x} : Set (AddCircle (1:ℝ))) ∩ Set.Ioc (0:ℝ) (0 + 1))
    with h | ⟨u, hu⟩
  · rw [h]; simp
  · refine measure_mono_null (fun z hz => ?_) (by simp : volume ({u} : Set ℝ) = 0)
    rw [Set.mem_singleton_iff]
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hu1, hu2⟩ := hu
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hz1 hu1
    have hzu : ((z : AddCircle (1:ℝ)) = (u : AddCircle (1:ℝ))) := by rw [hz1, hu1]
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1:ℝ)) (a := (0:ℝ)) hz2 hu2).mp hzu

/-- On `AddCircle 1` (the frequency circle `ℝ/ℤ`) the standard measure is Haar measure of total
mass `1`, which is `circleMeasure`. -/
private lemma volume_addCircle_one_eq_circleMeasure :
    (volume : Measure (AddCircle (1:ℝ))) = Work.Analysis.IonescuWainger.circleMeasure := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The lifts of a function from `[0,1)` and from `(0,1]` agree almost everywhere on the circle,
since the two fundamental domains differ by the single null point `0`. -/
private lemma liftIco_ae_eq_liftIoc (F : ℝ → ℂ) :
    AddCircle.liftIco (1:ℝ) 0 F =ᵐ[volume] AddCircle.liftIoc (1:ℝ) 0 F := by
  have h0 : ∀ᵐ z ∂(volume : Measure (AddCircle (1:ℝ))), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_singleton_addCircle_one 0
  filter_upwards [h0] with z hz
  exact (AddCircle.liftIoc_eq_liftIco_of_ne (a := (0:ℝ)) (f := F) (by simpa using hz)).symm

/-- A function which is in `L¹` on the fundamental domain `(0,1]` has an `L¹` lift to the circle,
namely the lift from `[0,1)` (the one used by `periodize`). -/
private lemma memLp_liftIco {G : ℝ → ℂ}
    (hG : MemLp G 1 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    MemLp (AddCircle.liftIco (1:ℝ) 0 G) 1 Work.Analysis.IonescuWainger.circleMeasure := by
  have hlift : MemLp (AddCircle.liftIoc (1:ℝ) 0 G) 1 (volume : Measure (AddCircle (1:ℝ))) :=
    MemLp.memLp_liftIoc (T := (1:ℝ)) (t := (0:ℝ)) (f := G) (p := 1)
      (show MemLp G 1 (volume.restrict (Set.Ioc (0:ℝ) (0 + 1))) from by simpa using hG)
  have hlift' : MemLp (AddCircle.liftIco (1:ℝ) 0 G) 1 (volume : Measure (AddCircle (1:ℝ))) :=
    MemLp.ae_eq (f := AddCircle.liftIoc (1:ℝ) 0 G) (g := AddCircle.liftIco (1:ℝ) 0 G)
      (liftIco_ae_eq_liftIoc G).symm hlift
  rwa [volume_addCircle_one_eq_circleMeasure] at hlift'

/-- The periodisation of an integrable function is integrable on the circle. -/
theorem IntegrablePeriodize {φ : ℝ → ℂ} (hφ : MeasureTheory.Integrable φ) :
    MeasureTheory.Integrable (Work.Analysis.IonescuWainger.periodize φ)
      Work.Analysis.IonescuWainger.circleMeasure :=
  show MeasureTheory.Integrable
      (AddCircle.liftIco (1:ℝ) 0 (fun x : ℝ => ∑' k : ℤ, φ (x + k)))
      Work.Analysis.IonescuWainger.circleMeasure from
    memLp_one_iff_integrable.mp
      (memLp_liftIco (memLp_one_iff_integrable.mpr (integrable_tsum_add hφ)))

end Work.KMTPlan.A6
