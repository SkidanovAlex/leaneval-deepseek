import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1B.MeanSqPiece.corrMeanSqRealFin3
import Submission.Work.BoseFixB1B.MeanSqPiece.meanSq1d_holds
import Submission.Work.BoseFixB1B.MeanSqPiece.meanSq3dCond
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace Work.BoseFixB1B.MeanSqPiece

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Coordinate lemmas (copied from `Submission/Work/BoseFixB1S/MeanSq/E3Box.lean`) -/

lemma toLp_mem_acube_iff {ℓ : ℝ} (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y ∈ Submission.BoseGases.acube ℓ ↔ y ∈ Work.BoseFixB1S.slBig ℓ := by
  rw [Submission.BoseGases.mem_acube_iff, Work.BoseFixB1S.mem_slBig]

lemma toLp_mem_dlBox_iff {ℓ d : ℝ} (y : Fin 3 → ℝ) (u : E3) :
    WithLp.toLp 2 y ∈ Submission.BoseGases.dlBox ℓ d u ↔
      y ∈ Work.BoseFixB1S.slBox ℓ (ℓ * d) u.ofLp := by
  rw [Submission.BoseGases.mem_dlBox_iff, Submission.BoseGases.mem_acube_iff,
    Work.BoseFixB1S.mem_slBox]
  constructor
  · rintro ⟨h1, h2⟩ j
    rw [Work.BoseFixB1S.slI_eq, Set.mem_inter_iff, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h1j := h1 j
      simp only [Set.mem_Icc, WithLp.ofLp_toLp] at h1j
      exact h1j
    · rw [Set.mem_Icc]
      have h2j := h2
      rw [Submission.BoseGases.mem_acube_iff] at h2j
      have h2jj := h2j j
      simp only [Set.mem_Icc] at h2jj
      have hcoord : (WithLp.toLp 2 y - (ℓ * d) • u).ofLp j = y j - ℓ * d * u.ofLp j := by
        rw [PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
      rw [hcoord] at h2jj
      exact ⟨by linarith [h2jj.1], by linarith [h2jj.2]⟩
  · intro h
    refine ⟨fun m => ?_, ?_⟩
    · have hm := h m
      rw [Work.BoseFixB1S.slI_eq, Set.mem_inter_iff, Set.mem_Icc] at hm
      simp only [Set.mem_Icc, WithLp.ofLp_toLp]
      exact hm.1
    · rw [Submission.BoseGases.mem_acube_iff]
      intro j
      have hj := h j
      rw [Work.BoseFixB1S.slI_eq, Set.mem_inter_iff, Set.mem_Icc] at hj
      simp only [Set.mem_Icc]
      have hcoord : (WithLp.toLp 2 y - (ℓ * d) • u).ofLp j = y j - ℓ * d * u.ofLp j := by
        rw [PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
      rw [hcoord]
      exact ⟨by linarith [hj.2.1], by linarith [hj.2.2]⟩

lemma volume_dlBox_eq (ℓ d : ℝ) (u : E3) :
    volume (Submission.BoseGases.dlBox ℓ d u)
      = volume (Work.BoseFixB1S.slBox ℓ (ℓ * d) u.ofLp) := by
  have hpre : WithLp.toLp 2 ⁻¹' (Submission.BoseGases.dlBox ℓ d u)
      = Work.BoseFixB1S.slBox ℓ (ℓ * d) u.ofLp := by
    ext y
    rw [Set.mem_preimage, toLp_mem_dlBox_iff]
  rw [← hpre, MeasureTheory.MeasurePreserving.measure_preimage
    (PiLp.volume_preserving_toLp (Fin 3))
    (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u).nullMeasurableSet]

/-! ## The transfer of the `Fin 3 → ℝ` statement to `EuclideanSpace ℝ (Fin 3)` -/

/-- **Transfer to `EuclideanSpace ℝ (Fin 3)`.**  Assume the real-valued `slBox` estimate on
`Fin 3 → ℝ` (with the matching constant); then the `dlBox`/`boxMass` statement on
`EuclideanSpace ℝ (Fin 3)` follows by transferring along the measure preserving coordinate
equivalence `WithLp.toLp 2`. -/
theorem corrMeanSqRealE3_holds_of_fin3 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {w : E3 → ℝ} (hw : Continuous w)
    (hR : ∀ {L H : ℝ}, 0 < H → H ≤ L → ∀ {W : (Fin 3 → ℝ) → ℝ}, Continuous W →
      MeasureTheory.Integrable (fun v : Fin 3 → ℝ =>
          ((1 / (volume : Measure (Fin 3 → ℝ)).real (Work.BoseFixB1S.slBox L H v)) *
            ∫ y in Work.BoseFixB1S.slBox L H v, W y) ^ 2)
        ∧ (∫ v : Fin 3 → ℝ,
            ((1 / (volume : Measure (Fin 3 → ℝ)).real (Work.BoseFixB1S.slBox L H v)) *
              ∫ y in Work.BoseFixB1S.slBox L H v, W y) ^ 2)
          ≤ (9 / H) ^ 3 * (∫ y in Work.BoseFixB1S.slBig L, (W y) ^ 2)) :
    MeasureTheory.Integrable (fun u : E3 =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
      ∧ (∫ u : E3,
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
        ≤ (9 / (ℓ * d)) ^ 3 *
          (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) := by
  have hH : 0 < ℓ * d := mul_pos hℓ hd
  have hHle : ℓ * d ≤ ℓ := by nlinarith [hℓ, hd1]
  set W : (Fin 3 → ℝ) → ℝ := fun y => w (WithLp.toLp 2 y) with hWdef
  have hW : Continuous W := hw.comp (by fun_prop)
  obtain ⟨hint, hbd⟩ := hR hH hHle hW
  set e : E3 ≃ᵐ (Fin 3 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm with he
  have heu : ∀ u : E3, e u = u.ofLp := fun u => rfl
  have hmp : MeasureTheory.MeasurePreserving (e : E3 → (Fin 3 → ℝ)) volume volume :=
    MeasureTheory.MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (PiLp.volume_preserving_toLp (Fin 3))
  have hemb : MeasurableEmbedding (e : E3 → (Fin 3 → ℝ)) := e.measurableEmbedding
  set g : (Fin 3 → ℝ) → ℝ := fun v =>
    ((1 / (volume : Measure (Fin 3 → ℝ)).real (Work.BoseFixB1S.slBox ℓ (ℓ * d) v)) *
      ∫ y in Work.BoseFixB1S.slBox ℓ (ℓ * d) v, W y) ^ 2 with hgdef
  -- the box mass is the small-box volume
  have hreal : ∀ u : E3, (volume : Measure E3).real (Submission.BoseGases.dlBox ℓ d u)
      = (volume : Measure (Fin 3 → ℝ)).real (Work.BoseFixB1S.slBox ℓ (ℓ * d) (e u)) := by
    intro u
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def,
      volume_dlBox_eq ℓ d u, heu u]
  have hbm : ∀ u : E3, Work.SmallBoxSliding.boxMass ℓ d u
      = (volume : Measure (Fin 3 → ℝ)).real (Work.BoseFixB1S.slBox ℓ (ℓ * d) (e u)) := by
    intro u
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, hreal u]
  -- the box mean is the small-box mean
  have hbi : ∀ u : E3, (∫ x in Submission.BoseGases.dlBox ℓ d u, w x)
      = ∫ y in Work.BoseFixB1S.slBox ℓ (ℓ * d) (e u), W y := by
    intro u
    have hpre : WithLp.toLp 2 ⁻¹' (Submission.BoseGases.dlBox ℓ d u)
        = Work.BoseFixB1S.slBox ℓ (ℓ * d) (e u) := by
      rw [heu u]
      ext y
      rw [Set.mem_preimage, toLp_mem_dlBox_iff]
    rw [← hpre]
    have hset := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
      (PiLp.volume_preserving_toLp (Fin 3))
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding w
      (Submission.BoseGases.dlBox ℓ d u)
    rw [hWdef]
    simpa using hset.symm
  -- the target integrand is `g ∘ e`
  have hpoint : (fun u : E3 =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
      = fun u : E3 => g (e u) := by
    funext u
    rw [hgdef, hbm u, hbi u]
  -- the large cube integral
  have hslBig : (∫ y in Work.BoseFixB1S.slBig ℓ, (W y) ^ 2)
      = ∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2 := by
    have hpre : WithLp.toLp 2 ⁻¹' (Submission.BoseGases.acube ℓ) = Work.BoseFixB1S.slBig ℓ := by
      ext y
      rw [Set.mem_preimage, toLp_mem_acube_iff]
    rw [← hpre]
    have hset := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
      (PiLp.volume_preserving_toLp (Fin 3))
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      (fun x : E3 => (w x) ^ 2) (Submission.BoseGases.acube ℓ)
    simpa [hWdef] using hset
  constructor
  · rw [hpoint]
    exact (hmp.integrable_comp_emb hemb).mpr hint
  · calc (∫ u : E3,
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
        = ∫ u : E3, g (e u) := by rw [hpoint]
      _ = ∫ v : Fin 3 → ℝ, g v :=
          MeasureTheory.MeasurePreserving.integral_comp hmp hemb g
      _ ≤ (9 / (ℓ * d)) ^ 3 * (∫ y in Work.BoseFixB1S.slBig ℓ, (W y) ^ 2) := hbd
      _ = (9 / (ℓ * d)) ^ 3 * (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2) := by
          rw [hslBig]

/-- **The real-valued sliding-box mean-square bound on `EuclideanSpace ℝ (Fin 3)`**
(FS's sliding-localisation mean-square estimate, in the form used by the B1B block).

The proof assembles

* `Work.BoseFixB1B.MeanSqPiece.meanSq1d_holds` — the one-dimensional bound with the sharp
  constant `9/h` (bulk `1/h` plus two Hardy-type boundary terms `4/h`),
* `Work.BoseFixB1B.MeanSqPiece.meanSq3dCond` — its threefold tensorisation to `Fin 3 → ℝ`
  (constant `(9/h)³`),
* `Work.BoseFixB1B.MeanSqPiece.corrMeanSqRealFin3` — the passage from the `ℝ≥0∞` box mean
  bound to the `ℝ`-valued statement in coordinates, and
* `corrMeanSqRealE3_holds_of_fin3` — the transfer of the coordinate statement to `dlBox`,
  `boxMass`, `acube` on `EuclideanSpace ℝ (Fin 3)` along the measure preserving equivalence
  `WithLp.toLp 2`. -/
theorem corrMeanSqRealE3_holds {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : Continuous w) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3),
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
        ≤ (9/(ℓ*d))^3 *
          (∫ x in Submission.BoseGases.acube ℓ, (w x)^2) := by
  -- the one-dimensional bound, in the shape expected by the tensorisation
  have h1d : ∀ {ℓ' h' : ℝ}, 0 < h' → h' ≤ ℓ' → ∀ {F : ℝ → ℝ≥0∞},
      AEMeasurable F (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ' h' u, F x)
          / (volume (Work.BoseFixB1S.slI ℓ' h' u))) ^ 2
        ≤ ENNReal.ofReal (9 / h') * ∫⁻ x in Set.Icc (-ℓ' / 2) (ℓ' / 2), (F x) ^ 2 := by
    intro ℓ' h' hh hhℓ F hF
    exact Work.BoseFixB1B.MeanSqPiece.meanSq1d_holds (ℓ := ℓ') (h := h') hh hhℓ hF
  -- the three-dimensional bound on `Fin 3 → ℝ`
  have H3 : ∀ {ℓ' h' : ℝ}, 0 < h' → h' ≤ ℓ' → ∀ {F : (Fin 3 → ℝ) → ℝ≥0∞}, Measurable F →
      ∫⁻ u : Fin 3 → ℝ,
          ((∫⁻ y in Work.BoseFixB1S.slBox ℓ' h' u, F y)
            / (volume (Work.BoseFixB1S.slBox ℓ' h' u))) ^ 2
        ≤ ENNReal.ofReal ((9 / h') ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ', (F y) ^ 2 := by
    intro ℓ' h' hh hhℓ F hF
    exact Work.BoseFixB1B.MeanSqPiece.meanSq3dCond h1d hh hhℓ hF
  -- the real-valued coordinate statement, then the transfer to `EuclideanSpace ℝ (Fin 3)`
  exact corrMeanSqRealE3_holds_of_fin3 hℓ hd hd1 hw
    (by
      intro L H hH hHL W hW
      exact Work.BoseFixB1B.MeanSqPiece.corrMeanSqRealFin3 (ℓ := L) (h := H) H3 hH hHL hW)

end Work.BoseFixB1B.MeanSqPiece
