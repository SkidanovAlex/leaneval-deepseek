import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBox.q3kinDiagPeel
import Submission.Work.BoseFixR.BsOneBodyBoxBound
import Submission.Work.BoseFixR.FibKTBoxFacts
import Submission.Work.BoseFixR.GapWordFibreMeas
import Submission.Work.BoseFixR.NeuFracFibreMeas
import Submission.Work.BoseFixR.NeuGapMomBoxBound
import Submission.Work.BoseFixR.WindowedFTMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.KinGePDiag` — the diagonal `p`-space mode form is dominated by `kinFormB`

The target lemma of this file is

  `pDiagForm ℓ (fsKinCoeff ((2 d s ℓ)⁻¹)) Φ ≤ kinFormB n ℓ d s eT b Φ`

for every smooth `Φ` and `n ≥ 1`.  See the file `README`/`HANDOFF` for the surrounding
programme; this file contains the proof and the small amount of glue it needs.
-/

noncomputable section

namespace Work.BoseFixR

open MeasureTheory

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The unconditional slot peel

`Submission.Work.SmallBoxBridge.Fourier.peel_slot_abox` peels the `i`-th coordinate out of the
centred `(m+1)`-particle box, but carries a (never used) continuity hypothesis on the
integrand.  Here is the same statement without it. -/

theorem peel_slot_abox_indep {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 1))
    {H : Submission.BoseGases.X (m + 1) → ℝ}
    (hind : ∀ (r : Submission.BoseGases.X m) (y y' : EuclideanSpace ℝ (Fin 3)),
      H (Submission.BoseGases.kcInsN m i (y, r)) = H (Submission.BoseGases.kcInsN m i (y', r))) :
    (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x
      = ∫ r in Submission.BoseGases.abox m ℓ,
          H (Submission.BoseGases.kcInsN m i (0, r)) := by
  have hpre : (Submission.BoseGases.kcInsN m i) ⁻¹' (Submission.BoseGases.abox (m + 1) ℓ)
      = Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ := by
    ext p
    obtain ⟨y, r⟩ := p
    simp only [Set.mem_preimage, Set.mem_prod, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro hp
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using hp i,
        fun j => by simpa [Submission.BoseGases.kc_insN_apply_succ] using hp (i.succAbove j)⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · rcases Fin.exists_succAbove_eq hj with ⟨j', hj'⟩
        rw [← hj']
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 j'
  have hvol : (MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ)
      = (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (Submission.BoseGases.kcE3) (Submission.BoseGases.X m),
      ← MeasureTheory.Measure.prod_restrict]
  have h1 := (Submission.BoseGases.kc_mp_insN m i).restrict_preimage_emb
      (Submission.BoseGases.kcInsN m i).measurableEmbedding (Submission.BoseGases.abox (m + 1) ℓ)
  have h2 : MeasureTheory.MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i).symm)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ))
      ((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    rw [hpre, hvol] at h1
    exact MeasureTheory.MeasurePreserving.symm (Submission.BoseGases.kcInsN m i) h1
  have hchange : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x)
      = ∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X m,
          H (Submission.BoseGases.kcInsN m i p)
        ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    have hc := h2.integral_comp (Submission.BoseGases.kcInsN m i).symm.measurableEmbedding
      (fun p : Submission.BoseGases.kcE3 × Submission.BoseGases.X m =>
        H (Submission.BoseGases.kcInsN m i p))
    simpa using hc
  have hrew : (∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X m,
        H (Submission.BoseGases.kcInsN m i p)
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))))
      = ∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X m,
          H (Submission.BoseGases.kcInsN m i (0, p.2))
        ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => hind p.2 p.1 0)
  have hprod : (∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X m,
          H (Submission.BoseGases.kcInsN m i (0, p.2))
        ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))))
      = (∫ y : Submission.BoseGases.kcE3, (1 : ℝ)
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
        * (∫ r : Submission.BoseGases.X m, H (Submission.BoseGases.kcInsN m i (0, r))
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    have h := MeasureTheory.integral_prod_mul
      (μ := MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))
      (ν := MeasureTheory.volume.restrict (Submission.BoseGases.abox m ℓ))
      (f := fun _ : Submission.BoseGases.kcE3 => (1 : ℝ))
      (g := fun r : Submission.BoseGases.X m => H (Submission.BoseGases.kcInsN m i (0, r)))
    simpa using h
  have hint1 : (∫ y : Submission.BoseGases.kcE3, (1 : ℝ)
      ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))) = ℓ ^ 3 := by
    rw [MeasureTheory.integral_const, MeasureTheory.Measure.real,
      MeasureTheory.Measure.restrict_apply_univ,
      Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
    simp
  rw [hchange, hrew, hprod, hint1, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)),
    one_mul]

/-! ## 2. Continuity of the slot density -/

/-- The `p`-density of the slot-`i` diagonal mode content is continuous. -/
theorem continuous_pDens {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    Continuous (Work.BoseBox.pDens ℓ Φ i) := by
  have h := Work.SmallBoxBridge.Cauchy.continuous_integral_pSlotAmp_sq (N := m + 1) (s := ℓ)
    hℓ hΦ i
  have hEq : Work.BoseBox.pDens ℓ Φ i
      = fun p : EuclideanSpace ℝ (Fin 3) =>
          (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            ‖Submission.BoseGases.pSlotAmp ℓ p Φ i x‖ ^ 2 := rfl
  rw [hEq]
  exact continuous_const.mul h

/-! ## 3. `mainWord ≤ fsT` for a continuous one-body state -/

/-- The main (two-cutoff) word is dominated by the full localised kinetic word `fsT`, because
the remaining three pieces are nonnegative. -/
theorem mainWord_le_fsT {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (hb : 0 ≤ b) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) := hψ.sub continuous_const
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Work.BoseKinLoc.lamBox ℓ 0)) := by
    have hsub := Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ (0 : EuclideanSpace ℝ (Fin 3))
    simp only [smul_zero] at hsub
    exact (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3))
      (2 * (|ℓ| + 1))) (hcont.pow 2).continuousOn).mono_set hsub
  have hneu : 0 ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
    have hn := Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 (0 : EuclideanSpace ℝ (Fin 3)) hI
    unfold Work.BoseKinLoc.neuWord
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) heT0) ha2) hn
  have hgap : 0 ≤ Work.BoseKinLoc.gapWord ℓ b 0 ψ :=
    Work.BoseKinLoc.gapWord_nonneg hb hℓ.le 0 ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d eT b 0 ψ :=
    Work.BoseKinLoc.momWord_nonneg hb heT0 hdℓ.le 0 ψ
  rw [Work.BoseKinLoc.fsT_eq_sum]
  linarith

/-! ## 4. Measure-theoretic helpers -/

/-- The `toReal` of a `lintegral` is dominated by the Bochner integral of its `toReal`
(junk-robust: if the `lintegral` is `⊤` the left side is `0`). -/
theorem toReal_lintegral_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {B : α → ENNReal} (hB : AEMeasurable B μ) :
    (∫⁻ a, B a ∂μ).toReal ≤ ∫ a, (B a).toReal ∂μ := by
  by_cases htop : (∫⁻ a, B a ∂μ) = ⊤
  · rw [htop, ENNReal.toReal_top]
    exact MeasureTheory.integral_nonneg (fun a => ENNReal.toReal_nonneg)
  · have hfin : (∫⁻ a, B a ∂μ) < ⊤ := lt_top_iff_ne_top.mpr htop
    have hmeas : AEMeasurable (fun a => (B a).toReal) μ :=
      ENNReal.measurable_toReal.comp_aemeasurable hB
    have hnonneg : 0 ≤ᵐ[μ] fun a => (B a).toReal :=
      Filter.Eventually.of_forall (fun a => ENNReal.toReal_nonneg)
    have hid : ∫ a, (B a).toReal ∂μ
        = (∫⁻ a, ENNReal.ofReal ((B a).toReal) ∂μ).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable
    rw [hid]
    have haeeq : ∫⁻ a, ENNReal.ofReal ((B a).toReal) ∂μ = ∫⁻ a, B a ∂μ := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_lt_top' hB htop] with a ha
      exact ENNReal.ofReal_toReal ha.ne
    rw [haeeq]

/-- `fsKinCoeff 0 r = r²` for `r ≥ 0`. -/
lemma fsKinCoeff_zero_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff 0 r = r ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff, sub_zero, max_eq_left hr]

/-- The square of the momentum times the slot density is integrable.  This is the existing
`Work.SmallBoxBridge.Cauchy.integrable_cModeForm` at the cutoff `0`, restricted to one slot. -/
theorem integrable_normSq_mul_pDens {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (m + 1)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * Work.BoseBox.pDens ℓ Φ i p) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hK := Work.SmallBoxBridge.Cauchy.integrable_cModeForm (n := m) (s := ℓ)
    (c := 0) hℓ le_rfl (Φ := Φ) hΦ
  have hEq : (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff 0 ‖p‖ *
        (∑ i : Fin (m + 1), (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          ‖Submission.BoseGases.pSlotAmp ℓ p Φ i x‖ ^ 2))
      = fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
        ∑ i : Fin (m + 1), Work.BoseBox.pDens ℓ Φ i p := by
    funext p
    rw [fsKinCoeff_zero_of_nonneg (norm_nonneg p)]
    simp only [Work.BoseBox.pDens]
  rw [hEq] at hK
  refine hK.mono' ?_ ?_
  · exact ((continuous_norm.pow 2).mul (continuous_pDens hℓ hΦc i)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    have hnn : ∀ j : Fin (m + 1), 0 ≤ Work.BoseBox.pDens ℓ Φ j p := fun j =>
      mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))
    have hle : Work.BoseBox.pDens ℓ Φ i p
        ≤ ∑ j : Fin (m + 1), Work.BoseBox.pDens ℓ Φ j p :=
      Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hnn i))]
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- The slot density has finite `lintegral`. -/
theorem lintegral_pDens_lt_top {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (m + 1)) :
    ∫⁻ p : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseBox.pDens ℓ Φ i p) < ⊤ := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hs : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ < 1} :=
    measurableSet_lt continuous_norm.measurable
      (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)).measurable
  have hpdcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∑ j : Fin (m + 1), Work.BoseBox.pDens ℓ Φ j p) :=
    continuous_finsetSum _ (fun j _ => continuous_pDens hℓ hΦc j)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3))
    1).exists_bound_of_continuousOn hpdcont.continuousOn
  have hKmem : ∀ p : EuclideanSpace ℝ (Fin 3), ‖p‖ < 1 →
      ∑ j : Fin (m + 1), Work.BoseBox.pDens ℓ Φ j p ≤ K := by
    intro p hp
    have h1 := hK p (by simpa [Metric.mem_closedBall, dist_eq_norm] using hp.le)
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_abs_self _) h1
  have hint := integrable_normSq_mul_pDens hℓ hΦ i
  have hnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseBox.pDens ℓ Φ i p := fun p =>
    mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))
  have hbound : ∀ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Work.BoseBox.pDens ℓ Φ i p)
      ≤ ENNReal.ofReal K *
            ({p : EuclideanSpace ℝ (Fin 3) | ‖p‖ < 1}.indicator
              (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) p)
          + ENNReal.ofReal (‖p‖ ^ 2 * Work.BoseBox.pDens ℓ Φ i p) := by
    intro p
    by_cases hp : ‖p‖ < 1
    · rw [Set.indicator_of_mem (by simpa using hp), Pi.one_apply, mul_one]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
      exact le_trans (Finset.single_le_sum (s := Finset.univ) (f := fun j =>
        Work.BoseBox.pDens ℓ Φ j p) (fun j _ =>
        mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _)))
        (Finset.mem_univ i)) (hKmem p hp)
    · rw [Set.indicator_of_notMem (by simpa using hp), mul_zero, zero_add]
      refine ENNReal.ofReal_le_ofReal ?_
      have hnorm : (1 : ℝ) ≤ ‖p‖ := not_lt.mp hp
      have h1 : (1 : ℝ) ≤ ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
      nlinarith [hnn p]
  have hconst : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal K *
        ({p : EuclideanSpace ℝ (Fin 3) | ‖p‖ < 1}.indicator
          (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) p)) volume :=
    aemeasurable_const.mul (Measurable.indicator measurable_const hs).aemeasurable
  calc ∫⁻ p, ENNReal.ofReal (Work.BoseBox.pDens ℓ Φ i p) ∂volume
      ≤ ∫⁻ p, (ENNReal.ofReal K *
              ({p : EuclideanSpace ℝ (Fin 3) | ‖p‖ < 1}.indicator
                (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) p)
            + ENNReal.ofReal (‖p‖ ^ 2 * Work.BoseBox.pDens ℓ Φ i p)) ∂volume :=
        MeasureTheory.lintegral_mono hbound
    _ = ENNReal.ofReal K *
            (∫⁻ p, {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ < 1}.indicator
              (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) p ∂volume)
          + ∫⁻ p, ENNReal.ofReal (‖p‖ ^ 2 * Work.BoseBox.pDens ℓ Φ i p) ∂volume := by
        rw [MeasureTheory.lintegral_add_left' hconst,
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal K * volume {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ < 1}
          + ENNReal.ofReal (∫ p, ‖p‖ ^ 2 * Work.BoseBox.pDens ℓ Φ i p) := by
        rw [MeasureTheory.lintegral_indicator_one hs,
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall (fun p => mul_nonneg (sq_nonneg _) (hnn p)))]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (MeasureTheory.measure_mono (fun p hp => by
            have hp' : ‖p‖ < 1 := hp
            rw [Metric.mem_closedBall, dist_eq_norm]
            simpa using hp'.le))
          ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).measure_lt_top)),
        ENNReal.ofReal_lt_top⟩


/-- **The per-symbol comparison.**  For a nonnegative cutoff `c`, the `p`-integral of
`fsKinCoeff c` against the slot density `pDens` is dominated by the `bsOneBody` form of the
slot fibre, integrated over the centred box. -/
theorem pDens_integral_le_bsOneBody {m : ℕ} {ℓ c K : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    (hK : ∀ r ∈ Submission.BoseGases.abox m ℓ,
        ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseBox.fibKT ℓ Φ i r p ≤ K)
    (hcont : Continuous (Function.uncurry (Work.BoseBox.fibKT ℓ Φ i))) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff c ‖p‖ * Work.BoseBox.pDens ℓ Φ i p
      ≤ ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
            (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
  have hboxm : MeasurableSet (Submission.BoseGases.abox m ℓ) :=
    Submission.BoseGases.abox_measurable m ℓ
  have hFnn : ∀ r : ℝ, 0 ≤ Submission.BoseGases.fsKinCoeff c r :=
    Submission.BoseGases.fsKinCoeff_nonneg c
  have hFmeas : Measurable (Submission.BoseGases.fsKinCoeff c) := by
    unfold Submission.BoseGases.fsKinCoeff
    fun_prop
  have hnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseBox.pDens ℓ Φ i p := fun p =>
    mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))
  have hUnn : ∀ (r : Submission.BoseGases.X m) (p : EuclideanSpace ℝ (Fin 3)),
      0 ≤ Work.BoseBox.rKern ℓ Φ i r p := by
    intro r p
    simp only [Work.BoseBox.rKern]
    exact mul_nonneg (Work.BoseBox.fibKT_nonneg ℓ Φ i r p)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) r)
  have hUmeas : Measurable (Function.uncurry (Work.BoseBox.rKern ℓ Φ i)) := by
    have h1 : Function.uncurry (Work.BoseBox.rKern ℓ Φ i)
        = fun q : Submission.BoseGases.X m × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseBox.fibKT ℓ Φ i q.1 q.2 *
              (Submission.BoseGases.abox m ℓ).indicator (fun _ => (1 : ℝ)) q.1 := rfl
    rw [h1]
    exact hcont.measurable.mul ((Measurable.indicator measurable_const hboxm).comp measurable_fst)
  have hAeq : ∀ p : EuclideanSpace ℝ (Fin 3),
      Work.BoseBox.pDens ℓ Φ i p = ∫ r, Work.BoseBox.rKern ℓ Φ i r p := by
    intro p
    have h1 : Work.BoseBox.pDens ℓ Φ i p
        = ∫ r in Submission.BoseGases.abox m ℓ, Work.BoseBox.fibKT ℓ Φ i r p := by
      rw [Work.BoseBox.pDens]
      exact Work.BoseBox.q3kinDiagPeel (m := m) (ℓ := ℓ) hℓ hΦ i p
    rw [h1, ← MeasureTheory.integral_indicator hboxm
      (f := fun r : Submission.BoseGases.X m => Work.BoseBox.fibKT ℓ Φ i r p)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
    by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
    · simp only [Work.BoseBox.rKern, Set.indicator_of_mem hr, mul_one]
    · simp only [Work.BoseBox.rKern, Set.indicator_of_notMem hr, mul_zero]
  have hfin : ∀ p : EuclideanSpace ℝ (Fin 3),
      ∫⁻ r : Submission.BoseGases.X m, ENNReal.ofReal (Work.BoseBox.rKern ℓ Φ i r p) < ⊤ := by
    intro p
    have h1 : (fun r : Submission.BoseGases.X m =>
          ENNReal.ofReal (Work.BoseBox.rKern ℓ Φ i r p))
        = fun r => (Submission.BoseGases.abox m ℓ).indicator
            (fun r => ENNReal.ofReal (Work.BoseBox.fibKT ℓ Φ i r p)) r := by
      funext r
      by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
      · simp only [Work.BoseBox.rKern, Set.indicator_of_mem hr, mul_one]
      · simp only [Work.BoseBox.rKern, Set.indicator_of_notMem hr, mul_zero,
          ENNReal.ofReal_zero]
    rw [h1]
    have hbound : ∀ r : Submission.BoseGases.X m,
        (Submission.BoseGases.abox m ℓ).indicator
            (fun r => ENNReal.ofReal (Work.BoseBox.fibKT ℓ Φ i r p)) r
          ≤ (Submission.BoseGases.abox m ℓ).indicator
              (fun _ : Submission.BoseGases.X m => ENNReal.ofReal K) r := by
      intro r
      by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
        exact ENNReal.ofReal_le_ofReal (hK r hr p)
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hbound) ?_
    rw [MeasureTheory.lintegral_indicator_const hboxm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Submission.BoseGases.abox_lt_top m ℓ hℓ.le)
  have hstep := Work.BoseBox.lintegral_step (m := m)
    (F := Submission.BoseGases.fsKinCoeff c) hFnn hFmeas
    (A := Work.BoseBox.pDens ℓ Φ i) hnn
    (U := Work.BoseBox.rKern ℓ Φ i) hUnn hUmeas hAeq hfin
  have hident : ∫ p, Submission.BoseGases.fsKinCoeff c ‖p‖ * Work.BoseBox.pDens ℓ Φ i p
      = (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          Work.BoseBox.pDens ℓ Φ i p)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun p => mul_nonneg (hFnn ‖p‖) (hnn p)))
      (((Work.BoseBox.continuous_fsKinCoeff_norm c).mul
        (continuous_pDens hℓ hΦ i)).aestronglyMeasurable)
  have hBmeas : AEMeasurable (fun r : Submission.BoseGases.X m =>
      ∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseBox.rKern ℓ Φ i r p)) MeasureTheory.volume := by
    have hfun : Measurable (Function.uncurry (fun (r : Submission.BoseGases.X m)
        (p : EuclideanSpace ℝ (Fin 3)) =>
          ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            Work.BoseBox.rKern ℓ Φ i r p))) := by
      have h1 : Function.uncurry (fun (r : Submission.BoseGases.X m)
          (p : EuclideanSpace ℝ (Fin 3)) =>
            ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
              Work.BoseBox.rKern ℓ Φ i r p))
          = fun q : Submission.BoseGases.X m × EuclideanSpace ℝ (Fin 3) =>
              ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖q.2‖ *
                Work.BoseBox.rKern ℓ Φ i q.1 q.2) := rfl
      rw [h1]
      exact ENNReal.measurable_ofReal.comp
        (((hFmeas.comp continuous_norm.measurable).comp measurable_snd).mul hUmeas)
    exact (Measurable.lintegral_prod_right (ν := (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) hfun).aemeasurable
  rw [hident, hstep]
  by_cases htop : (∫⁻ r : Submission.BoseGases.X m, ∫⁻ p : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseBox.rKern ℓ Φ i r p)) = ⊤
  · rw [htop, ENNReal.toReal_top, mul_zero]
    exact integral_nonneg (fun r =>
      Work.BSKinetic.bsOneBody_nonneg (u := 0) (fun t => hFnn t) _)
  · have hle := toReal_lintegral_le hBmeas
    have hval : ∀ r : Submission.BoseGases.X m,
        (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          Work.BoseBox.rKern ℓ Φ i r p)).toReal
        = (Submission.BoseGases.abox m ℓ).indicator (fun _ : Submission.BoseGases.X m => (1 : ℝ)) r *
          ((2 * Real.pi) ^ 3 * Work.BSKinetic.bsOneBody ℓ
            (Submission.BoseGases.fsKinCoeff c) 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
      intro r
      by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
      · rw [Set.indicator_of_mem hr, one_mul]
        have hBr : (∫⁻ p : EuclideanSpace ℝ (Fin 3),
              ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
                Work.BoseBox.rKern ℓ Φ i r p))
            = ∫⁻ p : EuclideanSpace ℝ (Fin 3),
                ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
                  Work.BoseBox.fibKT ℓ Φ i r p) := by
          refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          simp only [Work.BoseBox.rKern, Set.indicator_of_mem hr, mul_one]
        rw [hBr, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall (fun p => mul_nonneg (hFnn ‖p‖)
            (Work.BoseBox.fibKT_nonneg ℓ Φ i r p)))
          (((Work.BoseBox.continuous_fsKinCoeff_norm c).mul
            (hcont.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable)]
        have h2 : Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
            = fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.fibKT ℓ Φ i r p := rfl
        rw [Work.BoseBox.bsOneBody_eq_integral_bOKT, h2]
        field_simp
      · rw [Set.indicator_of_notMem
            (f := fun _ : Submission.BoseGases.X m => (1 : ℝ)) hr, zero_mul]
        have hBr : (∫⁻ p : EuclideanSpace ℝ (Fin 3),
              ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
                Work.BoseBox.rKern ℓ Φ i r p)) = 0 := by
          have hzero : (fun p : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal
              (Submission.BoseGases.fsKinCoeff c ‖p‖ * Work.BoseBox.rKern ℓ Φ i r p))
              = fun _ => (0 : ENNReal) := by
            funext p
            simp only [Work.BoseBox.rKern, Set.indicator_of_notMem hr, mul_zero,
              ENNReal.ofReal_zero]
          rw [hzero, MeasureTheory.lintegral_zero]
        rw [hBr, ENNReal.toReal_zero]
    have hbridge : ∫ r : Submission.BoseGases.X m,
          (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            Work.BoseBox.rKern ℓ Φ i r p)).toReal
        = ∫ r : Submission.BoseGases.X m,
            ((Submission.BoseGases.abox m ℓ).indicator (fun _ : Submission.BoseGases.X m => (1 : ℝ)) r *
              ((2 * Real.pi) ^ 3 * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff c) 0
                  (Work.BoseKinLoc.Kinetic.genFibre i Φ r))) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hval)
    have hlast : ((2 * Real.pi) ^ 3)⁻¹ * ∫ r : Submission.BoseGases.X m,
            ((Submission.BoseGases.abox m ℓ).indicator (fun _ : Submission.BoseGases.X m => (1 : ℝ)) r *
              ((2 * Real.pi) ^ 3 * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff c) 0
                  (Work.BoseKinLoc.Kinetic.genFibre i Φ r)))
        = ∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
      have hpoint : ∀ r : Submission.BoseGases.X m,
          ((2 * Real.pi) ^ 3)⁻¹ *
            ((Submission.BoseGases.abox m ℓ).indicator (fun _ : Submission.BoseGases.X m => (1 : ℝ)) r *
              ((2 * Real.pi) ^ 3 * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff c) 0
                  (Work.BoseKinLoc.Kinetic.genFibre i Φ r)))
          = (Submission.BoseGases.abox m ℓ).indicator
              (fun r => Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
                (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) r := by
        intro r
        by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
        · simp only [Set.indicator_of_mem hr, one_mul]
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (by positivity : (2 * Real.pi) ≠ 0)),
            one_mul]
        · simp only [Set.indicator_of_notMem hr, zero_mul, mul_zero]
      rw [← MeasureTheory.integral_const_mul ((2 * Real.pi) ^ 3)⁻¹,
        ← MeasureTheory.integral_indicator hboxm
          (f := fun r : Submission.BoseGases.X m => Work.BSKinetic.bsOneBody ℓ
            (Submission.BoseGases.fsKinCoeff c) 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
      exact hpoint r
    calc ((2 * Real.pi) ^ 3)⁻¹ * (∫⁻ r : Submission.BoseGases.X m,
            ∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
              Work.BoseBox.rKern ℓ Φ i r p)).toReal
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ r : Submission.BoseGases.X m,
            (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
              Work.BoseBox.rKern ℓ Φ i r p)).toReal :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ r : Submission.BoseGases.X m,
            ((Submission.BoseGases.abox m ℓ).indicator (fun _ : Submission.BoseGases.X m => (1 : ℝ)) r *
              ((2 * Real.pi) ^ 3 * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff c) 0
                  (Work.BoseKinLoc.Kinetic.genFibre i Φ r))) := by rw [hbridge]
      _ = ∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := hlast


end Work.BoseFixR

namespace Work.BoseFixR

/-- `bOKT` expanded in the windowed-exponential form used by `Work.BoseBox.WindowedFTMeas`. -/
lemma bOKT_expand {m : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X (m + 1) → ℝ} (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p
      = ‖∫ z : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ((Submission.BoseGases.chiScale ℓ z : ℂ) *
              ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) z : ℝ)
                : ℂ))‖ ^ 2 := by
  simp only [Work.BoseBox.bOKT, Submission.BoseGases.kinFT, Work.BSKinetic.bsWin,
    Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, smul_zero, sub_zero]

/-- Joint measurability of the box indicator. -/
lemma measurable_indU (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Measurable (Work.BoseKinLoc.indU ℓ u) := by
  have h1 : Work.BoseKinLoc.indU ℓ u
      = (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) := rfl
  rw [h1]
  exact measurable_const.indicator (Work.BoseKinLoc.Kinetic.lamBox_measurable ℓ u)

/-- Measurability of the momentum cutoff indicator. -/
lemma measurable_momProj (ℓ d : ℝ) : Measurable (Work.BoseKinLoc.momProj ℓ d) := by
  have h1 : Work.BoseKinLoc.momProj ℓ d
      = {p : EuclideanSpace ℝ (Fin 3) | (d ^ 2 * ℓ)⁻¹ < ‖p‖}.indicator (fun _ => (1 : ℝ)) := by
    funext p
    rw [Work.BoseKinLoc.momProj]
    by_cases h : (d ^ 2 * ℓ)⁻¹ < ‖p‖
    · rw [if_pos h, Set.indicator_of_mem (by simpa using h)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]
  rw [h1]
  exact measurable_const.indicator (measurableSet_lt measurable_const continuous_norm.measurable)

/-- The windowed-`bsOneBody` word along the fibre is a.e. strongly measurable. -/
theorem aemeasurable_bsOneBody_genFibre {m : ℕ} {ℓ : ℝ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (i : Fin (m + 1))
    (hwin : ∀ (w : EuclideanSpace ℝ (Fin 3) → ℂ) (S : EuclideanSpace ℝ (Fin 3) → ℝ),
      Measurable w → Measurable S →
      Measurable (fun r : Submission.BoseGases.X m =>
        ∫ p : EuclideanSpace ℝ (Fin 3), S p *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (w z * ((Work.BoseKinLoc.Qfree ℓ 0
                (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2))
    (c : ℝ) :
    AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) := by
  have h0 : Measurable (fun r : Submission.BoseGases.X m =>
      ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖∫ z : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ((Submission.BoseGases.chiScale ℓ z : ℂ) *
              ((Work.BoseKinLoc.Qfree ℓ 0
                (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2) :=
    hwin (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ z : ℂ))
      (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖)
      ((Complex.continuous_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ)).measurable)
      (Work.BoseBox.continuous_fsKinCoeff_norm c).measurable
  have hid : ∀ r : Submission.BoseGases.X m,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff c ‖p‖ *
              Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p :=
    fun r => Work.BoseBox.bsOneBody_eq_integral_bOKT ℓ (Submission.BoseGases.fsKinCoeff c) _
  have hid2 : ∀ r : Submission.BoseGases.X m,
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff c ‖p‖ *
              Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ‖∫ z : EuclideanSpace ℝ (Fin 3),
                Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
                  ((Submission.BoseGases.chiScale ℓ z : ℂ) *
                    ((Work.BoseKinLoc.Qfree ℓ 0
                      (fun z : EuclideanSpace ℝ (Fin 3) =>
                        Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2 := by
    intro r
    have hid3 : (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖ *
          Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p)
        = fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((Submission.BoseGases.chiScale ℓ z : ℂ) *
                ((Work.BoseKinLoc.Qfree ℓ 0
                  (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2 := by
      funext p
      rw [bOKT_expand (ℓ := ℓ) (Φ := Φ) i r p]
      rfl
    rw [hid3]
  rw [show (fun r : Submission.BoseGases.X m =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      = fun r => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ‖∫ z : EuclideanSpace ℝ (Fin 3),
                Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
                  ((Submission.BoseGases.chiScale ℓ z : ℂ) *
                    ((Work.BoseKinLoc.Qfree ℓ 0
                      (fun z : EuclideanSpace ℝ (Fin 3) =>
                        Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2
      from funext (fun r => (hid r).trans (hid2 r))]
  exact AEMeasurable.const_mul h0.aemeasurable _

/-- **Auxiliary: the `fsT`-word along the fibre is a.e. strongly measurable**, given the
component-wise measurability inputs (the gap word, the windowed Fourier words and the Neumann
fraction). -/
theorem aemeasurable_fsT_genFibre {m : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (hb : 0 ≤ b)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (m + 1))
    (hgap : AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)))
    (hwin : ∀ (w : EuclideanSpace ℝ (Fin 3) → ℂ) (S : EuclideanSpace ℝ (Fin 3) → ℝ),
      Measurable w → Measurable S →
      Measurable (fun r : Submission.BoseGases.X m =>
        ∫ p : EuclideanSpace ℝ (Fin 3), S p *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (w z * ((Work.BoseKinLoc.Qfree ℓ 0
                (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2))
    (hneu : AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m))) :
    MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  have ha2 : 0 < (d * ℓ) ^ (-2 : ℤ) := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    exact inv_pos.mpr (by positivity)
  -- the two windowed Fourier words of `mainWord`
  have hwinWord : ∀ (c : ℝ), AEMeasurable (fun r : Submission.BoseGases.X m =>
      ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) := by
    intro c
    have h0 : Measurable (fun r : Submission.BoseGases.X m =>
        ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((Submission.BoseGases.chiScale ℓ z : ℂ) *
                ((Work.BoseKinLoc.Qfree ℓ 0
                  (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2) :=
      hwin (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ z : ℂ))
        (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖)
        ((Complex.continuous_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ)).measurable)
        (Work.BoseBox.continuous_fsKinCoeff_norm c).measurable
    have hid : ∀ r : Submission.BoseGases.X m,
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p)
        = ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((Submission.BoseGases.chiScale ℓ z : ℂ) *
                ((Work.BoseKinLoc.Qfree ℓ 0
                  (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2 := by
      intro r
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      show Submission.BoseGases.fsKinCoeff c ‖p‖ * Work.BoseBox.bOKT ℓ
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p
        = Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((Submission.BoseGases.chiScale ℓ z : ℂ) *
                ((Work.BoseKinLoc.Qfree ℓ 0
                  (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2
      rw [bOKT_expand (ℓ := ℓ) (Φ := Φ) i r p]
      rfl
    exact h0.aemeasurable.congr (Filter.Eventually.of_forall (fun r => (hid r).symm))
  have hmain : MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) := by
    have h1 : (fun r : Submission.BoseGases.X m =>
        Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        = fun r => (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
                Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p)
            + eT * (((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
                Work.BoseBox.bOKT ℓ (Work.BoseKinLoc.Kinetic.genFibre i Φ r) p) := by
      funext r
      rw [Work.BoseKinLoc.mainWord]
      simp only [Work.BoseBox.bsOneBody_eq_integral_bOKT]
    rw [h1]
    have h2 := AEMeasurable.const_mul
      (AEMeasurable.const_mul (hwinWord ((2 * (s * ℓ))⁻¹)) ((2 * Real.pi) ^ 3)⁻¹) (1 - eT)
    have h3 := AEMeasurable.const_mul
      (AEMeasurable.const_mul (hwinWord ((2 * (d * s * ℓ))⁻¹)) ((2 * Real.pi) ^ 3)⁻¹) eT
    exact AEMeasurable.aestronglyMeasurable (AEMeasurable.add h2 h3)
  -- `momWord`
  have hmom : MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.momWord ℓ d eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) := by
    have h0 : Measurable (fun r : Submission.BoseGases.X m =>
        ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
                ((Work.BoseKinLoc.Qfree ℓ 0
                  (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2) :=
      hwin (fun z : EuclideanSpace ℝ (Fin 3) => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ))
        (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momProj ℓ d p)
        (Complex.continuous_ofReal.measurable.comp (measurable_indU ℓ 0))
        (measurable_momProj ℓ d)
    have h1 : (fun r : Submission.BoseGases.X m =>
        Work.BoseKinLoc.momWord ℓ d eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        = fun r => b * eT * (d * ℓ) ^ (-2 : ℤ) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
              ‖∫ z : EuclideanSpace ℝ (Fin 3),
                Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
                  (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
                    ((Work.BoseKinLoc.Qfree ℓ 0
                      (Work.BoseKinLoc.Kinetic.genFibre i Φ r) z : ℝ) : ℂ))‖ ^ 2) := by
      funext r
      rw [Work.BoseKinLoc.momWord, Work.BoseKinLoc.momForm]
      simp only [Submission.BoseGases.kinFT]
    rw [h1]
    exact AEMeasurable.aestronglyMeasurable
      (AEMeasurable.const_mul
        (AEMeasurable.const_mul h0.aemeasurable ((2 * Real.pi) ^ 3)⁻¹)
        (b * eT * (d * ℓ) ^ (-2 : ℤ)))
  -- `neuWord`
  have hneu' : MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.neuWord ℓ d eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) := by
    have h1 : (fun r : Submission.BoseGases.X m =>
        Work.BoseKinLoc.neuWord ℓ d eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        = fun r => (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) *
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
      funext r
      have hmea : Measurable (Work.BoseKinLoc.Kinetic.genFibre i Φ r) :=
        ((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous).measurable
      have hint : MeasureTheory.IntegrableOn
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            (Work.BoseKinLoc.Kinetic.genFibre i Φ r z) ^ 2)
          (Work.BoseKinLoc.lamBox ℓ 0) := by
        have hsub := Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ
          (0 : EuclideanSpace ℝ (Fin 3))
        simp only [smul_zero] at hsub
        exact (ContinuousOn.integrableOn_compact (isCompact_closedBall
          (0 : EuclideanSpace ℝ (Fin 3)) (2 * (|ℓ| + 1)))
          (((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous).pow 2).continuousOn).mono_set hsub
      have hQ : Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          = fun z => Work.BoseKinLoc.Kinetic.genFibre i Φ r z
              + (-(Work.BoseKinLoc.meanU ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))) := by
        funext z
        simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BoseKinLoc.meanU,
          sub_eq_add_neg]
      rw [Work.BoseKinLoc.neuWord, hQ]
      rw [Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableOn_sq ha2
        (0 : EuclideanSpace ℝ (Fin 3)) (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        (-(Work.BoseKinLoc.meanU ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))) hmea hint]
    rw [h1]
    exact AEMeasurable.aestronglyMeasurable
      (AEMeasurable.const_mul hneu ((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ)))
  -- assemble
  have hfsT : (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      = fun r => Work.BoseKinLoc.neuWord ℓ d eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        + Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        + Work.BoseKinLoc.momWord ℓ d eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        + Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    funext r
    rw [Work.BoseKinLoc.fsT_eq_sum]
  rw [hfsT]
  exact ((hneu'.add (hgap.aestronglyMeasurable)).add hmom).add hmain

end Work.BoseFixR

namespace Work.BoseFixR

theorem KinGePDiag {n : ℕ} {ℓ d s eT b : ℝ} (hn : 1 ≤ n) (hℓ : 0 < ℓ) (hs : 0 < s) (hd0 : 0 < d)
    (hd1 : d ≤ 1) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Submission.BoseGases.pDiagForm ℓ (Submission.BoseGases.fsKinCoeff ((2 * d * s * ℓ)⁻¹)) Φ
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s eT b Φ := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hΦc : Continuous Φ := hΦ.continuous
  set cS : ℝ := (2 * (s * ℓ))⁻¹ with hcSdef
  set cB : ℝ := (2 * (d * s * ℓ))⁻¹ with hcBdef
  have hcSnn : 0 ≤ cS := by rw [hcSdef]; positivity
  have hcBnn : 0 ≤ cB := by rw [hcBdef]; positivity
  have hcSB : cS ≤ cB := by
    rw [hcSdef, hcBdef]
    refine inv_anti₀ (by positivity) ?_
    have h : d * s * ℓ ≤ s * ℓ := by
      have h1 : d * s * ℓ ≤ 1 * (s * ℓ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hd1 (le_of_lt (mul_pos hs hℓ))
      simpa using h1
    linarith
  rw [show (2 * d * s * ℓ)⁻¹ = cB from by rw [hcBdef]; ring_nf]
  rw [Submission.BoseGases.pDiagForm, Work.BoseKinLoc.kinFormB, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m + 1)))) => ?_)
  -- ## the analytic inputs (delegated)
  have hFib : ∃ K : ℝ, 0 ≤ K ∧ (∀ r ∈ Submission.BoseGases.abox m ℓ,
      ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseBox.fibKT ℓ Φ i r p ≤ K)
      ∧ Continuous (Function.uncurry (Work.BoseBox.fibKT ℓ Φ i)) := by
    obtain ⟨⟨Ki, hKi0, hKi⟩, _, hcont⟩ := FibKTBoxFacts (m := m) (ℓ := ℓ) hℓ hΦc i
    exact ⟨Ki, hKi0, hKi, hcont⟩
  have hBsS : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K :=
    BsOneBodyBoxBound (m := m) (ℓ := ℓ) (c := cS) hℓ hcSnn hΦ i
  have hBsB : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K :=
    BsOneBodyBoxBound (m := m) (ℓ := ℓ) (c := cB) hℓ hcBnn hΦ i
  have hNG : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BoseBox.neuGapMom ℓ d s eT b Φ i r ≤ K :=
    NeuGapMomBoxBound (m := m) (ℓ := ℓ) (d := d) (s := s) (eT := eT) (b := b)
      hℓ hd0 heT0 heT1 hb hΦc i
  have hgapMeas : AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) :=
    GapWordFibreMeas (m := m) (ℓ := ℓ) (b := b) hΦc i
  have hwin : ∀ (w : EuclideanSpace ℝ (Fin 3) → ℂ) (S : EuclideanSpace ℝ (Fin 3) → ℝ),
      Measurable w → Measurable S →
      Measurable (fun r : Submission.BoseGases.X m =>
        ∫ p : EuclideanSpace ℝ (Fin 3), S p *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (w z * ((Work.BoseKinLoc.Qfree ℓ 0
                (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2) :=
    fun w S hw hS => WindowedFTMeas (m := m) (ℓ := ℓ) hΦc i hw hS
  have hdℓ : 0 < d * ℓ := mul_pos hd0 hℓ
  have ha2 : 0 < (d * ℓ) ^ (-2 : ℤ) := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    exact inv_pos.mpr (by positivity)
  have hneuMeas : AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) :=
    NeuFracFibreMeas (m := m) (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ)) hℓ ha2 hΦ i
  obtain ⟨Ki, hKi0, hKi, hKicont⟩ := hFib
  obtain ⟨Ks, hKs0, hKs⟩ := hBsS
  obtain ⟨Kb, hKb0, hKb⟩ := hBsB
  obtain ⟨Kv, hKv0, hKv⟩ := hNG
  -- ## the `fsT` bound and the integrability of the two `bsOneBody` words
  have hmainEq : ∀ r : Submission.BoseGases.X m,
      Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        = (1 - eT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          + eT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    intro r
    rw [Work.BoseKinLoc.mainWord, ← hcSdef, ← hcBdef]
  have hfsTle : ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        ≤ Kv + ((1 - eT) * Ks + eT * Kb) := by
    intro r hr
    have h1 : Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        = Work.BoseBox.neuGapMom ℓ d s eT b Φ i r
          + Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
      rw [show Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          = Work.BoseBox.fsWord ℓ d s eT b Φ i r from rfl]
      rw [Work.BoseBox.fsWord_eq]
      rfl
    rw [h1, hmainEq r]
    have h2 := hKs r hr
    have h3 := hKb r hr
    have h4 := hKv r hr
    nlinarith [heT0, heT1, h2, h3, h4]
  have hfsTint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun _ : Submission.BoseGases.X m => Kv + ((1 - eT) * Ks + eT * Kb)) ?_ ?_ ?_
    · haveI : MeasureTheory.IsFiniteMeasure
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        MeasureTheory.isFiniteMeasure_restrict.mpr
          (Submission.BoseGases.abox_lt_top m ℓ hℓ.le).ne
      exact MeasureTheory.integrable_const _
    · exact (aemeasurable_fsT_genFibre hℓ hd0 heT0 hb hΦ i hgapMeas hwin hneuMeas).restrict
    · refine (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable m ℓ)).mpr ?_
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      rw [Real.norm_of_nonneg (Work.BoseKinLoc.Word.fsT_nonneg_of_continuous hℓ hd0 hs heT0 heT1 hb
        0 ((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous))]
      exact hfsTle r hr
  -- ## integrability of the two `bsOneBody` words on the box
  have hIntK : ∀ (c K' : ℝ), 0 ≤ K' → (∀ r ∈ Submission.BoseGases.abox m ℓ,
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K') →
      MeasureTheory.Integrable (fun r : Submission.BoseGases.X m =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ)) := by
    intro c K' hK'0 hK'
    refine MeasureTheory.Integrable.mono' (g := fun _ : Submission.BoseGases.X m => K') ?_ ?_ ?_
    · haveI : MeasureTheory.IsFiniteMeasure
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        MeasureTheory.isFiniteMeasure_restrict.mpr
          (Submission.BoseGases.abox_lt_top m ℓ hℓ.le).ne
      exact MeasureTheory.integrable_const _
    · exact (aemeasurable_bsOneBody_genFibre (m := m) (ℓ := ℓ) i hwin c).aestronglyMeasurable.restrict
    · refine (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable m ℓ)).mpr ?_
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      rw [Real.norm_of_nonneg (Work.BSKinetic.bsOneBody_nonneg (u := 0)
        (fun t => Submission.BoseGases.fsKinCoeff_nonneg c t) _)]
      exact hK' r hr
  have hIntS := hIntK cS Ks hKs0 hKs
  have hIntB := hIntK cB Kb hKb0 hKb
  -- ## the `p`-side comparison
  have hpdnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseBox.pDens ℓ Φ i p := fun p =>
    mul_nonneg (by positivity) (MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
  have hpdAEM : AEMeasurable (Work.BoseBox.pDens ℓ Φ i)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    (continuous_pDens hℓ hΦc i).aemeasurable
  have hpdlint : ∫⁻ p : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (Work.BoseBox.pDens ℓ Φ i p) < ⊤ := lintegral_pDens_lt_top hℓ hΦ i
  have hcore := Work.BoseBox.coreA (c₀ := cB) (c₁ := cS) (c₂ := cB) hcSB le_rfl heT0 heT1
    hpdnn hpdAEM hpdlint
  have hidentB : ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff cB ‖p‖ *
        Work.BoseBox.pDens ℓ Φ i p
      = (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff cB ‖p‖ *
          Work.BoseBox.pDens ℓ Φ i p)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg cB ‖p‖) (hpdnn p)))
      (((Work.BoseBox.continuous_fsKinCoeff_norm cB).mul
        (continuous_pDens hℓ hΦc i)).aestronglyMeasurable)
  have hstepA : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff cB ‖p‖ * Work.BoseBox.pDens ℓ Φ i p
      ≤ (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff cS ‖p‖ * Work.BoseBox.pDens ℓ Φ i p)
        + eT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff cB ‖p‖ * Work.BoseBox.pDens ℓ Φ i p) := by
    conv_lhs => rw [hidentB]
    exact hcore
  have hcmpS := pDens_integral_le_bsOneBody (m := m) (ℓ := ℓ) (c := cS) (K := Ki)
    hℓ hcSnn hΦc i hKi hKicont
  have hcmpB := pDens_integral_le_bsOneBody (m := m) (ℓ := ℓ) (c := cB) (K := Ki)
    hℓ hcBnn hΦc i hKi hKicont
  -- ## the `mainWord` integral and its domination
  have hlin : ∫ r in Submission.BoseGases.abox m ℓ,
        Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
      = (1 - eT) * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        + eT * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
    rw [show (fun r : Submission.BoseGases.X m =>
          Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        = fun r => (1 - eT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
            + eT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) from funext hmainEq]
    rw [MeasureTheory.integral_add (hIntS.const_mul _) (hIntB.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hdom : (1 - eT) * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        + eT * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      ≤ ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    rw [← hlin]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hfsTint ?_
    · refine Filter.Eventually.of_forall (fun r => ?_)
      show (0 : ℝ) ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
      rw [hmainEq r]
      exact add_nonneg (mul_nonneg (by linarith) (Work.BSKinetic.bsOneBody_nonneg (u := 0)
          (fun t => Submission.BoseGases.fsKinCoeff_nonneg cS t) _))
        (mul_nonneg heT0 (Work.BSKinetic.bsOneBody_nonneg (u := 0)
          (fun t => Submission.BoseGases.fsKinCoeff_nonneg cB t) _))
    · exact Filter.Eventually.of_forall (fun r => mainWord_le_fsT hℓ hd0 heT0 hb
        ((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous))
  -- ## the RHS in the `r`-form (dropping the box indicator and peeling a slot)
  have hRHS : (ℓ ^ (-3 : ℤ)) * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (m + 1) i Φ x)
      = ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    -- (i) the box indicator is `1` on the box
    have hind : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (m + 1) i Φ x)
          = Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x) := by
      intro x hx
      have hxi : x i ∈ Submission.BoseGases.acube ℓ := hx i
      have h1 : Work.BoseKinLoc.indU ℓ 0 (x i) = 1 :=
        Set.indicator_of_mem (by simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hxi) _
      rw [h1, one_mul]
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable (m + 1) ℓ) hind]
    -- (ii) the fibre `genFibre` is the inserted `fibre`
    have hfib : ∀ r : Submission.BoseGases.X m,
        Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          = Work.BoseKinLoc.fsT ℓ d s eT b 0
              (Work.BoseKinLoc.fibre (m + 1) i Φ (Submission.BoseGases.kcInsN m i (0, r))) := by
      intro r
      congr 1
      exact funext (fun z => Work.BoseKinLoc.Kinetic.genFibre_eq_fibre i Φ r 0 z)
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable m ℓ)
      (fun r _ => hfib r)]
    -- (iii) peel the slot
    rw [← peel_slot_abox_indep (m := m) (ℓ := ℓ) hℓ i
      (H := fun x => Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (m + 1) i Φ x))
      (fun r y y' => by
        congr 1
        funext z
        simp only [Work.BoseKinLoc.fibre, Submission.BoseGases.update_kcInsN])]
    rw [show ℓ ^ (-3 : ℤ) = (ℓ ^ 3)⁻¹ from by rw [zpow_neg, zpow_ofNat]]
  -- ## the final combination
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff cB ‖p‖ * Work.BoseBox.pDens ℓ Φ i p
      ≤ (1 - eT) * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        + eT * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) :=
        le_trans hstepA (add_le_add (mul_le_mul_of_nonneg_left hcmpS (by linarith))
          (mul_le_mul_of_nonneg_left hcmpB heT0))
    _ ≤ ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := hdom
    _ = (ℓ ^ (-3 : ℤ)) * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (m + 1) i Φ x) := hRHS.symm

end Work.BoseFixR
