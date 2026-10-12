import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.BandSdefs
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pointwise band lower bound for the localised potential word `qLHSwordB`

Main target (statement kept verbatim below): on the bad band `bandSet ℓ d μ` the localised
potential word `qLHSwordB h M ℓ d μ u Φ` is bounded below by the *chemical-potential* loss
`−(μ · bandK · bandS² · n) · ‖Φ‖²`, where `n` is the particle number.

Structure of the proof (all constants are `Work.BoseFixB1.bandK`/`bandS`):

* `wSmallPair_nonneg_qLHS` — the localised two-body kernel is `≥ 0` for `v ≥ 0`, so the pair
  half of the word is a non-negative contribution and may be dropped;
* `w1Fibre_abs_le_bandS_qLHS` — the **fibre bound**: on the band, every fibre
  `∫_y w_{1,B(u)}(z,y) dy` is dominated by the constant `bandK · bandS²`.  Proof: the corpus
  pointwise kernel domination `abs_wSmall1Pair_chiB_le` gives
  `|w_{1,B(u)}(z,y)| ≤ 2κ⁻¹ χ_{B(u)}(z) |g₀(z−y)| χ_{B(u)}(y)`; on the band `χ_{B(u)} ≤ bandS`
  pointwise (`chiSmallB_le_bandS`), and translation invariance of `∫|g₀|` turns the `y`-integral
  into `bandG`;
* `integrable_qLHS_integrand_qLHS` — the integrand of `qLHSwordB` is integrable over the box
  (`integrableOn_slot_wSmallPair` for the pair half, `integrableOn_slot_fibre` for the fibre
  half, the latter with the uniform bound of the fibre lemma);
* the assembly: the bracket is pointwise `≥ −μ·n·bandK·bandS²` (`Σ_i` fibre bound + pair `≥ 0`),
  and `integral_mono_ae` against the integrable function `Φ²·(−μ·n·bandK·bandS²)` gives the
  statement.

Notation: throughout, the localised one-body kernel is spelled
`wSmallPair M ℓ d u (g₀ v h)`, which is definitionally `wSmall1Pair h M ℓ d u` — this is the
spelling in which the corpus fibre bounds are stated.
-/

namespace Work.BoseFixB1

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. The localised pair kernel is nonnegative -/

lemma wSmallPair_nonneg_qLHS {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) (M : ℕ) (ℓ d : ℝ)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y := by
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled,
    Submission.BoseGases.convScaleSmall]
  refine mul_nonneg
    (mul_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x) ?_)
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u y)
  refine div_nonneg (div_nonneg (hv _) ?_) (Submission.BoseGases.convScale_nonneg ℓ _)
  rw [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun z =>
    mul_nonneg (Submission.BoseGases.chiSmall_nonneg M z)
      (Submission.BoseGases.chiSmall_nonneg M (_ - z))

/-! ## 1. The fibre bound on the band -/

lemma w1Fibre_abs_le_bandS_qLHS {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hreg : R ≤ ℓ * d / 16) (hregχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.bandSet ℓ d μ) :
    ∀ z : EuclideanSpace ℝ (Fin 3),
      |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
        ≤ bandK v h M * bandS M ℓ d μ ^ 2 := by
  intro z
  have hc0 : 0 ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (Work.SmallBoxSliding.smallConvLower_nonneg M))
  have hS0 : 0 ≤ bandS M ℓ d μ := bandS_nonneg M ℓ d μ
  have hG0 : 0 ≤ bandG v h := bandG_nonneg
  have hA0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u z :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u z
  have hAz : Submission.BoseGases.chiSmallB M ℓ d u z ≤ bandS M ℓ d μ :=
    chiSmallB_le_bandS hM hℓ hd hμ hu z
  -- pointwise domination of the kernel
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| ≤
        (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * |Submission.BoseGases.g0 v h (z - y)| * bandS M ℓ d μ := by
    intro y
    have hD : |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| ≤
        (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * |Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M ℓ d u y := by
      simpa only [Submission.BoseGases.wSmall1Pair] using
        (Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le (v := v) hv_supp hR h hM hℓ hd hreg hregχ u z y)
    have hy : Submission.BoseGases.chiSmallB M ℓ d u y ≤ bandS M ℓ d μ :=
      chiSmallB_le_bandS hM hℓ hd hμ hu y
    exact le_trans hD (mul_le_mul_of_nonneg_left hy
      (mul_nonneg (mul_nonneg hc0 hA0) (abs_nonneg _)))
  -- the majorant is integrable
  have hgi : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      |Submission.BoseGases.g0 v h (z - y)|) :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).abs.comp_sub_left z
  have hmaj : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
        * |Submission.BoseGases.g0 v h (z - y)| * bandS M ℓ d μ) := by
    have h := hgi.const_mul ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)
      * Submission.BoseGases.chiSmallB M ℓ d u z * bandS M ℓ d μ)
    refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
    ring
  have hstep1 : |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| := by
    have hh := norm_integral_le_integral_norm
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
    simpa only [Real.norm_eq_abs] using hh
  have hstep2 : ∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
        ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * |Submission.BoseGases.g0 v h (z - y)| * bandS M ℓ d μ) :=
    integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) hmaj.integrableOn
      (ae_of_all _ (fun y => hpt y))
  have hstep3 : ∫ y in Submission.BoseGases.acube ℓ,
        ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * |Submission.BoseGases.g0 v h (z - y)| * bandS M ℓ d μ)
      = ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * bandS M ℓ d μ) * (∫ y in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.g0 v h (z - y)|) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  have hstep4 : ∫ y in Submission.BoseGases.acube ℓ, |Submission.BoseGases.g0 v h (z - y)|
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (z - y)| :=
    setIntegral_le_integral hgi (ae_of_all _ (fun y => abs_nonneg _))
  have hstep5 : (∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (z - y)|)
      = bandG v h := by
    rw [bandG]
    exact integral_sub_left_eq_self (fun w : EuclideanSpace ℝ (Fin 3) =>
      |Submission.BoseGases.g0 v h w|) volume z
  have hreg2 : ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
        * bandS M ℓ d μ) * bandG v h
      ≤ ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * bandS M ℓ d μ * bandS M ℓ d μ)
        * bandG v h := by
    have h1 : (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
        ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * bandS M ℓ d μ :=
      mul_le_mul_of_nonneg_left hAz hc0
    have h2 : (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * bandS M ℓ d μ
        ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * bandS M ℓ d μ * bandS M ℓ d μ :=
      mul_le_mul_of_nonneg_right h1 hS0
    exact mul_le_mul_of_nonneg_right h2 hG0
  calc |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| := hstep1
    _ ≤ ∫ y in Submission.BoseGases.acube ℓ,
          ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
            * |Submission.BoseGases.g0 v h (z - y)| * bandS M ℓ d μ) := hstep2
    _ = ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * bandS M ℓ d μ) * (∫ y in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.g0 v h (z - y)|) := hstep3
    _ ≤ ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * bandS M ℓ d μ) * (∫ y : EuclideanSpace ℝ (Fin 3),
            |Submission.BoseGases.g0 v h (z - y)|) :=
        mul_le_mul_of_nonneg_left hstep4 (mul_nonneg (mul_nonneg hc0 hA0) hS0)
    _ = ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M ℓ d u z
          * bandS M ℓ d μ) * bandG v h := by rw [hstep5]
    _ ≤ ((2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * bandS M ℓ d μ * bandS M ℓ d μ)
        * bandG v h := hreg2
    _ = bandK v h M * bandS M ℓ d μ ^ 2 := by
        rw [show bandK v h M = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * bandG v h from rfl]
        ring

/-! ## 2. Integrability of the `qLHSwordB` integrand -/

lemma integrable_qLHS_integrand_qLHS {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hreg : R ≤ ℓ * d / 16) (hregχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hcont : Continuous Φ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.bandSet ℓ d μ) :
    Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (- μ * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
  classical
  have hFbound := w1Fibre_abs_le_bandS_qLHS (v := v) (h := h) hR hv_supp hM hℓ hd hμ hreg hregχ hu
  have hFm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) :=
    Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d)
      (f := Submission.BoseGases.g0 v h) M u
      (Submission.BoseGases.g0_integrable hR hv_supp h).aestronglyMeasurable.aemeasurable
  have hS1c : Continuous (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (-μ)) :=
    (hcont.pow 2).mul continuous_const
  -- ### the chemical (fibre) half
  have hchem_i : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      ((Φ x) ^ 2 * (-μ)) * (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y))
      (Submission.BoseGases.abox n ℓ) volume := fun i =>
    Submission.BoseGases.integrableOn_slot_fibre (N := n) (ℓ := ℓ) hℓ i hFm
      (fun z _ => hFbound z) hS1c
  have hchem : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * (- μ * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    have hsum : Integrable (fun x : Submission.BoseGases.X n => ∑ i : Fin n,
        ((Φ x) ^ 2 * (-μ)) * (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y))
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
      simpa only [IntegrableOn] using (integrable_finsetSum (Finset.univ : Finset (Fin n))
        (f := fun (i : Fin n) (x : Submission.BoseGases.X n) =>
          ((Φ x) ^ 2 * (-μ)) * (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y))
        (fun i _ => hchem_i i))
    refine hsum.congr (ae_of_all _ (fun x => ?_))
    have hmul := Finset.mul_sum (Finset.univ : Finset (Fin n))
      (fun i : Fin n => ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
      ((Φ x) ^ 2 * (-μ))
    exact hmul.symm.trans (by ring)
  -- ### the pair half
  have hvsupp' : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport v := subset_closure (Function.mem_support.mpr hne)
    have hz' := hv_supp hmem
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz'
    exact absurd hz' (not_lt.mpr hz)
  have hvint : Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hS2c : Continuous (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (1 / 2 : ℝ)) :=
    (hcont.pow 2).mul continuous_const
  have hpair_p : ∀ p : Fin n × Fin n, p ∈ Submission.BoseGases.pairSet n →
      IntegrableOn (fun x : Submission.BoseGases.X n =>
        ((Φ x) ^ 2 * (1 / 2 : ℝ)) * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        (Submission.BoseGases.abox n ℓ) volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by
      simpa [Submission.BoseGases.pairSet] using hp
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n ℓ)
      (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (1 / 2 : ℝ)) hS2c.continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := n) (ℓ := ℓ) (d := d) (R := R) hℓ hd
      hvint hvsupp' hM hreg hregχ u hpne hS2c.aestronglyMeasurable hB0 (by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx))
  have hpair : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      ((1 / 2 : ℝ) * (∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    have hsum : Integrable (fun x : Submission.BoseGases.X n => ∑ p ∈ Submission.BoseGases.pairSet n,
        ((Φ x) ^ 2 * (1 / 2 : ℝ)) * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
      simpa only [IntegrableOn] using (integrable_finsetSum (Submission.BoseGases.pairSet n)
        (f := fun (p : Fin n × Fin n) (x : Submission.BoseGases.X n) =>
          ((Φ x) ^ 2 * (1 / 2 : ℝ)) * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        (fun p hp => hpair_p p hp))
    refine hsum.congr (ae_of_all _ (fun x => ?_))
    have hmul := Finset.mul_sum (Submission.BoseGases.pairSet n)
      (fun p : Fin n × Fin n => Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
      ((Φ x) ^ 2 * (1 / 2 : ℝ))
    exact hmul.symm.trans (by ring)
  -- ### combine
  have htot := hchem.add hpair
  refine htot.congr (ae_of_all _ (fun x => ?_))
  simp only [Pi.add_apply]
  ring

/-! ## 3. The target -/

theorem qLHSwordB_ge_neg_bandS {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hreg : R ≤ ℓ * d / 16) (hregχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (hcont : Continuous Φ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.bandSet ℓ d μ) :
    -(μ * (Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ ^ 2 * n)
        * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
      ≤ Work.SmallBoxSliding.qLHSwordB (N := n) h M ℓ d μ u Φ := by
  classical
  set C : ℝ := bandK v h M * bandS M ℓ d μ ^ 2 with hCdef
  have hFbound := w1Fibre_abs_le_bandS_qLHS (v := v) (h := h) hR hv_supp hM hℓ hd hμ hreg hregχ hu
  -- the unfolding of the word
  have hrhs : Work.SmallBoxSliding.qLHSwordB (N := n) h M ℓ d μ u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          (- μ * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
            + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    simp only [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword,
      Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair]
  -- pointwise lower bound for the bracket
  have hpt : ∀ x : Submission.BoseGases.X n,
      -(μ * (C * (n : ℝ))) ≤
        - μ * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
    intro x
    have hS : (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
        ≤ (n : ℝ) * C := by
      calc (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
          ≤ ∑ _i : Fin n, C :=
            Finset.sum_le_sum (fun i _ => le_trans (le_abs_self _) (hFbound (x i)))
        _ = (n : ℝ) * C := by simp [Finset.sum_const, nsmul_eq_mul]
    have hP : 0 ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) :=
      Finset.sum_nonneg fun p _ => wSmallPair_nonneg_qLHS hv M ℓ d u (x p.1) (x p.2)
    have h1 : -(μ * ((n : ℝ) * C))
        ≤ - μ * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y) := by
      have h := mul_le_mul_of_nonneg_left hS (le_of_lt hμ)
      linarith
    have h2 : 0 ≤ (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) :=
      mul_nonneg (by norm_num) hP
    have h3 : -(μ * (C * (n : ℝ))) = -(μ * ((n : ℝ) * C)) := by ring
    rw [h3]
    linarith
  -- integrability of the two integrands
  have hPhi2 : IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) volume := by
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n ℓ) (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (hcont.pow 2).continuousOn
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hcont.pow 2).aestronglyMeasurable B ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)
  have hint_lhs : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * (-(μ * (C * (n : ℝ)))))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    hPhi2.mul_const _
  have hint_rhs : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (- μ * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    integrable_qLHS_integrand_qLHS (v := v) (h := h) hv hv1 hR hv_supp hM hℓ hd hμ hreg hregχ
      hcont hu
  have hmono := integral_mono_ae hint_lhs hint_rhs
    (ae_of_all _ (fun x => mul_le_mul_of_nonneg_left (hpt x) (sq_nonneg _)))
  -- the left-hand integrand evaluates to `−(μ·C·n)·∫Φ²`
  have heval : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (-(μ * (C * (n : ℝ)))))
      = -(μ * (C * (n : ℝ))) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (-(μ * (C * (n : ℝ)))))
          = (fun x : Submission.BoseGases.X n => (-(μ * (C * (n : ℝ)))) * (Φ x) ^ 2) from by
            funext x; ring]
    rw [integral_const_mul]
  have hgoal : -(μ * (bandK v h M * bandS M ℓ d μ ^ 2 * (n : ℝ))
        * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (-(μ * (C * (n : ℝ)))) := by
    rw [heval, hCdef]
    ring
  rw [hrhs, hgoal]
  exact hmono

end Work.BoseFixB1
