import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.Winchk
import Submission.Work.BoseFixB1B.cutFibreMass_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.PortSmallB.cutFibreMassFactsSmallB`

The **fibre-mass facts** for the smooth approximants of the sharp box state, at the **cube**
window `χ^{S}_{B(u)} = chiSmallB M L d u` (the window of the matched sliding word
`Work.BoseFixB1B.sbWordCube`) instead of the **ball** window `chiB L d u`.

This is the *cube-window port* of the PROVED
`Submission.Work.BoseFixB1B.cutFibreMass_facts.cutFibreMass_facts`: everything in that file is
window-generic except for

* the support fact `chiB_eq_zero_of_notMem_dlBox` — replaced by the PROVED
  `Work.BoseB1Cube.Winchk.chiSmallB_eq_zero_of_notMem_dlBox`;
* the sup bound `|chiB| ≤ chiSup^2` — replaced by the PROVED
  `Work.BoseB1Cube.Winchk.abs_chiSmallB_le_kappaS` (`|chiSmallB M L d u| ≤ kappaS M`), so that
  the squared constant `chiSup^4` becomes `(kappaS M)^2`.

Consequently only the two window-dependent bricks are re-proved here
(`cutFibreMass_integrand_leS`, `cutFibreMass_sum_le_L2S`); every other ingredient of the chain
(`setIntegral_le_const`, `kcInsN_mem_abox`, `boxQ_kcInsN_eq`, `boxP_fibre_abs_le`,
`setIntegral_sq_sub_mean_le`, `integrableOn_fibreIntegral`, the box-margin null set and the
pointwise convergence of the two states) is imported verbatim from `Work.BoseFixB1B`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.PortSmallB

open Submission.BoseGases
open Work.BoseFixB1B
open Work.BoseB1Cube.Winchk

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The pointwise (in the outside configuration) fibre-mass bound, cube window -/

/-- **The pointwise fibre-mass bound** at the cube window.  For `r ∈ abox n L`, the
`chiSmallB`-windowed `L²`-mass of the mean-free slot-`i` fibre of `Ψ` is at most `(kappaS M)^2`
times the (unwindowed, unprojected) `L²`-mass of the same fibre. -/
lemma cutFibreMass_integrand_leS {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ}
    (hM : 1 ≤ M) (u : E3)
    {Ψ : X (n+1) → ℝ} (hΨm : Measurable Ψ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hΨb : ∀ x ∈ abox (n+1) L, |Ψ x| ≤ Cb) (i : Fin (n+1)) {r : X n}
    (hr : r ∈ abox n L) :
    (∫ y in acube L, (chiSmallB M L d u y * Work.SmallBoxTBWord.boxQ
        (SmallBoxSliding.boxMass L d u)
        (dlBox L d u) i Ψ ((kcInsN n i) (y, r)))^2)
      ≤ (kappaS M)^2 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by
  have hAmeas : MeasurableSet (dlBox L d u) := SmallBoxSliding.measurableSet_dlBox L d u
  have hAfin : (volume : Measure E3) (dlBox L d u) < ⊤ :=
    (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).measure_lt_top
  have hvol : SmallBoxSliding.boxMass L d u = (volume : Measure E3).real (dlBox L d u) :=
    SmallBoxSliding.boxMass_eq_measureReal L d u
  have hsub : dlBox L d u ⊆ acube L := SmallBoxSliding.dlBox_subset_acube L d u
  have hfcube : (volume : Measure E3) (acube L) < ⊤ := acube_lt_top L hL.le
  have hgmeas : Measurable (fun y : E3 => Ψ ((kcInsN n i) (y, r))) :=
    hΨm.comp ((kcInsN n i).measurable.comp (measurable_id.prod measurable_const))
  have hgb : ∀ y ∈ acube L, |Ψ ((kcInsN n i) (y, r))| ≤ Cb := fun y hy =>
    hΨb _ (kcInsN_mem_abox i hy ((mem_abox_iff n L r).mp hr))
  have hmb : |(1 / SmallBoxSliding.boxMass L d u) *
      ∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r))| ≤ Cb :=
    boxP_fibre_abs_le hL hd u hCb hΨb i hr
  have hχ : ∀ y : E3, |chiSmallB M L d u y| ≤ kappaS M := fun y =>
    abs_chiSmallB_le_kappaS hM u y
  set m : ℝ := (1 / SmallBoxSliding.boxMass L d u) *
    ∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r)) with hm
  have hmain : (∫ y in acube L, (chiSmallB M L d u y * (Ψ ((kcInsN n i) (y, r)) - m))^2)
      ≤ (kappaS M)^2 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by
    have htrunc : (∫ y in acube L, (chiSmallB M L d u y * (Ψ ((kcInsN n i) (y, r)) - m))^2)
        = ∫ y in dlBox L d u, (chiSmallB M L d u y * (Ψ ((kcInsN n i) (y, r)) - m))^2 :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (acube_measurable L) hsub
        (fun y hy => by
          rw [Work.BoseB1Cube.Winchk.chiSmallB_eq_zero_of_notMem_dlBox hM hL hd hy.2, zero_mul]
          norm_num)
    have hβint : IntegrableOn (fun y : E3 => (kappaS M)^2 *
        (Ψ ((kcInsN n i) (y, r)) - m)^2) (dlBox L d u) volume := by
      refine IntegrableOn.of_bound hAfin ?_ ((kappaS M)^2 * (2*Cb)^2) ?_
      · exact (((hgmeas.sub_const m).pow_const 2).const_mul _).aestronglyMeasurable
      · rw [ae_restrict_iff' hAmeas]
        refine ae_of_all _ (fun y hy => ?_)
        have h1 : |Ψ ((kcInsN n i) (y, r)) - m| ≤ 2 * Cb := by
          have habs : |Ψ ((kcInsN n i) (y, r)) - m|
              ≤ |Ψ ((kcInsN n i) (y, r))| + |m| := by
            simpa [Real.norm_eq_abs] using
              norm_sub_le (Ψ ((kcInsN n i) (y, r))) m
          rw [hm] at hmb ⊢
          linarith [hgb y (hsub hy)]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (kappaS M)),
          abs_of_nonneg (sq_nonneg _), ← sq_abs (Ψ ((kcInsN n i) (y, r)) - m)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h1 2) (sq_nonneg _)
    have step2 : (∫ y in dlBox L d u, (chiSmallB M L d u y * (Ψ ((kcInsN n i) (y, r)) - m))^2)
        ≤ ∫ y in dlBox L d u, (kappaS M)^2 * (Ψ ((kcInsN n i) (y, r)) - m)^2 :=
      setIntegral_le_of_le_ae hAmeas hβint
        (fun y _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (fun y _ => by
          rw [mul_pow, ← sq_abs (chiSmallB M L d u y)]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) (hχ y) 2) (sq_nonneg _))
    have step3 : (∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)) - m)^2)
        ≤ ∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)))^2 := by
      have h := setIntegral_sq_sub_mean_le (A := dlBox L d u)
        (volA := SmallBoxSliding.boxMass L d u) (Cb := Cb) hAmeas hAfin hvol hgmeas hCb
        (fun y hy => hgb y (hsub hy))
      simpa only [hm] using h
    have step4 : (∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)))^2)
        ≤ ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by
      refine setIntegral_mono_set (f := fun y : E3 => (Ψ ((kcInsN n i) (y, r)))^2) ?_ ?_ ?_
      · exact IntegrableOn.of_bound hfcube (hgmeas.pow_const 2).aestronglyMeasurable (Cb ^ 2) (by
          rw [ae_restrict_iff' (acube_measurable L)]
          exact ae_of_all _ (fun y hy => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hgb y hy) 2))
      · exact ae_of_all _ (fun y => sq_nonneg _)
      · exact ae_of_all _ (fun y hy => hsub hy)
    calc (∫ y in acube L, (chiSmallB M L d u y * (Ψ ((kcInsN n i) (y, r)) - m))^2)
        = ∫ y in dlBox L d u, (chiSmallB M L d u y * (Ψ ((kcInsN n i) (y, r)) - m))^2 :=
          htrunc
      _ ≤ ∫ y in dlBox L d u, (kappaS M)^2 * (Ψ ((kcInsN n i) (y, r)) - m)^2 := step2
      _ = (kappaS M)^2 * ∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)) - m)^2 :=
          integral_const_mul _ _
      _ ≤ (kappaS M)^2 * ∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)))^2 :=
          mul_le_mul_of_nonneg_left step3 (sq_nonneg _)
      _ ≤ (kappaS M)^2 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 :=
          mul_le_mul_of_nonneg_left step4 (sq_nonneg _)
  have hQ : ∀ y : E3, Work.SmallBoxTBWord.boxQ (SmallBoxSliding.boxMass L d u) (dlBox L d u) i Ψ
      ((kcInsN n i) (y, r)) = Ψ ((kcInsN n i) (y, r)) - m := by
    intro y
    rw [boxQ_kcInsN_eq, hm]
  simpa only [hQ] using hmain

/-! ## 2. The total fibre mass is bounded by the `L²`-mass, cube window -/

/-- **The fibre mass is dominated by the `L²`-mass** at the cube window: for a measurable state
`Ψ` bounded by `Cb` on the box, the sum of the `chiSmallB`-windowed, mean-free fibre masses is at
most `(n+1)·(kappaS M)^2` times the `L²`-mass of `Ψ` on the box. -/
theorem cutFibreMass_sum_le_L2S {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ}
    (hM : 1 ≤ M) (u : E3)
    {Ψ : X (n+1) → ℝ} (hΨm : Measurable Ψ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hΨb : ∀ x ∈ abox (n+1) L, |Ψ x| ≤ Cb) :
    ∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
        (chiSmallB M L d u) i Ψ
      ≤ (↑(n+1) : ℝ) * ((kappaS M)^2 * ∫ x in abox (n+1) L, (Ψ x)^2) := by
  have hInt : IntegrableOn (fun x : X (n+1) => (Ψ x)^2) (abox (n+1) L) volume :=
    IntegrableOn.of_bound (abox_lt_top (n+1) L hL.le) (hΨm.pow_const 2).aestronglyMeasurable
      (Cb^2) (by
        rw [ae_restrict_iff' (abox_measurable (n+1) L)]
        exact ae_of_all _ (fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hΨb x hx) 2))
  have hper : ∀ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
      (chiSmallB M L d u) i Ψ ≤ (kappaS M)^2 * ∫ x in abox (n+1) L, (Ψ x)^2 := by
    intro i
    have hstep : (∫ r in abox n L, ∫ y in acube L, (chiSmallB M L d u y *
          Work.SmallBoxTBWord.boxQ
          (SmallBoxSliding.boxMass L d u) (dlBox L d u) i Ψ ((kcInsN n i) (y, r)))^2)
        ≤ (kappaS M)^2 * ∫ x in abox (n+1) L, (Ψ x)^2 := by
      calc (∫ r in abox n L, ∫ y in acube L, (chiSmallB M L d u y *
              Work.SmallBoxTBWord.boxQ
              (SmallBoxSliding.boxMass L d u) (dlBox L d u) i Ψ ((kcInsN n i) (y, r)))^2)
          ≤ ∫ r in abox n L, (kappaS M)^2 * ∫ y in acube L,
              (Ψ ((kcInsN n i) (y, r)))^2 :=
            setIntegral_le_of_le_ae (abox_measurable n L)
              ((integrableOn_fibreIntegral i hL hΨm hCb hΨb).const_mul _)
              (fun r _ => mul_nonneg (sq_nonneg (kappaS M))
                (integral_nonneg_of_ae (ae_of_all _ (fun y => sq_nonneg _))))
              (fun r hr => cutFibreMass_integrand_leS hL hd hM u hΨm hCb hΨb i hr)
        _ = (kappaS M)^2 * ∫ r in abox n L, ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 :=
            integral_const_mul _ _
        _ = (kappaS M)^2 * ∫ x in abox (n+1) L, (Ψ x)^2 := by
            rw [abox_integral_peel i (fun x => (Ψ x)^2) hInt]
    simpa only [cutFibreMass] using hstep
  calc (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
        (chiSmallB M L d u) i Ψ)
      ≤ ∑ _i : Fin (n+1), (kappaS M)^2 * ∫ x in abox (n+1) L, (Ψ x)^2 :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = (↑(n+1) : ℝ) * ((kappaS M)^2 * ∫ x in abox (n+1) L, (Ψ x)^2) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-! ## 3. The fibre-mass facts at the cube window -/

theorem cutFibreMassFactsSmallB {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    (∃ C : ℝ, 0 ≤ C ∧
      (∀ δ : ℝ, 0 < δ → ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiSmallB M L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) ≤ C) ∧
      (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) ≤ C))
    ∧ Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i
        (fun x => Work.BoseFixB1B.cutProd (γ δ) ψ x
          - Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hM1 : 1 ≤ M := by omega
  set CC : ℝ := (↑(n+1) : ℝ) * (kappaS M)^2 * Cb^2 * (L^3)^(n+1) with hCC
  have hCC0 : 0 ≤ CC := by
    rw [hCC]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (kappaS M)))
      (pow_nonneg hCb 2)) (pow_nonneg (pow_nonneg hL.le 3) _)
  have hmeasS : Measurable (sharpBoxState (dlBox L d u) ψ) :=
    cutFibre_measurable_sharpBoxState (SmallBoxSliding.measurableSet_dlBox L d u)
      hψ.continuous.measurable
  have hmass : ∀ {ω : X (n+1) → ℝ}, (∀ x ∈ abox (n+1) L, |ω x| ≤ Cb) →
      ∫ x in abox (n+1) L, (ω x)^2 ≤ Cb^2 * (L^3)^(n+1) := by
    intro ω hω
    have hle : ∫ x in abox (n+1) L, (ω x)^2
        ≤ Cb^2 * (volume : Measure (X (n+1))).real (abox (n+1) L) :=
      setIntegral_le_const (abox_measurable (n+1) L) (abox_lt_top (n+1) L hL.le) (sq_nonneg _)
        (fun x hx => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hω x hx) 2)
    rwa [volume_real_abox (n+1) hL.le] at hle
  have hK0 : 0 ≤ (↑(n+1) : ℝ) * (kappaS M)^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (kappaS M))
  refine ⟨⟨CC, hCC0, ⟨?_, ?_⟩⟩, ?_⟩
  · intro δ hδ
    have hmeas : Measurable (cutProd (γ δ) ψ) :=
      cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous hψ.continuous
    have hb := cutFibre_abs_cutProd_le hL hcut hδ hCb hψb
    calc (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
          (chiSmallB M L d u) i (cutProd (γ δ) ψ))
        ≤ (↑(n+1) : ℝ) * ((kappaS M)^2 * ∫ x in abox (n+1) L, (cutProd (γ δ) ψ x)^2) :=
          cutFibreMass_sum_le_L2S hL hd hM1 u hmeas hCb hb
      _ = (↑(n+1) : ℝ) * (kappaS M)^2 * (∫ x in abox (n+1) L, (cutProd (γ δ) ψ x)^2) := by
          ring
      _ ≤ (↑(n+1) : ℝ) * (kappaS M)^2 * (Cb^2 * (L^3)^(n+1)) :=
          mul_le_mul_of_nonneg_left (hmass hb) hK0
      _ = CC := by rw [hCC]; ring
  · have hb : ∀ x ∈ abox (n+1) L, |sharpBoxState (dlBox L d u) ψ x| ≤ Cb :=
      cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb
    calc (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
          (chiSmallB M L d u) i (sharpBoxState (dlBox L d u) ψ))
        ≤ (↑(n+1) : ℝ) * ((kappaS M)^2 * ∫ x in abox (n+1) L,
            (sharpBoxState (dlBox L d u) ψ x)^2) :=
          cutFibreMass_sum_le_L2S hL hd hM1 u hmeasS hCb hb
      _ = (↑(n+1) : ℝ) * (kappaS M)^2 * (∫ x in abox (n+1) L,
            (sharpBoxState (dlBox L d u) ψ x)^2) := by ring
      _ ≤ (↑(n+1) : ℝ) * (kappaS M)^2 * (Cb^2 * (L^3)^(n+1)) :=
          mul_le_mul_of_nonneg_left (hmass hb) hK0
      _ = CC := by rw [hCC]; ring
  · have hkey : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
          (chiSmallB M L d u) i
          (fun x => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x))
        ≤ (↑(n+1) : ℝ) * ((kappaS M)^2 *
          (∫ x in abox (n+1) L,
            (cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2)) := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hmeas : Measurable
          (fun x => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x) :=
        (cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous hψ.continuous).sub hmeasS
      have hb : ∀ x ∈ abox (n+1) L,
          |cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x| ≤ 2 * Cb := by
        intro x hx
        have habs : |cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x|
            ≤ |cutProd (γ δ) ψ x| + |sharpBoxState (dlBox L d u) ψ x| := by
          simpa [Real.norm_eq_abs] using
            norm_sub_le (cutProd (γ δ) ψ x) (sharpBoxState (dlBox L d u) ψ x)
        have hA := cutFibre_abs_cutProd_le hL hcut hδ hCb hψb x hx
        have hB : |sharpBoxState (dlBox L d u) ψ x| ≤ Cb :=
          cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb x hx
        linarith
      exact cutFibreMass_sum_le_L2S (Cb := 2 * Cb) hL hd hM1 u hmeas
        (mul_nonneg (by norm_num) hCb) hb
    have hbound : Filter.Tendsto
        (fun δ : ℝ => (↑(n+1) : ℝ) * ((kappaS M)^2 *
          (∫ x in abox (n+1) L,
            (cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : Filter.Tendsto (fun _ : ℝ => (↑(n+1) : ℝ) * (kappaS M)^2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((↑(n+1) : ℝ) * (kappaS M)^2)) :=
        tendsto_const_nhds
      have h := hc.mul (cutFibreMass_tendsto_integral_sq hL hd u hcut hψ.continuous hCb hψb)
      simpa [mul_assoc] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ hkey
    exact Filter.Eventually.of_forall (fun δ => Finset.sum_nonneg (fun i _ => by
      unfold Work.BoseFixB1B.cutFibreMass
      exact integral_nonneg_of_ae (ae_of_all _ (fun r =>
        integral_nonneg_of_ae (ae_of_all _ (fun y => sq_nonneg _))))))

end Work.BoseB1Cube.PortSmallB
