import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Ledger
import Submission.Work.BoseFixB3.CS.Pieces.integrable_prod_wPair_mul_bounded
import Submission.Work.BoseFixB3.CS.Pieces.leakCoupl_swap
import Submission.Work.BoseFixB3.CS.Pieces.leakFn_abs_le
import Submission.Work.BoseFixB3.CS.Pieces.null_prod_preimage_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.CS_pair_hyps_of_integrable`

The **first two conjuncts** of `Pieces.CS_side_hyps`, *with the missing standing hypothesis*
`MeasureTheory.Integrable v` added.  See
`Pieces/FINDING_CS_side_hyps_missing_Integrable_v.md` (in this directory) for why the hypothesis
is needed: both conjuncts are integrability of `wLoc ℓ h 0`-weighted integrands over
`volume.prod volume`, and (via `wLoc ℓ h 0 = wPair ℓ h` and Tonelli) they are the assertions
`v · w₀ ^ 2 ∈ L¹` and `g₀ · w₀ ∈ L¹`; the first is *not* implied by the hypotheses of
`CS_side_hyps`.

The work is done by the full-space pair-integrability lemma
`Pieces.integrable_prod_wPair_mul_bounded` (an a.e.-bounded measurable weight times
`wPair ℓ h` for `h ∈ L¹` supported in `ball 0 R`), fed with the a.e. bounds `0 ≤ w₀ ≤ 1`
(`Submission.BoseGases.scattering_bounds_ae`) pulled back along `(z₁,z₂) ↦ z₁ - z₂`
(null preimages of null sets: `Pieces.null_prod_preimage_sub`).
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `wLoc ℓ h 0 = wPair ℓ h` (`chiU ℓ 0 = chiScale ℓ`). -/
lemma wLoc_zero_eq_wPair' (ℓ : ℝ) (h : E3 → ℝ) (x y : E3) :
    Submission.BoseGases.wLoc ℓ h 0 x y = Submission.BoseGases.wPair ℓ h x y := by
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.chiU,
    Submission.BoseGases.chiScale, Submission.BoseGases.wScaled]

/-- A `volume`-a.e. statement pulls back to a `volume.prod volume`-a.e. statement along
`(x,y) ↦ x - y`: the pullback of a null set is null (`Pieces.null_prod_preimage_sub`). -/
lemma ae_prod_sub_of_ae {p : E3 → Prop}
    (hp : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure E3), p t) :
    ∀ᵐ z ∂(MeasureTheory.volume.prod MeasureTheory.volume), p (z.1 - z.2) := by
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure E3) {t : E3 | ¬ p t} = 0 :=
    MeasureTheory.ae_iff.mp hp
  rw [MeasureTheory.ae_iff]
  have hset : {a : E3 × E3 | ¬ p (a.1 - a.2)}
      = {z : E3 × E3 | z.1 - z.2 ∈ {t : E3 | ¬ p t}} := by
    ext z; exact Iff.rfl
  rw [hset]
  exact null_prod_preimage_sub hnull

/-- The composite `z ↦ w (z.1 - z.2)` is a.e. strongly measurable on the product measure for
any locally integrable `w`. -/
lemma aestronglyMeasurable_sub_prod {w : E3 → ℝ} (hw : LocallyIntegrable w) :
    AEStronglyMeasurable (fun z : E3 × E3 => w (z.1 - z.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hwaem : AEStronglyMeasurable w (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    hw.aestronglyMeasurable
  let m : E3 → ℝ := AEStronglyMeasurable.mk w hwaem
  have hsm : StronglyMeasurable m := hwaem.stronglyMeasurable_mk
  have heq : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure E3), m t = w t :=
    hwaem.ae_eq_mk.symm
  have hcomp : StronglyMeasurable (fun z : E3 × E3 => m (z.1 - z.2)) :=
    hsm.comp_measurable
      ((measurable_fst.sub measurable_snd) : Measurable fun z : E3 × E3 => z.1 - z.2)
  refine hcomp.aestronglyMeasurable.congr ?_
  filter_upwards [ae_prod_sub_of_ae (p := fun t => m t = w t) heq] with z hz
  exact hz

/-- **The two pair-level conjuncts of `CS_side_hyps` under `Integrable v`** (the first two
conjuncts of the target, verbatim). -/
theorem CS_pair_hyps_of_integrable {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_int : MeasureTheory.Integrable v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun z : E3 × E3 =>
        (Classical.choose h (z.1 - z.2)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 z.1 z.2) ∧
    MeasureTheory.Integrable (fun z : E3 × E3 =>
        Work.BoseFixB3.CS.leakFn fc κ ℓ z.2 * (Classical.choose h (z.1 - z.2))
          * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 z.1 z.2) := by
  classical
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  obtain ⟨hw0, hw1⟩ :=
    Submission.BoseGases.scattering_bounds_ae hR hv hvrad hv_supp hrad hw
  have hsubsm : AEStronglyMeasurable (fun z : E3 × E3 => Classical.choose h (z.1 - z.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    aestronglyMeasurable_sub_prod hw.lhs_integrable
  refine ⟨?_, ?_⟩
  · -- conjunct 1: `w₀² · wLoc ℓ v 0`
    have key := integrable_prod_wPair_mul_bounded (ℓ := ℓ) (R := R) hℓ (h := v) hv_int hsuppv hRℓ
      (B := fun a b : E3 => (Classical.choose h (a - b)) ^ 2) ?_ (C := 1) (by norm_num) ?_
    · have hAB : (fun z : E3 × E3 =>
            (Classical.choose h (z.1 - z.2)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 z.1 z.2)
          = fun z : E3 × E3 =>
            (Classical.choose h (z.1 - z.2)) ^ 2 * Submission.BoseGases.wPair ℓ v z.1 z.2 := by
        funext z
        rw [wLoc_zero_eq_wPair']
      rw [hAB]
      exact key
    · have h2 : AEStronglyMeasurable (fun z : E3 × E3 => (Classical.choose h (z.1 - z.2)) ^ 2)
          (MeasureTheory.volume.prod MeasureTheory.volume) := hsubsm.pow 2
      simpa only [Function.uncurry_def, Pi.pow_apply] using h2
    · filter_upwards [ae_prod_sub_of_ae hw0, ae_prod_sub_of_ae hw1] with z hz0 hz1
      have hz : (Classical.choose h (z.1 - z.2)) ^ 2 ≤ 1 := by nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz
  · -- conjunct 2: `leakFn fc κ ℓ · w₀ · wLoc ℓ (g₀ v h) 0`
    have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR hv_supp h
    have hgS : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 := fun z hz =>
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
    have hleaksm : StronglyMeasurable (fun z : E3 × E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ z.2) :=
      (leakSwap_leakFn_sm fc κ ℓ).comp_measurable
        (measurable_snd : Measurable fun z : E3 × E3 => z.2)
    have key := integrable_prod_wPair_mul_bounded (ℓ := ℓ) (R := R) hℓ
      (h := Submission.BoseGases.g0 v h) hgI hgS hRℓ
      (B := fun a b : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ b * Classical.choose h (a - b))
      ?_ (C := (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
        (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal)) (by positivity) ?_
    · have hAB : (fun z : E3 × E3 =>
            Work.BoseFixB3.CS.leakFn fc κ ℓ z.2 * (Classical.choose h (z.1 - z.2))
              * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 z.1 z.2)
          = fun z : E3 × E3 =>
            (Work.BoseFixB3.CS.leakFn fc κ ℓ z.2 * Classical.choose h (z.1 - z.2))
              * Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) z.1 z.2 := by
        funext z
        rw [wLoc_zero_eq_wPair']
      rw [hAB]
      exact key
    · have h3 : AEStronglyMeasurable
          (fun z : E3 × E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ z.2
            * Classical.choose h (z.1 - z.2))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        hleaksm.aestronglyMeasurable.mul hsubsm
      simpa only [Function.uncurry_def] using h3
    · filter_upwards [ae_prod_sub_of_ae hw0, ae_prod_sub_of_ae hw1] with z hz0 hz1
      have hb := leakFn_abs_le fc hκ hℓ z.2
      have hwabs : |Classical.choose h (z.1 - z.2)| ≤ 1 := by
        rw [abs_of_nonneg hz0]; exact hz1
      rw [Real.norm_eq_abs, abs_mul]
      calc |Work.BoseFixB3.CS.leakFn fc κ ℓ z.2| * |Classical.choose h (z.1 - z.2)|
          ≤ (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
              (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) * 1 :=
            mul_le_mul hb hwabs (abs_nonneg _) (by positivity)
        _ = 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
              (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal := by ring

end

end Work.BoseFixB3.CS.Pieces
