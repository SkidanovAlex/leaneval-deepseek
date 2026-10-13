/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/Main`: the per-term bounds for the slot transport estimate

This module contains the analytic infrastructure for the per-slot `T2Slot` estimate:
elementary monotonicity facts for the canonical weight `canonW q z θ = w(z)² sin(2θ)^{-q}`,
the three "generic" Leibniz-term bounds (a sup factor on one factor and a Cauchy–Schwarz /
AM–GM bound on the other two) and the "top-slot" bound obtained from the radial integration
by parts.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.slotCS
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.TransportS.SlotT2

/-! ## Elementary monotonicity of the canonical weight -/

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ^{-η} ≤ σ^{-η'}` for `η ≤ η'` and `σ ∈ (0,1]`. -/
theorem rpow_neg_le_neg {σ a b : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hab : a ≤ b) :
    σ ^ (-a) ≤ σ ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)

/-- For `0 ≤ q ≤ 1 + η`, `σ^{1-q} ≤ σ^{-η}` on `σ ∈ (0,1]`. -/
theorem rpow_one_sub_le {σ q : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hq : q ≤ 1 + Work.Spaces.eta) : σ ^ (1 - q) ≤ σ ^ (-Work.Spaces.eta) :=
  Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)

theorem sqrt_mul_sqrt_le_half (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  have h := two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)
  rw [Real.sq_sqrt hx, Real.sq_sqrt hy] at h
  linarith

/-! ## Almost everywhere versions of the two standard facts -/

/-- A pointwise statement for interior angles upgrades to an a.e. statement on `Iθ`. -/
theorem ae_of_forall_Ioo {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), P θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), P θ := by
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- A pointwise statement for positive radii upgrades to an a.e. statement on `Iz`. -/
theorem ae_of_forall_Ioi {P : ℝ → Prop} (h : ∀ z, 0 < z → P z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), P z := by
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume))).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-! ## A slot predicate on the open quadrant

The Mathlib-side predicate `SlotW` demands the domination at *all* angles of `Iθ`, including the
endpoints `θ ∈ {0, π/2}`, where the weight `canonW 0 = w²` does not vanish.  For the exponent
`q = 0` (the leaf weight `w²`) the domination therefore fails there, while all the arguments
only ever use interior angles.  The predicate below only asks for the interior bound. -/

/-- The interior version of `SlotW`: `canonW q · X²` is dominated by the `ℋ⁴`-integrand of `f`
on the *open* quadrant. -/
def SlotWo (α q : ℝ) (X : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ

theorem SlotWo.of_slotW {α q : ℝ} {X f : ℝ → ℝ → ℝ} (h : SlotW α q X f) :
    SlotWo α q X f :=
  fun z θ hz hθ hθ2 => h.le z hz.le θ ⟨hθ.le, hθ2.le⟩

theorem slotWo_z {α : ℝ} {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (f : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) : SlotWo α q (Work.Spaces.DzIter j f) f :=
  SlotWo.of_slotW (slotW_z α hq0 hq f j hj)

theorem slotWo_mixed {α : ℝ} {q : ℝ} (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    SlotWo α q (Work.Spaces.mixed j i f) f :=
  SlotWo.of_slotW (slotW_mixed α hq0 hqγ f j i hi hij)

/-- The pure `D_z`-slots at exponent `0` are slots for the `ℋ⁴`-integrand. -/
theorem slotWo_zero_z {α : ℝ} (f : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) :
    SlotWo α 0 (Work.Spaces.DzIter j f) f := by
  intro z θ hz hθ hθ2
  have hη := (slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl f j hj)
    z θ hz hθ hθ2
  have hle : canonW 0 z θ ≤ canonW Work.Spaces.eta z θ := by
    have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
      simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
    rw [h1, canonW]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (one_le_rpow_neg Work.Spaces.eta_nonneg ⟨hθ, hθ2⟩)
  exact le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) hη

/-- The mixed slots at exponent `0` are slots for the `ℋ⁴`-integrand. -/
theorem slotWo_zero_mixed {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) : SlotWo α 0 (Work.Spaces.mixed j i f) f := by
  intro z θ hz hθ hθ2
  have hγ0 : 0 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.gam_pos hα)
  have hγ := (slotWo_mixed (α := α) (q := Work.Spaces.gam α) (Work.Spaces.gam_pos hα)
    le_rfl f j i hi hij) z θ hz hθ hθ2
  have hle : canonW 0 z θ ≤ canonW (Work.Spaces.gam α) z θ := by
    have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
      simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
    rw [h1, canonW]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (one_le_rpow_neg hγ0 ⟨hθ, hθ2⟩)
  exact le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) hγ

/-! ## The pointwise splitting of a product of two canonical slots -/

/-- On the interval `Iθ`, `canonW q z θ · |G| · |Y|` is the product of the square roots of the
two `q`-weighted squares. -/
theorem canonW_mul_abs_eq {q z θ : ℝ} {G Y : ℝ → ℝ → ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * |G z θ| * |Y z θ|
      = Real.sqrt (canonW q z θ * (G z θ) ^ 2)
        * Real.sqrt (canonW q z θ * (Y z θ) ^ 2) := by
  have hc : 0 ≤ canonW q z θ := canonW_nonneg hθ
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [show (Real.sqrt (canonW q z θ) * |G z θ|) * (Real.sqrt (canonW q z θ) * |Y z θ|)
      = (Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ)) * (|G z θ| * |Y z θ|) from by
    ring]
  rw [Real.mul_self_sqrt hc]
  ring

/-- The canonical weight vanishes at `z = 0`. -/
theorem canonW_zero (q θ : ℝ) : canonW q 0 θ = 0 := by
  simp [canonW, Work.Spaces.w]

/-- The product `√A · √B` of two `θ`-slice integrable densities is integrable (dominated by
the arithmetic mean). -/
theorem integrable_sqrt_mul_sqrt_slice {A B : ℝ → ℝ} {s : Set ℝ}
    (hA : MeasureTheory.IntegrableOn A s)
    (hB : MeasureTheory.IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    MeasureTheory.IntegrableOn (fun x => Real.sqrt (A x) * Real.sqrt (B x)) s := by
  refine MeasureTheory.Integrable.mono' ((hA.add hB).const_mul (1/2)) ?_ ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    show Real.sqrt (A x) * Real.sqrt (B x) ≤ (1/2) * (A x + B x)
    rw [show (1/2 : ℝ) * (A x + B x) = (A x + B x) / 2 from by ring]
    exact sqrt_mul_sqrt_le_half (A x) (B x) (hAnn x) (hBnn x)

/-! ## The three generic Leibniz-term bounds -/

/-- **The "sup on the coefficient" term bound.**  If the first factor of a Leibniz summand is
bounded by `KF` and the other two factors are canonical `ℋ⁴`-slots of `g` (with the same
exponent `q`), then the iterated integral is at most `KF · HkSq α 4 g`. -/
theorem termBoundF {α q KF : ℝ} {f g : ℝ → ℝ → ℝ} {b1 a1 : ℕ} {G Y : ℝ → ℝ → ℝ}
    (hS2 : SlotWo α q G g) (hS3 : SlotWo α q Y g) (hKF : 0 ≤ KF)
    (hFb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.mixed b1 a1 f z θ| ≤ KF)
    (hmemg : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
      ≤ KF * Work.Spaces.HkSq α 4 g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the pointwise domination on interior angles
  have hpt : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|
        ≤ KF * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hGsq : canonW q z θ * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      hS2 z θ hz hθ.1 hθ.2
    have hYsq : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      hS3 z θ hz hθ.1 hθ.2
    have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hGY : canonW q z θ * |G z θ| * |Y z θ| ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [canonW_mul_abs_eq (q := q) (G := G) (Y := Y) hθI]
      calc Real.sqrt (canonW q z θ * (G z θ) ^ 2)
            * Real.sqrt (canonW q z θ * (Y z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul (Real.sqrt_le_sqrt hGsq) (Real.sqrt_le_sqrt hYsq)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = Work.Spaces.HkIntegrand α 4 g z θ :=
            Real.mul_self_sqrt hHnn
    calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|
        = |Work.Spaces.mixed b1 a1 f z θ| * (canonW q z θ * |G z θ| * |Y z θ|) := by ring
      _ ≤ KF * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul (hFb z θ hz hθ.1 hθ.2) hGY
            (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)) hKF
  -- the angular monotonicity
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, KF * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ ((hmemg.1 z hz).const_mul KF) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
      exact mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
        (abs_nonneg _)) (abs_nonneg _)
    · rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | hz0
      · subst h0
        filter_upwards with θ
        rw [canonW_zero, zero_mul, zero_mul, zero_mul]
        exact mul_nonneg hKF (Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
      · exact ae_of_forall_Ioo (fun θ hθ => hpt z hz0 θ hθ)
  -- the radial monotonicity
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, KF * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 g z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmemg.2.const_mul KF) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => ?_)
      exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
        mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
          (abs_nonneg _)) (abs_nonneg _))
    · refine ae_of_forall_Ioi (fun z hz => ?_)
      show (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
        ≤ KF * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ
      rw [← MeasureTheory.integral_const_mul]
      exact hslice z hz.le
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, KF * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 g z θ := houter
    _ = KF * Work.Spaces.HkSq α 4 g := by
        rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]

/-- **The "sup on a `g`-slot" term bound.**  If the middle factor is bounded by `KG` and the
two remaining factors are canonical `ℋ⁴`-slots of `f` resp. `g` with the same exponent `q`,
then the iterated integral is at most `KG · |f|_{ℋ⁴} · |g|_{ℋ⁴}`. -/
theorem termBoundG {α q KG : ℝ} {f g : ℝ → ℝ → ℝ} {j2 i2 : ℕ} {F Y : ℝ → ℝ → ℝ}
    (hS1 : SlotWo α q F f) (hS3 : SlotWo α q Y g) (hKG : 0 ≤ KG)
    (hGb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.mixed j2 i2 g z θ| ≤ KG)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|)
      ≤ KG * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set Ff : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ with hFf
  set Gg : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hGg
  have hFf_int : MeasureTheory.IntegrableOn Ff Work.Spaces.Iz := hmemf.2
  have hGg_int : MeasureTheory.IntegrableOn Gg Work.Spaces.Iz := hmemg.2
  have hFf_nn : ∀ z, 0 ≤ Ff z := fun z => MeasureTheory.setIntegral_nonneg hIθm
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
  have hGg_nn : ∀ z, 0 ≤ Gg z := fun z => MeasureTheory.setIntegral_nonneg hIθm
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  -- the pointwise domination on interior angles
  have hpt : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      canonW q z θ * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|
        ≤ KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
    intro z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hFsq : canonW q z θ * (F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      hS1 z θ hz hθ.1 hθ.2
    have hYsq : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      hS3 z θ hz hθ.1 hθ.2
    have hFY : canonW q z θ * |F z θ| * |Y z θ|
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
      rw [canonW_mul_abs_eq (q := q) (G := F) (Y := Y) hθI]
      exact mul_le_mul (Real.sqrt_le_sqrt hFsq) (Real.sqrt_le_sqrt hYsq)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc canonW q z θ * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|
        = (canonW q z θ * |F z θ| * |Y z θ|) * |Work.Spaces.mixed j2 i2 g z θ| := by ring
      _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) * KG :=
          mul_le_mul hFY (hGb z θ hz hθ.1 hθ.2) (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by ring
  -- the angular monotonicity down to `KG · √Ff · √Gg`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|)
        ≤ KG * (Real.sqrt (Ff z) * Real.sqrt (Gg z)) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hzero : (∫ θ in Work.Spaces.Iθ, canonW q 0 θ
          * |F 0 θ| * |Work.Spaces.mixed j2 i2 g 0 θ| * |Y 0 θ|) = 0 := by
        rw [show (fun θ => canonW q 0 θ * |F 0 θ|
            * |Work.Spaces.mixed j2 i2 g 0 θ| * |Y 0 θ|) = fun _ => (0:ℝ) from by
          funext θ; rw [canonW_zero]; ring]
        simp
      rw [hzero]
      exact mul_nonneg hKG (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · have hprod : MeasureTheory.Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        integrable_sqrt_mul_sqrt_slice (hmemf.1 z hz) (hmemg.1 z hz)
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
      have h1 : (∫ θ in Work.Spaces.Iθ, canonW q z θ
            * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hprod.const_mul KG) ?_
        · refine MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
          exact mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
            (abs_nonneg _)) (abs_nonneg _)
        · exact ae_of_forall_Ioo (fun θ hθ => hpt z hz0 θ hθ)
      have h2 : (∫ θ in Work.Spaces.Iθ, KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)))
          = KG * ∫ θ in Work.Spaces.Iθ, (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) :=
        MeasureTheory.integral_const_mul KG _
      have h3 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          ≤ Real.sqrt (Ff z) * Real.sqrt (Gg z) := by
        have h := cs_sqrt_le (s := Work.Spaces.Iθ) (hmemf.1 z hz) (hmemg.1 z hz)
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
        simpa only [hFf, hGg] using h
      rw [h2] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_left h3 hKG)
  -- the radial monotonicity and the two-level Cauchy–Schwarz
  have hprod_int : MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (Ff z) * Real.sqrt (Gg z)) Work.Spaces.Iz :=
    integrable_sqrt_mul_sqrt_slice hFf_int hGg_int hFf_nn hGg_nn
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|)
      ≤ KG * ∫ z in Work.Spaces.Iz, Real.sqrt (Ff z) * Real.sqrt (Gg z) := by
    have hstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|)
        ≤ ∫ z in Work.Spaces.Iz, KG * (Real.sqrt (Ff z) * Real.sqrt (Gg z)) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hprod_int.const_mul KG) ?_
      · refine MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => ?_)
        exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
          mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
            (abs_nonneg _)) (abs_nonneg _))
      · exact ae_of_forall_Ioi (fun z hz => hslice z hz.le)
    rwa [MeasureTheory.integral_const_mul] at hstep
  have hcs : (∫ z in Work.Spaces.Iz, Real.sqrt (Ff z) * Real.sqrt (Gg z))
      ≤ Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
    have h := cs_sqrt_le (s := Work.Spaces.Iz) hFf_int hGg_int hFf_nn hGg_nn
    simpa only [hFf, hGg, Work.Spaces.HkSq] using h
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |F z θ| * |Work.Spaces.mixed j2 i2 g z θ| * |Y z θ|)
      ≤ KG * ∫ z in Work.Spaces.Iz, Real.sqrt (Ff z) * Real.sqrt (Gg z) := houter
    _ ≤ KG * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 g)) :=
        mul_le_mul_of_nonneg_left hcs hKG
    _ = KG * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := by
        simp only [Work.Spaces.HkNorm]

/-- **The σ-gain term bound.**  If the coefficient factor carries a factor `σ = sin 2θ` and
the other two factors are `ℋ⁴`-slots of `g` (a pure one priced with `η` and a mixed one priced
with `γ`), then the iterated integral is at most `CK · HkSq α 4 g`. -/
theorem termBoundSigma {α q CK : ℝ} {f g : ℝ → ℝ → ℝ} {b1 a1 : ℕ} {G Y : ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hCK : 0 ≤ CK) (hFb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ CK * Real.sin (2 * θ))
    (hq : q ≤ 1 + Work.Spaces.eta)
    (hS2 : SlotWo α Work.Spaces.eta G g) (hS3 : SlotWo α (Work.Spaces.gam α) Y g)
    (hmemg : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
      ≤ CK * Work.Spaces.HkSq α 4 g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]
    linarith [hα, Work.Spaces.eta_lt_one]
  -- the pointwise domination on interior angles
  have hpt : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|
        ≤ CK * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
    have hσ1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
    have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hGnn : 0 ≤ canonW q z θ * |G z θ| * |Y z θ| :=
      mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)
    have hGsq : canonW Work.Spaces.eta z θ * (G z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := hS2 z θ hz hθ.1 hθ.2
    have hYsq : canonW (Work.Spaces.gam α) z θ * (Y z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := hS3 z θ hz hθ.1 hθ.2
    have hsplit : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
        = Real.sin (2 * θ) ^ (1 - q) := by
      rw [show (1:ℝ) - q = 1 + (-q) by ring, Real.rpow_add hσ0, Real.rpow_one]
    have hmix : Real.sin (2 * θ) ^ (1 - q) ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
      rpow_one_sub_le hσ0 hσ1 hq
    have hGY : Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      have h1 : Real.sin (2 * θ) * canonW q z θ
          = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (1 - q) := by
        rw [canonW]
        rw [show Real.sin (2 * θ) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q))
            = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)) from by
          ring]
        rw [hsplit]
      have h3 : (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (1 - q)
          ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_left hmix hw
      have hstep1 : Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
          ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (|G z θ| * |Y z θ|) := by
        rw [show Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
            = (Real.sin (2 * θ) * canonW q z θ) * (|G z θ| * |Y z θ|) from by ring, h1]
        exact mul_le_mul_of_nonneg_right h3 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hGYabs : |G z θ| * |Y z θ| ≤ (G z θ ^ 2 + Y z θ ^ 2) / 2 := by
        have h := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (G z θ) (Y z θ)
        rwa [abs_mul] at h
      have hstep2 : (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            * (|G z θ| * |Y z θ|)
          ≤ (1 / 2) * ((canonW Work.Spaces.eta z θ * (G z θ) ^ 2)
              + (canonW Work.Spaces.eta z θ * (Y z θ) ^ 2)) := by
        show (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            * (|G z θ| * |Y z θ|)
          ≤ (1 / 2) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
                * (G z θ) ^ 2
              + (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
                * (Y z θ) ^ 2)
        refine le_trans (mul_le_mul_of_nonneg_left hGYabs
          (mul_nonneg hw (Real.rpow_nonneg hσ0.le _))) ?_
        rw [show (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * ((G z θ ^ 2 + Y z θ ^ 2) / 2)
            = (1 / 2) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
                * (G z θ) ^ 2
              + (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
                * (Y z θ) ^ 2) from by ring]
      have h3' : canonW Work.Spaces.eta z θ * (Y z θ) ^ 2
          ≤ canonW (Work.Spaces.gam α) z θ * (Y z θ) ^ 2 := by
        have hle : Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            ≤ Real.sin (2 * θ) ^ (-Work.Spaces.gam α) :=
          rpow_neg_le_neg hσ0 hσ1 hηγ
        rw [canonW, canonW]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle hw) (sq_nonneg _)
      exact le_trans (le_trans hstep1 hstep2) (by linarith [hGsq, le_trans h3' hYsq])
    calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|
        = |Work.Spaces.mixed b1 a1 f z θ| * (canonW q z θ * |G z θ| * |Y z θ|) := by ring
      _ ≤ (CK * Real.sin (2 * θ)) * (canonW q z θ * |G z θ| * |Y z θ|) :=
          mul_le_mul_of_nonneg_right (hFb z θ hz hθ.1 hθ.2) hGnn
      _ = CK * (Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)) := by ring
      _ ≤ CK * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hGY hCK
  -- the angular monotonicity
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, CK * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ ((hmemg.1 z hz).const_mul CK) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
      exact mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
        (abs_nonneg _)) (abs_nonneg _)
    · rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | hz0
      · subst h0
        filter_upwards with θ
        rw [canonW_zero, zero_mul, zero_mul, zero_mul]
        exact mul_nonneg hCK (Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
      · exact ae_of_forall_Ioo (fun θ hθ => hpt z hz0 θ hθ)
  -- the radial monotonicity
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, CK * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 g z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmemg.2.const_mul CK) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => ?_)
      exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
        mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
          (abs_nonneg _)) (abs_nonneg _))
    · refine ae_of_forall_Ioi (fun z hz => ?_)
      show (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
        ≤ CK * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ
      rw [← MeasureTheory.integral_const_mul]
      exact hslice z hz.le
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed b1 a1 f z θ| * |G z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, CK * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 g z θ := houter
    _ = CK * Work.Spaces.HkSq α 4 g := by
        rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]


/-! ## The top-slot bound (the radial integration by parts) -/

/-- Multiplication of a `SmoothOpen` function by a power of `sin(2θ)` keeps it `SmoothOpen`
(on the open quadrant the base is positive). -/
theorem smoothOpen_mul_rpow_sin {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (d : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin (2 * θ) ^ d * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => Real.sin (2 * θ) ^ d * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => Real.sin (2 * θ) ^ d * f z θ)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ d * f p.1 p.2 from rfl]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ d) Work.FTS.EllipticEst.Q0 := by
    have htwo : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (2:ℝ) * p.2)
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2:ℝ))).mul
        (contDiffOn_snd (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0))
    refine (htwo.sin).rpow_const_of_ne ?_
    intro p hp
    have hp2 : 0 < p.2 := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2; linarith [Real.pi_pos]))
  exact h1.mul hf

/-- `D_z` of a product with a `θ`-only factor. -/
theorem Dz_mul_sin {f : ℝ → ℝ → ℝ} (d : ℝ) (z θ : ℝ) :
    Work.Spaces.Dz (fun z θ => Real.sin (2 * θ) ^ d * f z θ) z θ
      = Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
  ring

/-- **The top-slot bound.**  For a slot `(a, 4-a)` (`a ≤ 4`) and the weight
`canonW q = w² sin(2θ)^{-q}` with `q ≤ γ` (and `q ≤ η` when `a = 0`), the pairing of the
order-five derivative with the order-four slot is bounded by `2 Mf HkSq α 4 g` whenever `Mf`
dominates `|f|` and `|D_z f|` on the open quadrant and the boundary traces of the slot vanish.
The proof reduces the weight `σ^{-q}` to the canonical hard weight `sghard α a` by multiplying
`f` by a power of `σ` (amended at the degenerate points `z = 0`, `θ ∈ {0, π/2}`, which are
null and irrelevant) and then applies the per-slot radial integration by parts
`T3BadAux.slot_prod_le`. -/
theorem topSlotBound {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (a : ℕ) (ha : a ≤ 4) (q : ℝ)
    (hMf : 0 ≤ Mf)
    (hqη : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.mixed (4 - a) a g z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.Spaces.mixed (4 - a) a g z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ|
      ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  have ha5 : a < 5 := by omega
  -- the canonical hard exponent and the multiplier
  obtain ⟨qbig, hqbig0, hqbig, hqq⟩ : ∃ qbig : ℝ,
      (a = 0 → qbig = Work.Spaces.eta) ∧ (a ≠ 0 → qbig = Work.Spaces.gam α) ∧ q ≤ qbig := by
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      exact ⟨Work.Spaces.eta, fun _ => rfl, fun h => absurd rfl h, hqη rfl⟩
    · exact ⟨Work.Spaces.gam α, fun h => absurd h h0, fun _ => rfl, hqγ⟩
  set d : ℝ := qbig - q with hd
  have hdnn : 0 ≤ d := by rw [hd]; linarith
  -- the amended multiplier: `σ^d f`, with the degenerate points set to `0`
  set fq : ℝ → ℝ → ℝ := fun z θ =>
    if z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2 then 0 else Real.sin (2 * θ) ^ d * f z θ with hfqdef
  -- the open-quadrant bound for the unamended multiplier
  have hfq_open : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Real.sin (2 * θ) ^ d * f z θ| ≤ Mf := by
    intro z θ hz hθ hθ2
    have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
    have hσ1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
    have hpow : Real.sin (2 * θ) ^ d ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hdnn
    calc |Real.sin (2 * θ) ^ d * f z θ|
        = Real.sin (2 * θ) ^ d * |f z θ| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ0.le _)]
      _ ≤ 1 * Mf := mul_le_mul hpow (hf z θ hz hθ hθ2) (abs_nonneg _) (by norm_num)
      _ = Mf := one_mul Mf
  have hDfq_open : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.Dz (fun z θ => Real.sin (2 * θ) ^ d * f z θ) z θ| ≤ Mf := by
    intro z θ hz hθ hθ2
    have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
    have hσ1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
    have hpow : Real.sin (2 * θ) ^ d ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hdnn
    rw [Dz_mul_sin]
    calc |Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ|
        = Real.sin (2 * θ) ^ d * |Work.Spaces.Dz f z θ| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ0.le _)]
      _ ≤ 1 * Mf := mul_le_mul hpow (hDf z θ hz hθ hθ2) (abs_nonneg _) (by norm_num)
      _ = Mf := one_mul Mf
  -- the two closed-domain bounds for the amended multiplier
  have hfq : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |fq z θ| ≤ Mf := by
    intro z hz θ hθ
    by_cases hbad : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2
    · simp only [hfqdef, if_pos hbad]
      simpa using hMf
    · simp only [hfqdef, if_neg hbad]
      simp only [not_or, not_not] at hbad
      obtain ⟨hz0, hθ0, hθ2⟩ := hbad
      have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
      have hθlt : θ < π / 2 := lt_of_le_of_ne hθ.2 hθ2
      exact hfq_open z θ hzpos hθpos hθlt
  have hDfq : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz fq z θ| ≤ Mf := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      rw [Work.Spaces.Dz, Work.Spaces.pz]
      simp only [zero_mul, abs_zero]
      exact hMf
    · by_cases hbad : θ = 0 ∨ θ = Real.pi / 2
      · have hzero : ∀ z' : ℝ, fq z' θ = 0 := by
          intro z'
          simp only [hfqdef, if_pos (Or.inr hbad)]
        have hev : (fun z' => fq z' θ) =ᶠ[𝓝 z] fun _ => (0:ℝ) :=
          Filter.Eventually.of_forall hzero
        rw [Work.Spaces.Dz, Work.Spaces.pz, hev.deriv_eq, deriv_const]
        simp only [mul_zero, abs_zero]
        exact hMf
      · have hθI : θ ∈ Set.Ioo (0:ℝ) (π/2) := by
          simp only [not_or, not_not] at hbad
          exact ⟨lt_of_le_of_ne hθ.1 (Ne.symm hbad.1), lt_of_le_of_ne hθ.2 hbad.2⟩
        have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθI
        have hσ1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
        have hpow : Real.sin (2 * θ) ^ d ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hdnn
        have hev : (fun z' => fq z' θ) =ᶠ[𝓝 z]
            (fun z' => Real.sin (2 * θ) ^ d * f z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          have hnot : ¬ (z' = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) := by
            rintro (h | h | h)
            · exact absurd h (ne_of_gt hz')
            · exact absurd h hθI.1.ne'
            · exact absurd h hθI.2.ne
          simp only [hfqdef, if_neg hnot]
        have hDzeq : Work.Spaces.Dz fq z θ
            = Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ := by
          rw [Work.Spaces.Dz, Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pz, hev.deriv_eq,
            deriv_const_mul_field]
          ring
        rw [hDzeq]
        calc |Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ|
            = Real.sin (2 * θ) ^ d * |Work.Spaces.Dz f z θ| := by
              rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ0.le _)]
          _ ≤ 1 * Mf := mul_le_mul hpow (hDf z θ hzpos hθI.1 hθI.2) (abs_nonneg _)
              (by norm_num)
          _ = Mf := one_mul Mf
  have hsmfq : Work.FTS.EllipticEst.SmoothOpen fq := by
    refine (smoothOpen_mul_rpow_sin hsmf d).congr ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hnot : ¬ (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) := by
      rintro (h | h | h)
      · exact absurd h (ne_of_gt hz)
      · exact absurd h (ne_of_gt hθ0)
      · exact absurd h (ne_of_lt hθ1)
    dsimp only [Function.uncurry]
    simp only [hfqdef, if_neg hnot]
  -- the `Thard`-slot is the `(4-a,a)` mixed derivative
  have hTh : Work.FTS.H2.Thard g ⟨a, ha5⟩ = fun z θ => Work.Spaces.mixed (4 - a) a g z θ :=
    Work.FTS.H2.Thard_eq_mixed g ⟨a, ha5⟩
  have hsgh : ∀ θ, Work.FTS.H2.sghard α ⟨a, ha5⟩ θ = Real.sin (2 * θ) ^ (-qbig) := by
    intro θ
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      have hk : (⟨0, ha5⟩ : Fin 5) = 0 := Fin.ext rfl
      rw [hk, Work.FTS.H2.sghard_apply_zero, hqbig0 rfl]
    · rw [Work.FTS.H2.sghard_apply_ne α _ (by simpa using h0), hqbig h0]
  -- the pointwise identity with `gK`
  have hkey : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) p.1 p.2
        * Work.Spaces.mixed (4 - a) a g p.1 p.2) p
      = Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ hθ2 => ?_)
    show canonW q z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ
      = Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ z θ
    have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
    have hfq_eq : fq z θ = Real.sin (2 * θ) ^ d * f z θ := by
      have hnot : ¬ (z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) := by
        rintro (h | h | h)
        · exact absurd h (ne_of_gt hz)
        · exact absurd h (ne_of_gt hθ)
        · exact absurd h (ne_of_lt hθ2)
      simp only [hfqdef, if_neg hnot]
    have hpow : Real.sin (2 * θ) ^ d * Real.sin (2 * θ) ^ (-qbig)
        = Real.sin (2 * θ) ^ (-q) := by
      rw [← Real.rpow_add hσ0, show d + (-qbig) = -q by rw [hd]; ring]
    have hmain : canonW q z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ
        = (Real.sin (2 * θ) ^ d * Real.sin (2 * θ) ^ (-qbig) * f z θ)
          * (Work.Spaces.w z ^ 2
            * (Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
              * Work.Spaces.mixed (4 - a) a g z θ)) := by
      rw [canonW, hpow]; ring
    rw [hmain, Work.FTS.TransportS.gK, hfq_eq, hsgh, hTh, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  -- Fubini and the integration by parts
  have hint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.TransportS.integrable_gK hsmfq hsmg hm5 hMf
      (fun z θ hz hθ hθ2 => hfq z (le_of_lt hz) θ ⟨le_of_lt hθ, le_of_lt hθ2⟩)
      ⟨a, ha5⟩
  have hint' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hint
  have htrTh : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g ⟨a, ha5⟩ z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g ⟨a, ha5⟩ z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) := by
    intro θ hθ
    rw [hTh]
    exact htr θ hθ
  have hibp := Work.FTS.TransportS.T3BadAux.slot_prod_le (α := α) (Mf := Mf)
    ⟨a, ha5⟩ hMf hsmfq hsmg hm4 hm5 hfq hDfq htrTh
  -- the `Xz`-energy
  have hXz : (∫ p, (Work.FTS.TransportS.Xz α g ⟨a, ha5⟩ p.1 p.2) ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≤ Work.Spaces.HkSq α 4 g := by
    have hInt := (Work.FTS.TransportS.integrable_HkIntegrand_prod hsmg hm4)
    calc (∫ p, (Work.FTS.TransportS.Xz α g ⟨a, ha5⟩ p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ ∫ p, Work.Spaces.HkIntegrand α 4 g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_mono
            (Work.FTS.TransportS.integrable_Xz_sq hsmg hm4 ⟨a, ha5⟩) hInt.1
            (fun p => Work.FTS.TransportS.Xz_sq_le_HkIntegrand4 α g ⟨a, ha5⟩ p.1 p.2)
      _ = Work.Spaces.HkSq α 4 g := hInt.2
  -- conclude
  have hIntLHS : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint'.congr (hkey.mono (fun p hp => hp.symm))
  have hEq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ)
      = ∫ p, Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integral_integral hIntLHS]
    exact MeasureTheory.integral_congr_ae hkey
  rw [hEq]
  calc |∫ p, Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g ⟨a, ha5⟩ p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hibp
    _ ≤ 2 * Mf * Work.Spaces.HkSq α 4 g :=
        mul_le_mul_of_nonneg_left hXz (by linarith)

end Work.FTS.TransportS.T2Sup
