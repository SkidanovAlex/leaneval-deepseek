import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.pd_aux.abs_boxMean_le
import Submission.Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean
import Submission.Work.UBBInputs9.B.pd_aux.kinIntD_le_indicator
import Submission.Work.UBBInputs9.B.pd_aux.kinInt_le_indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.integrable_kinIntPrj`

**The projected (mean-free) sliding Dirichlet integrand is `L¹`.**  For `ℓ, d > 0` and a smooth
state `Φ` of compact support on `X 1`,

    `p = (u,x) ↦ kinIntPrj ℓ d Φ u x  =  Σ_k (∂_k (χ_{B(u)}·Q_{B(u)}Φ)(x))²`

is `Integrable` for `pdMu ℓ = volume_u ⊗ (volume_x ↾ abox 1 ℓ)`.  This is the `L¹`-input which
turns the sliding projected Dirichlet word into a genuine Bochner integral (it is the
mean-free analogue of `B/integrable_fderiv_chiBPhi_sq`, and the missing `sorry` of
`pd_aux/RHS_eq_prod`).

## Proof

Write `c_u = boxMean ℓ d u Φ`, so that `boxQ (boxMass ℓ d u) (dlBox ℓ d u) 0 Φ = Φ - c_u`
(`boxQ_eq_boxMean`).  Two independent facts are used.

* **Measurability.**  `proj_decomp` provides the pointwise Leibniz decomposition

      `kinIntPrj ℓ d Φ u x
         = Σ_k (chiBLc ℓ d Φ k (u,x) - c_u · chiBLb ℓ d k (u,x))²`,

  where `chiBLc`, `chiBLb` are the explicit (continuous!) Leibniz expressions for
  `∂_k(χ_B·Φ)` and `∂_kχ_B`; and `u ↦ c_u` is measurable (`aemeasurable_boxMean`).  Hence the
  integrand is a.e. strongly measurable as a finite sum of squares of products of measurable
  functions.

* **A.e. domination.**  Off the ball `‖u‖ > R` the window factor `chiScale (ℓd)(x₀ - (ℓd)u)`
  and its derivative both vanish on `abox 1 ℓ`, so the integrand is `0` there; on the ball it is
  bounded.  Concretely `kinIntPrj ≤ 2·kinInt + 2·c_u²·kinIntD` (`kinIntPrj_le_bound`), `|c_u| ≤ MΦ`
  (`abs_boxMean_le`), and `kinInt`, `kinIntD` are bounded by constants times the indicator of a
  fixed closed ball (`kinInt_le_indicator`, `kinIntD_le_indicator`).  The dominating function is
  integrable on `pdMu ℓ` because `volume ↾ abox 1 ℓ` is a finite measure.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The a.e. statements -/

/-- Almost every point of `pdMu ℓ` has its second coordinate in `abox 1 ℓ`. -/
lemma ae_mem_abox_pdMu (ℓ : ℝ) :
    ∀ᵐ p ∂(Work.UBBInputs9.B.pdMu ℓ), p.2 ∈ Submission.BoseGases.abox 1 ℓ := by
  have hs : MeasurableSet (Submission.BoseGases.abox 1 ℓ) :=
    Submission.BoseGases.abox_measurable 1 ℓ
  have h1 : ∀ᵐ x ∂((volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ)),
      x ∈ Submission.BoseGases.abox 1 ℓ := ae_restrict_mem hs
  exact (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ³))
    (ν := (volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ))).ae h1

/-- `kinIntPrj` is a sum of squares, hence nonnegative. -/
lemma kinIntPrj_nonneg (ℓ d : ℝ) (Φ : X1 → ℝ) (u : ℝ³) (x : X1) :
    0 ≤ Work.UBBInputs9.B.kinIntPrj ℓ d Φ u x := by
  unfold Work.UBBInputs9.B.kinIntPrj
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

/-- At fixed `u` the projected integrand is strongly measurable in `x`; the content here is the
joint (a.e.) strong measurability in `(u,x)`, obtained from the Leibniz decomposition of
`proj_decomp` and the measurability of the box mean in the centre `u`. -/
lemma aestronglyMeasurable_kinIntPrj {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    AEStronglyMeasurable (fun p : ℝ³ × X1 =>
      Work.UBBInputs9.B.kinIntPrj ℓ d Φ p.1 p.2) (Work.UBBInputs9.B.pdMu ℓ) := by
  have hcm : AEMeasurable (fun p : ℝ³ × X1 => boxMean ℓ d p.1 Φ)
      (Work.UBBInputs9.B.pdMu ℓ) :=
    (aemeasurable_boxMean hℓ hΦ.continuous).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³))
        (ν := (volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ)))
  have hterm : ∀ k : Fin 3, AEStronglyMeasurable (fun p : ℝ³ × X1 =>
      (chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) ^ 2)
      (Work.UBBInputs9.B.pdMu ℓ) := by
    intro k
    exact (((continuous_chiBLc hℓ hd Φ hΦ k).aestronglyMeasurable).sub
      (hcm.aestronglyMeasurable.mul
        (continuous_chiBLb hℓ hd k).aestronglyMeasurable)).pow 2
  have hsum : AEStronglyMeasurable (fun p : ℝ³ × X1 => ∑ k : Fin 3,
      (chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) ^ 2)
      (Work.UBBInputs9.B.pdMu ℓ) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun k _ => hterm k)
    have h' : (∑ k ∈ Finset.univ, fun p : ℝ³ × X1 =>
        (chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) ^ 2)
        = (fun p : ℝ³ × X1 => ∑ k : Fin 3,
            (chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) ^ 2) := by
      funext p
      simp [Finset.sum_apply]
    rwa [h'] at h
  refine hsum.congr (Filter.Eventually.of_forall (fun p => ?_))
  obtain ⟨u, x⟩ := p
  exact (kinIntPrj_eq hℓ hd u hΦ x).symm

/-! ## The a.e. domination -/

/-- Monotonicity of the closed-ball indicator in the radius. -/
lemma indicator_closedBall_mono {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) (u : ℝ³) :
    (Metric.closedBall (0 : ℝ³) R₁).indicator (fun _ => (1 : ℝ)) u
      ≤ (Metric.closedBall (0 : ℝ³) R₂).indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) R₁
  · rw [Set.indicator_of_mem hu,
      Set.indicator_of_mem (Metric.closedBall_subset_closedBall h hu)]
  · rw [Set.indicator_of_notMem hu]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) u

/-- **Domination of `kinIntPrj`.**  There are `R, CH` with `CH ≥ 0` and
`kinIntPrj ℓ d Φ u x ≤ CH · 1_{‖u‖ ≤ R}` for all `x ∈ abox 1 ℓ` and all `u`. -/
lemma kinIntPrj_le_indicator' {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) :
    ∃ R CH : ℝ, 0 ≤ CH ∧ ∀ (u : ℝ³) (x : X1), x ∈ Submission.BoseGases.abox 1 ℓ →
      Work.UBBInputs9.B.kinIntPrj ℓ d Φ u x
        ≤ CH * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) u := by
  obtain ⟨MΦ, hMΦ⟩ := hcs.exists_bound_of_continuous hΦ.continuous
  have hΦb : ∀ x : X1, |Φ x| ≤ MΦ := fun x => by
    rw [← Real.norm_eq_abs]; exact hMΦ x
  obtain ⟨R₁, C₁, hC₁, h₁⟩ := kinInt_le_indicator hℓ hd hΦ hcs
  obtain ⟨R₂, C₂, hC₂, h₂⟩ := kinIntD_le_indicator hℓ hd
  refine ⟨max R₁ R₂, 2 * C₁ + 2 * MΦ ^ 2 * C₂, by positivity, ?_⟩
  intro u x hx
  have e₁ : Work.UBBInputs9.B.kinInt ℓ d Φ u x
      ≤ C₁ * (Metric.closedBall (0 : ℝ³) (max R₁ R₂)).indicator (fun _ => (1 : ℝ)) u :=
    le_trans (h₁ u x hx)
      (mul_le_mul_of_nonneg_left (indicator_closedBall_mono (le_max_left _ _) u) hC₁)
  have e₂ : Work.UBBInputs9.B.kinIntD ℓ d u x
      ≤ C₂ * (Metric.closedBall (0 : ℝ³) (max R₁ R₂)).indicator (fun _ => (1 : ℝ)) u :=
    le_trans (h₂ u x hx)
      (mul_le_mul_of_nonneg_left (indicator_closedBall_mono (le_max_right _ _) u) hC₂)
  calc Work.UBBInputs9.B.kinIntPrj ℓ d Φ u x
      ≤ 2 * Work.UBBInputs9.B.kinInt ℓ d Φ u x
          + 2 * MΦ ^ 2 * Work.UBBInputs9.B.kinIntD ℓ d u x :=
        kinIntPrj_le_bound hℓ hd hΦ (fun v => abs_boxMean_le hℓ hΦb v) u x
    _ ≤ 2 * (C₁ * (Metric.closedBall (0 : ℝ³) (max R₁ R₂)).indicator (fun _ => (1 : ℝ)) u)
          + 2 * MΦ ^ 2
            * (C₂ * (Metric.closedBall (0 : ℝ³) (max R₁ R₂)).indicator (fun _ => (1 : ℝ)) u) := by
        refine add_le_add (by linarith)
          (mul_le_mul_of_nonneg_left e₂ (by positivity))
    _ = (2 * C₁ + 2 * MΦ ^ 2 * C₂)
          * (Metric.closedBall (0 : ℝ³) (max R₁ R₂)).indicator (fun _ => (1 : ℝ)) u := by
        ring

/-! ## The target -/

theorem integrable_kinIntPrj {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 =>
        Work.UBBInputs9.B.kinIntPrj ℓ d Φ p.1 p.2)
      (Work.UBBInputs9.B.pdMu ℓ) := by
  classical
  obtain ⟨R, CH, hCH0, hb⟩ := kinIntPrj_le_indicator' hℓ hd hΦ hcs
  have hmeas := aestronglyMeasurable_kinIntPrj hℓ hd hΦ
  have hfin : IsFiniteMeasure ((volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume 1 ℓ hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  have hU : MeasureTheory.Integrable
      (fun u : ℝ³ => CH * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) u)
      (volume : Measure ℝ³) := by
    refine MeasureTheory.Integrable.const_mul ?_ CH
    rw [MeasureTheory.integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact MeasureTheory.integrableOn_const
      (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R)).ne
  have hOne : MeasureTheory.Integrable (fun _ : X1 => (1 : ℝ))
      ((volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ)) :=
    (MeasureTheory.integrable_const_iff
      (μ := (volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ))
      (c := (1 : ℝ))).mpr (Or.inr hfin)
  have hg : MeasureTheory.Integrable
      (fun p : ℝ³ × X1 =>
        CH * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.1)
      (Work.UBBInputs9.B.pdMu ℓ) := by
    have h := hU.mul_prod hOne
    simpa [Work.UBBInputs9.B.pdMu, mul_one] using h
  refine hg.mono' hmeas ?_
  filter_upwards [ae_mem_abox_pdMu ℓ] with p hp
  rw [Real.norm_of_nonneg (kinIntPrj_nonneg ℓ d Φ p.1 p.2)]
  exact hb p.1 p.2 hp

end Work.UBBInputs9.B.pd_aux
