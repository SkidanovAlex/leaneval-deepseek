/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the four Step-5 slice quantities

The lemma `sliceStep5Integrable` collects the four *integrability* statements that the
Step-5 slice estimate of Elgindi's elliptic section needs (they are the "honesty"
hypotheses of `sliceStep5Vg0`/`sliceStep5Vg1`/`sliceStep5Vv0`/`sliceStep5Vv1`):

* `(u/cos θ)² sin(2θ)^{2-γ}`,
* `(∂_θ(u/cos θ))² sin(2θ)^{4-γ}`,
* `(g)² sin(2θ)^{4-γ}`,
* `(g')² sin(2θ)^{2-γ}`,

for `1 ≤ γ ≤ 3/2`, `u ∈ C⁴((0,π/2))` continuous on `[0,π/2]` with `u 0 = u (π/2) = 0`,
`Lzero1 u = g`, and the six weighted `L²` integrability hypotheses of Step 5.

The first three follow from the already-proved pointwise/a-priori bounds
(`div_cos_sq_le_M`, `slice5_vweight_le`, `g_pointwise_ident`).  The fourth is the
delicate one: near `π/2` the pointwise expression of `g'` involves `tan θ`, so it is
handled on `[0, π/2 - 1/8]` by the pointwise bound and on `[π/2 - 1/8, π/2]` by the
weighted Hardy inequality `hardyNearPiHalf` together with the comparison
`(π/2-θ) ≤ sin 2θ ≤ 2(π/2-θ)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice5_rel
import Submission.Work.FTS.EllipticEst.remov.slice5_eqn_deriv2
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Local.slice5_vweight_le
import Submission.Work.FTS.EllipticEst.remov.slice5_reduce
import Submission.Work.FTS.EllipticEst.remov.g_pointwise_ident
import Submission.Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1
import Submission.Work.FTS.EllipticEst.remov.slice_ibp_w
import Submission.Work.FTS.EllipticEst.H2W.hardy_sinWeight
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vg0
import Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vv0
import Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vv1
import Submission.Work.FTS.EllipticEst.H2W.sliceStep5gDerivIdents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## Part 0. Elementary facts about `Iθ`, the weights, and the region split -/

private lemma Iθ_eq_icc : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl

private lemma Iθ_measurable : MeasurableSet Work.Spaces.Iθ := by
  rw [Iθ_eq_icc]; exact measurableSet_Icc

private lemma Iθ_volume_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Iθ_eq_icc, Real.volume_Icc]; exact ENNReal.ofReal_lt_top

/-- Almost every point of `Icc a b` lies in the open interval `Ioo a b`. -/
private lemma ae_mem_Ioo_of_Icc {a b : ℝ} :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Icc a b), θ ∈ Set.Ioo a b := by
  rw [Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A function continuous on the open interval is a.e.-strongly-measurable for the
restriction to the closed interval. -/
private lemma aesm_of_continuousOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (h : ContinuousOn f (Set.Ioo a b)) :
    AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  rw [Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b)).symm]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-- `∂` commutes with `ContDiffOn` on an open set. -/
private lemma contDiffOn_deriv_of_le_w {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    {n m : WithTop ℕ∞} (h : ContDiffOn ℝ n f s) (hm : m + 1 ≤ n) :
    ContDiffOn ℝ m (deriv f) s := by
  intro x hx
  exact (Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w
    (h.contDiffAt (hs.mem_nhds hx)) hm).contDiffWithinAt

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.remov.sin_two_nonneg_R hθ

private lemma sEta_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ

/-- `sin(2θ)^{2-γ} ≥ 0` on `Iθ`. -/
private lemma rpow_two_sub_gam_nonneg {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- `sin(2θ)^{2-γ} ≤ 1` on `Iθ` (because `2 - γ ≥ 0`). -/
private lemma rpow_two_sub_gam_le_one {γ θ : ℝ} (hγ2 : γ ≤ 3 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg_Iθ hθ) (Real.sin_le_one _) (by linarith)

/-- `sin(2θ)^{2-γ} ≤ sin(2θ)^{-η} = sEta θ` on `Iθ`. -/
private lemma rpow_two_sub_gam_le_sEta {γ θ : ℝ} (hγ2 : γ ≤ 3 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
  rcases eq_or_lt_of_le (sin_two_nonneg_Iθ hθ) with hz | hpos
  · have h1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) = 0 := by
      rw [← hz]; exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
    have h2 : Work.FTS.EllipticEst.sEta θ = 0 := by
      rw [Work.FTS.EllipticEst.sEta, ← hz]
      exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    rw [h1, h2]
  · refine Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) ?_
    rw [Work.Spaces.eta]; linarith

/-- The explicit expression for `∂_θ g` coming from `Lzero1 u = g`. -/
private def gE (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
    + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
    + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ

/-- **The comparison of the two weights** on `[π/2-1/8, π/2]`: with `δ = π/2 - θ`,
`sin 2θ = sin 2δ` and `δ ≤ sin 2δ ≤ 2δ` there. -/
private lemma sin_two_between_pi_half {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :
    Real.pi / 2 - θ ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
  set δ : ℝ := Real.pi / 2 - θ with hδ
  have hδ0 : 0 ≤ δ := by simp only [hδ]; linarith [hθ.2]
  have hδ8 : δ ≤ 1 / 8 := by simp only [hδ]; linarith [hθ.1]
  have hsin : Real.sin (2 * θ) = Real.sin (2 * δ) := by
    rw [hδ]
    have : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
    rw [this, Real.sin_pi_sub]
  rw [hsin]
  have h2δ0 : 0 ≤ 2 * δ := by linarith
  have h2δπ : 2 * δ ≤ Real.pi / 2 := by linarith [hδ8, Real.pi_gt_three]
  refine ⟨?_, Real.sin_le h2δ0⟩
  have h1 : 2 / Real.pi * (2 * δ) ≤ Real.sin (2 * δ) := Real.mul_le_sin h2δ0 h2δπ
  have h2 : δ ≤ 2 / Real.pi * (2 * δ) := by
    have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    have h5 : (1 : ℝ) * δ ≤ (4 / Real.pi) * δ := mul_le_mul_of_nonneg_right h4 hδ0
    calc δ = 1 * δ := by ring
      _ ≤ (4 / Real.pi) * δ := h5
      _ = 2 / Real.pi * (2 * δ) := by ring
  linarith

/-- On `[0, π/2-1/8]` we have `|tan θ| ≤ 8`. -/
private lemma abs_tan_le_eight {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 - 1 / 8)) :
    |Real.tan θ| ≤ 8 := by
  set x : ℝ := Real.pi / 2 - θ with hx
  have hx1 : (0 : ℝ) < x := by simp only [hx]; linarith [hθ.2]
  have hx2 : x < Real.pi / 2 := by simp only [hx]; linarith [hθ.1]
  have htanpos : 0 < Real.tan x := Real.tan_pos_of_pos_of_lt_pi_div_two hx1 hx2
  have htanx : x ≤ Real.tan x := Real.le_tan hx1.le hx2
  have hx18 : (1 / 8 : ℝ) ≤ x := by simp only [hx]; linarith [hθ.2]
  have hkey : Real.tan θ = (Real.tan x)⁻¹ := by
    have h := Real.tan_pi_div_two_sub x
    rwa [show Real.pi / 2 - x = θ by simp only [hx]; ring] at h
  have hbound : (Real.tan x)⁻¹ ≤ 8 := by
    have h := (inv_le_inv₀ htanpos (by norm_num : (0 : ℝ) < 1 / 8)).mpr
      (by linarith [htanx, hx18])
    simpa using h
  rw [hkey, abs_of_nonneg (inv_nonneg.mpr htanpos.le)]
  exact hbound

/-! ## Part 1. The four conjuncts, one by one -/

/-- **Conjunct 1**: `(u/cos θ)² sin(2θ)^{2-γ}` is integrable on `Iθ`.  Pointwise,
`(u/cos θ)² ≤ 100 ∫ (u'')² sEta` (`div_cos_sq_le_M`) and the weight is at most `1`. -/
private lemma sliceStep5_integrable_V0 (γ : ℝ) (hγ2 : γ ≤ 3 / 2) {u : ℝ → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hupi : u (Real.pi / 2) = 0)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := by
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact MeasureTheory.setIntegral_nonneg Iθ_measurable
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ' hθ))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    (MeasureTheory.AEStronglyMeasurable.div₀
        (huc.aestronglyMeasurable Iθ_measurable)
        (Real.continuous_cos.measurable.aestronglyMeasurable)).pow 2
      |>.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable)
  refine MeasureTheory.IntegrableOn.of_bound Iθ_volume_lt_top haesm (100 * M) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R] with θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 : (u θ / Real.cos θ) ^ 2 ≤ 100 * M := by
    have h := Work.FTS.EllipticEst.remov.div_cos_sq_le_M u hu2 huc hu0 hupi h2 θ hθ
    rwa [← hM] at h
  have hw1 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow_two_sub_gam_nonneg hθI
  have hwle : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := rpow_two_sub_gam_le_one hγ2 hθI
  have hnn : 0 ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    mul_nonneg (sq_nonneg _) hw1
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (100 * M) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
        mul_le_mul_of_nonneg_right h1 hw1
    _ ≤ (100 * M) * 1 := mul_le_mul_of_nonneg_left hwle (by linarith)
    _ = 100 * M := by ring

/-- **Conjunct 2**: `(∂_θ(u/cos θ))² sin(2θ)^{4-γ}` is integrable on `Iθ`
(the integrability component of `slice5_vweight_le`). -/
private lemma sliceStep5_integrable_V1 (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    {u : ℝ → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hupi : u (Real.pi / 2) = 0)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
  obtain ⟨_C, _hC, hv⟩ := Work.FTS.EllipticEst.remov.slice5_vweight_le γ hγ1 hγ2
  exact (hv u hu2 huc hu0 hupi h2 h1 h0).2.1

/-- The `v`-form of the pointwise identity for `g`: `g = -u'' + sin θ · v' - 5 cos θ · v`
with `v = u / cos θ`. -/
private lemma g_eq_v_form {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      g θ = -(deriv (deriv u) θ) + Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - 5 * Real.cos θ * (u θ / Real.cos θ) := by
  intro θ hθ
  have hgp := Work.FTS.EllipticEst.remov.g_pointwise_ident u g (hu.of_le (by norm_num))
    hode θ hθ
  have hv := Work.FTS.EllipticEst.remov.slice5_v_rel_one u hu θ hθ
  have hcos : Real.cos θ ≠ 0 := (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo hθ).ne'
  rw [hgp, hv]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **Conjunct 3**: `(g)² sin(2θ)^{4-γ}` is integrable on `Iθ`.  Pointwise,
`g = -u'' + (sin θ v' - 5 cos θ v)`, hence `g² ψ ≤ 2 (u'')² sEta + 4 (v')² ψ + 100 u²`
(the first by `ψ ≤ sEta`, the third because `cos θ · v = u` and `ψ ≤ 1`). -/
private lemma sliceStep5_integrable_G0 (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hv1 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
  have hgid := g_eq_v_form hu hode
  have hdom : MeasureTheory.IntegrableOn (fun θ => 2 * ((deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      + 100 * (u θ) ^ 2) Work.Spaces.Iθ :=
    ((h2.const_mul 2).add (hv1.const_mul 4)).add (h0.const_mul 100)
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · have hwcont : ContinuousOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn
    have hψc : ContinuousOn (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht => (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo ht).ne')
    have hψ2 : ContDiffOn ℝ 2 (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hu.of_le (by norm_num)).div Real.contDiff_cos.contDiffOn
        (fun t ht => (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo ht).ne')
    have hψ' : ContinuousOn (fun θ : ℝ => deriv (fun t => u t / Real.cos t) θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_deriv_of_le_w (m := 1) isOpen_Ioo hψ2 (by norm_num)).continuousOn
    have hu2c : ContinuousOn (fun θ : ℝ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) := by
      have h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
      have h2' : ContDiffOn ℝ 2 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
        contDiffOn_deriv_of_le_w (m := 2) isOpen_Ioo h3 (by norm_num)
      exact (contDiffOn_deriv_of_le_w (m := 1) isOpen_Ioo h2' (by norm_num)).continuousOn
    have hbase : ContinuousOn (fun θ : ℝ => -(deriv (deriv u) θ)
          + Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - 5 * Real.cos θ * (u θ / Real.cos θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hu2c.neg.add (Real.continuous_sin.continuousOn.mul hψ')).sub
        ((continuous_const.continuousOn.mul Real.continuous_cos.continuousOn).mul hψc)
    refine MeasureTheory.AEStronglyMeasurable.congr
      ((aesm_of_continuousOn_Ioo (hbase.pow 2)).mul (aesm_of_continuousOn_Ioo hwcont)) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R] with θ hθ
    show (-(deriv (deriv u) θ) + Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
      = (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
    rw [hgid θ hθ]
  · filter_upwards [Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hψnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
      Work.FTS.EllipticEst.remov.sig4_nonneg_R γ hθI
    have hψle1 : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 1 :=
      Real.rpow_le_one (sin_two_nonneg_Iθ hθI) (Real.sin_le_one _) (by linarith)
    have hψleEta : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ :=
      Work.FTS.EllipticEst.remov.sig4_le_sEta_R γ hγ1 hγ2 hθI
    have hS2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hCv : Real.cos θ * (u θ / Real.cos θ) = u θ :=
      Work.FTS.EllipticEst.remov.cos_mul_cbV hθ
    have hEta0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ' hθI
    set W : ℝ := Real.rpow (Real.sin (2 * θ)) (4 - γ) with hWdef
    have hWnn : 0 ≤ W := by rw [hWdef]; exact hψnn
    have hWleEta : W ≤ Work.FTS.EllipticEst.sEta θ := by rw [hWdef]; exact hψleEta
    have hWle1 : W ≤ 1 := by rw [hWdef]; exact hψle1
    have hA : (deriv (deriv u) θ) ^ 2 * W ≤ (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ :=
      mul_le_mul_of_nonneg_left hWleEta (sq_nonneg _)
    have hB : (Real.sin θ ^ 2 * (deriv (fun t => u t / Real.cos t) θ) ^ 2) * W
        ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 * W := by
      have hc : 0 ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 * W :=
        mul_nonneg (sq_nonneg _) hWnn
      have h := mul_le_mul_of_nonneg_right hS2 hc
      simpa [mul_assoc] using h
    have hC : (25 * (Real.cos θ * (u θ / Real.cos θ)) ^ 2) * W ≤ 25 * (u θ) ^ 2 := by
      rw [hCv]
      have h25 : 0 ≤ (25 : ℝ) * (u θ) ^ 2 := by positivity
      calc (25 * (u θ) ^ 2) * W ≤ (25 * (u θ) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hWle1 h25
        _ = 25 * (u θ) ^ 2 := by ring
    have hsq : (g θ) ^ 2 ≤ 2 * (deriv (deriv u) θ) ^ 2
        + 2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2 := by
      rw [hgid θ hθ]
      nlinarith [sq_nonneg (deriv (deriv u) θ
        + (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - 5 * Real.cos θ * (u θ / Real.cos θ)))]
    have hsq2 : (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2
        ≤ 2 * (Real.sin θ ^ 2 * (deriv (fun t => u t / Real.cos t) θ) ^ 2)
          + 2 * (25 * (Real.cos θ * (u θ / Real.cos θ)) ^ 2) := by
      nlinarith [sq_nonneg (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        + 5 * Real.cos θ * (u θ / Real.cos θ))]
    have h1 : (g θ) ^ 2 * W ≤ (2 * (deriv (deriv u) θ) ^ 2
          + 2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2) * W :=
      mul_le_mul_of_nonneg_right hsq hWnn
    have h2 : (2 * (deriv (deriv u) θ) ^ 2
          + 2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2) * W
        ≤ 2 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 * W)
          + 100 * (u θ) ^ 2 := by
      have hZ : (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2 * W
          ≤ (2 * (Real.sin θ ^ 2 * (deriv (fun t => u t / Real.cos t) θ) ^ 2)
            + 2 * (25 * (Real.cos θ * (u θ / Real.cos θ)) ^ 2)) * W :=
        mul_le_mul_of_nonneg_right hsq2 hWnn
      nlinarith [hA, hB, hC, hZ]
    have hfinal : (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ 2 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 100 * (u θ) ^ 2 := by
      rw [← hWdef]
      linarith [h1, h2]
    have hnn : 0 ≤ (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
      mul_nonneg (sq_nonneg _) hψnn
    have hnn2 : 0 ≤ 2 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 100 * (u θ) ^ 2 :=
      add_nonneg (add_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg _) hEta0))
        (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hψnn))) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg hnn2]
    exact hfinal

/-! ## Part 2. The fourth conjunct `(∂_θ g)² sin(2θ)^{2-γ}` -/

/-- `∂_θ g` equals the explicit `gE u` on `(0, π/2)`. -/
private lemma deriv_g_eq_gE {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ := by
  intro θ hθ
  have h := (sliceStep5gDerivIdents u g hu hode).2 θ hθ
  rw [h]
  rfl

/-- `Iθ` splits at `π/2 - 1/8`. -/
private lemma Icc_split_pi_half :
    Set.Icc (0 : ℝ) (Real.pi / 2 - 1 / 8) ∪ Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)
      = Set.Icc (0 : ℝ) (Real.pi / 2) := by
  ext x
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro (h | h) <;> exact ⟨by linarith [h.1, Real.pi_gt_three], by linarith [h.2]⟩
  · intro h
    by_cases hx : x ≤ Real.pi / 2 - 1 / 8
    · exact Or.inl ⟨h.1, hx⟩
    · exact Or.inr ⟨(not_le.mp hx).le, h.2⟩

/-- **The pointwise bound on `[0, π/2-1/8]`.**  There `|tan θ| ≤ 8`, so
`(g')² ≤ 4 ((u''')² + 64 (u'')² + 132² (u')² + 1040² u²)`; multiplying by the weight and
using `sin(2θ)^{2-γ} ≤ sEta`, `sin(2θ)^{2-γ} ≤ 1` gives the claim. -/
private lemma regionA_pointwise (γ : ℝ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 - 1 / 8)) :
    (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 132 ^ 2 * (deriv u θ) ^ 2
          + 1040 ^ 2 * (u θ) ^ 2) := by
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2]⟩
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hWnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow_two_sub_gam_nonneg hθIθ
  have hW1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := rpow_two_sub_gam_le_one hγ2 hθIθ
  have hWEta : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ Work.FTS.EllipticEst.sEta θ :=
    rpow_two_sub_gam_le_sEta hγ2 hθIθ
  have hEta0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ' hθIθ
  have hT8 : |Real.tan θ| ≤ 8 := abs_tan_le_eight hθ
  have hT2 : Real.tan θ ^ 2 ≤ 64 := by
    have h : |Real.tan θ| ^ 2 ≤ (8 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg (Real.tan θ), hT8]
    rwa [sq_abs, show (8 : ℝ) ^ 2 = 64 by norm_num] at h
  have hT4 : (2 * Real.tan θ ^ 2 - 4) ^ 2 ≤ 132 ^ 2 := by
    have h : |2 * Real.tan θ ^ 2 - 4| ≤ 132 := by
      refine abs_le.mpr ⟨by linarith [sq_nonneg (Real.tan θ)], by linarith⟩
    rw [← sq_abs (2 * Real.tan θ ^ 2 - 4)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hT6 : (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) ^ 2 ≤ 1040 ^ 2 := by
    have h : |2 * Real.tan θ ^ 3 + 2 * Real.tan θ| ≤ 1040 := by
      have h1 : |Real.tan θ ^ 3| ≤ 512 := by
        have h2 : |Real.tan θ| ^ 3 ≤ (8 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) hT8 3
        rw [abs_pow]
        have h3 : (8 : ℝ) ^ 3 = 512 := by norm_num
        linarith [h2, h3]
      calc |2 * Real.tan θ ^ 3 + 2 * Real.tan θ|
          ≤ |2 * Real.tan θ ^ 3| + |2 * Real.tan θ| := abs_add_le _ _
        _ = 2 * |Real.tan θ ^ 3| + 2 * |Real.tan θ| := by
            rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * 512 + 2 * 8 := by linarith
        _ = 1040 := by norm_num
    rw [← sq_abs (2 * Real.tan θ ^ 3 + 2 * Real.tan θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- the four-term square bound
  have hsq := Work.FTS.EllipticEst.remov.add_sq_le_four
    (-(deriv (deriv (deriv u)) θ)) (Real.tan θ * deriv (deriv u) θ)
    ((2 * Real.tan θ ^ 2 - 4) * deriv u θ)
    ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ)
  have hsq' : (-(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
      + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
      + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2
      ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 + (Real.tan θ * deriv (deriv u) θ) ^ 2
        + ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2
        + ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2) := by
    simpa only [neg_sq] using hsq
  rw [hg' θ hθI]
  simp only [gE]
  have hterm1 : (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) := le_rfl
  have hterm2 : (Real.tan θ * deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    have h1 : (Real.tan θ * deriv (deriv u) θ) ^ 2 ≤ 64 * (deriv (deriv u) θ) ^ 2 := by
      nlinarith [hT2, sq_nonneg (deriv (deriv u) θ)]
    calc (Real.tan θ * deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (64 * (deriv (deriv u) θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hWnn
      _ = 64 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ ≤ 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWEta (sq_nonneg _))
            (by norm_num)
  have hterm3 : ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 132 ^ 2 * (deriv u θ) ^ 2 := by
    have h1 : ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2
        ≤ 132 ^ 2 * (deriv u θ) ^ 2 := by
      nlinarith [hT4, sq_nonneg (deriv u θ)]
    calc ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (132 ^ 2 * (deriv u θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hWnn
      _ = 132 ^ 2 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ ≤ 132 ^ 2 * ((deriv u θ) ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW1 (sq_nonneg _))
            (by norm_num)
      _ = 132 ^ 2 * (deriv u θ) ^ 2 := by ring
  have hterm4 : ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1040 ^ 2 * (u θ) ^ 2 := by
    have h1 : ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2
        ≤ 1040 ^ 2 * (u θ) ^ 2 := by
      nlinarith [hT6, sq_nonneg (u θ)]
    calc ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (1040 ^ 2 * (u θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hWnn
      _ = 1040 ^ 2 * ((u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ ≤ 1040 ^ 2 * ((u θ) ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW1 (sq_nonneg _))
            (by norm_num)
      _ = 1040 ^ 2 * (u θ) ^ 2 := by ring
  have hsum : (-(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
        + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
        + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 + (Real.tan θ * deriv (deriv u) θ) ^ 2
        + ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2
        + ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2) *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    mul_le_mul_of_nonneg_right hsq' hWnn
  nlinarith [hsum, hterm1, hterm2, hterm3, hterm4, hWnn, hEta0]

/-- **Region A integrability**: on `[0, π/2-1/8]` the fourth integrand is dominated by
`4 ((u''')² sin(2θ)^{2-γ} + 64 (u'')² sEta + 132² (u')² + 1040² u²)`. -/
private lemma regionA_integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ)
    (h3 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2 - 1 / 8) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hIntA : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    h3.mono_set hsub
  have hIntB : MeasureTheory.IntegrableOn (fun θ => 64 * ((deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (h2.mono_set hsub).const_mul 64
  have hIntC : MeasureTheory.IntegrableOn (fun θ => 132 ^ 2 * (deriv u θ) ^ 2)
      (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (h1.mono_set hsub).const_mul (132 ^ 2)
  have hIntD : MeasureTheory.IntegrableOn (fun θ => 1040 ^ 2 * (u θ) ^ 2)
      (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (h0.mono_set hsub).const_mul (1040 ^ 2)
  have hdom : MeasureTheory.IntegrableOn (fun θ => 4 *
      ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 132 ^ 2 * (deriv u θ) ^ 2
        + 1040 ^ 2 * (u θ) ^ 2)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (((hIntA.add hIntB).add hIntC).add hIntD).const_mul 4
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · exact (((measurable_deriv g).pow_const 2).aestronglyMeasurable).mul
      (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable)
  · filter_upwards [ae_mem_Ioo_of_Icc (a := (0 : ℝ)) (b := Real.pi / 2 - 1 / 8)]
      with θ hθ
    have hpt := regionA_pointwise γ hγ2 hg' hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ :=
      ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le
    have hnn : 0 ≤ (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)
    have hnn2 : 0 ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 132 ^ 2 * (deriv u θ) ^ 2
        + 1040 ^ 2 * (u θ) ^ 2) := by
      refine mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_)
      · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)
      · exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ' hθIθ))
      · positivity
      · positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg hnn2]
    exact hpt

/-- **Differentiability of `∂_θ g`** on the region near `π/2`, through the explicit
expression `gE u` (which is `C¹` there because `u ∈ C⁴`). -/
private lemma hasDerivAt_deriv_g {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ) :
    ∀ θ ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
      HasDerivAt (deriv g) (deriv (deriv g) θ) θ := by
  intro θ hθ
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩
  have hcos : Real.cos θ ≠ 0 := (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo hθI).ne'
  have h4 : ContDiffAt ℝ 4 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθI)
  have hu3 : ContDiffAt ℝ 3 (deriv u) θ :=
    Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w (m := 3) h4 (by norm_num)
  have hu2 : ContDiffAt ℝ 2 (deriv (deriv u)) θ :=
    Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w (m := 2) hu3 (by norm_num)
  have hu1 : ContDiffAt ℝ 1 (deriv (deriv (deriv u))) θ :=
    Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w (m := 1) hu2 (by norm_num)
  have hA : DifferentiableAt ℝ (fun t => deriv (deriv (deriv u)) t) θ :=
    hu1.differentiableAt (by norm_num)
  have hB : DifferentiableAt ℝ (fun t => deriv (deriv u) t) θ :=
    hu2.differentiableAt (by norm_num)
  have hC : DifferentiableAt ℝ (fun t => deriv u t) θ :=
    hu3.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ u θ := h4.differentiableAt (by norm_num)
  have hT : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hdE : DifferentiableAt ℝ (gE u) θ := by
    show DifferentiableAt ℝ (fun t => -deriv (deriv (deriv u)) t
      + Real.tan t * deriv (deriv u) t + (2 * Real.tan t ^ 2 - 4) * deriv u t
      + (2 * Real.tan t ^ 3 + 2 * Real.tan t) * u t) θ
    exact (((hA.neg).add (hT.mul hB)).add ((((hT.pow 2).const_mul 2).sub
      (differentiableAt_const 4)).mul hC)).add
      ((((hT.pow 3).const_mul 2).add (hT.const_mul 2)).mul hD)
  have hEv : deriv g =ᶠ[𝓝 θ] gE u := by
    filter_upwards [isOpen_Ioo.mem_nhds hθI] with t ht
    exact hg' t ht
  exact ((hEv.differentiableAt_iff).mpr hdE).hasDerivAt

/-- Weighted AM–GM: `2|ab| d^{p+1} ≤ a² d^p + b² d^{p+2}` for `d > 0`. -/
private lemma amgm_weighted {p d a b : ℝ} (hd : 0 < d) :
    2 * (|a * b| * d ^ (p + 1)) ≤ a ^ 2 * d ^ p + b ^ 2 * d ^ (p + 2) := by
  have h1 : d ^ (p + 1) = d ^ (p / 2) * d ^ (p / 2 + 1) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have h2 : (|a| * d ^ (p / 2)) ^ 2 = a ^ 2 * d ^ p := by
    rw [mul_pow, sq_abs, sq, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hd)]
    congr 1; ring
  have h3 : (|b| * d ^ (p / 2 + 1)) ^ 2 = b ^ 2 * d ^ (p + 2) := by
    rw [mul_pow, sq_abs, sq, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hd)]
    congr 1; ring
  have h4 : 2 * (|a * b| * d ^ (p + 1))
      = 2 * (|a| * d ^ (p / 2)) * (|b| * d ^ (p / 2 + 1)) := by
    rw [h1, abs_mul]; ring
  have h5 : 2 * (|a| * d ^ (p / 2)) * (|b| * d ^ (p / 2 + 1))
      ≤ (|a| * d ^ (p / 2)) ^ 2 + (|b| * d ^ (p / 2 + 1)) ^ 2 := by
    nlinarith [sq_nonneg (|a| * d ^ (p / 2) - |b| * d ^ (p / 2 + 1))]
  rw [h2, h3, ← h4] at h5
  exact h5

/-- **Weighted Hardy inequality near `π/2`** (form used for conjunct 4).  For `α > 0`,
`f` continuous on `(π/2-ε, π/2)` with continuous derivative `f'` there and
`f'²(π/2-θ)^{α+2}` integrable,

  `∫_{π/2-ε}^{π/2} f²(π/2-θ)^α ≤ (1/α)(∫ f'²(π/2-θ)^{α+2} + ε^{α+1} f(π/2-ε)²)`.

The proof integrates `(f²(π/2-θ)^{α+1})' = 2ff'(π/2-θ)^{α+1} - (α+1)f²(π/2-θ)^α` over
`[c,t]` (`c = π/2-ε`, `t < π/2`), drops the nonnegative boundary term at `t` and uses
`2|ff'|(π/2-θ)^{α+1} ≤ f²(π/2-θ)^α + f'²(π/2-θ)^{α+2}`; the passage from the truncated
intervals to the whole one is done with the `AECover` machinery. -/
private lemma hardy_local {α : ℝ} (hα : 0 < α) {f f' : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hfcont : ContinuousOn f (Set.Ico (Real.pi / 2 - ε) (Real.pi / 2)))
    (hf'cont : ContinuousOn f' (Set.Ico (Real.pi / 2 - ε) (Real.pi / 2)))
    (hderiv : ∀ θ ∈ Set.Ico (Real.pi / 2 - ε) (Real.pi / 2), HasDerivAt f (f' θ) θ)
    (hint : MeasureTheory.IntegrableOn (fun θ => f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))
      (Set.Icc (Real.pi / 2 - ε) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.pi / 2 - θ) ^ α)
        (Set.Icc (Real.pi / 2 - ε) (Real.pi / 2)) ∧
      (∫ θ in (Real.pi / 2 - ε)..(Real.pi / 2), f θ ^ 2 * (Real.pi / 2 - θ) ^ α)
        ≤ 1 / α * ((∫ θ in (Real.pi / 2 - ε)..(Real.pi / 2),
              f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))
          + ε ^ (α + 1) * (f (Real.pi / 2 - ε)) ^ 2) := by
  set c : ℝ := Real.pi / 2 - ε with hcdef
  have hcle : c ≤ Real.pi / 2 := by simp only [hcdef]; linarith
  have hclt : c < Real.pi / 2 := by simp only [hcdef]; linarith
  have hcε : Real.pi / 2 - c = ε := by simp only [hcdef]; ring
  set u : ℝ → ℝ := fun θ => f θ ^ 2 * (Real.pi / 2 - θ) ^ α with hudef
  set B : ℝ := ∫ θ in c..Real.pi / 2, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2) with hBdef
  set K : ℝ := 1 / α * (B + ε ^ (α + 1) * (f c) ^ 2) with hKdef
  have hwIoc : MeasureTheory.IntegrableOn
      (fun θ => f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) (Set.Ioc c (Real.pi / 2)) :=
    hint.mono_set (fun x hx => ⟨hx.1.le, hx.2⟩)
  -- ### the truncated bound
  have htrunc : ∀ t ∈ Set.Ico c (Real.pi / 2), ∫ θ in c..t, u θ ≤ K := by
    intro t ht
    have hct : c ≤ t := ht.1
    have htlt : t < Real.pi / 2 := ht.2
    have hUI : Set.uIcc c t = Set.Icc c t := Set.uIcc_of_le hct
    have mkInt : ∀ (g : ℝ → ℝ), ContinuousOn g (Set.Icc c t) →
        IntervalIntegrable g volume c t :=
      fun g hg => (hUI.symm ▸ hg).intervalIntegrable
    have hsub : Set.Icc c t ⊆ Set.Ico c (Real.pi / 2) := fun x hx =>
      ⟨hx.1, lt_of_le_of_lt hx.2 htlt⟩
    have hdt : ∀ θ ∈ Set.Icc c t, 0 < Real.pi / 2 - θ := fun θ hθ => by linarith [hθ.2, htlt]
    have hpow : ∀ β : ℝ, ContinuousOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ β) (Set.Icc c t) := by
      intro β
      exact (continuous_const.sub continuous_id).continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hdt x hx)))
    have hucont : ContinuousOn u (Set.Icc c t) := by
      rw [hudef]
      exact ((hfcont.mono hsub).pow 2).mul (hpow α)
    have hH'cont : ContinuousOn (fun θ : ℝ => 2 * (f θ * f' θ) * (Real.pi / 2 - θ) ^ (α + 1)
        - (α + 1) * (f θ ^ 2 * (Real.pi / 2 - θ) ^ α)) (Set.Icc c t) :=
      ((((hfcont.mono hsub).mul (hf'cont.mono hsub)).const_mul 2).mul (hpow (α + 1))).sub
        ((((hfcont.mono hsub).pow 2).mul (hpow α)).const_mul (α + 1))
    have hHderiv : ∀ x ∈ Set.uIcc c t,
        HasDerivAt (fun θ : ℝ => f θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 1))
          (2 * (f x * f' x) * (Real.pi / 2 - x) ^ (α + 1)
            - (α + 1) * (f x ^ 2 * (Real.pi / 2 - x) ^ α)) x := by
      intro x hx
      rw [Set.uIcc_of_le hct] at hx
      have hxlt : x < Real.pi / 2 := lt_of_le_of_lt hx.2 htlt
      have hxa : HasDerivAt f (f' x) x := hderiv x ⟨hx.1, hxlt⟩
      have hd : Real.pi / 2 - x ≠ 0 := by linarith
      have hd2 : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
      have hprod := (hxa.pow 2).mul (hd2.rpow_const (p := α + 1) (Or.inl hd))
      convert hprod using 1
      · simp only [Pi.pow_apply]; ring_nf
    have hFTC : ∫ θ in c..t, (2 * (f θ * f' θ) * (Real.pi / 2 - θ) ^ (α + 1)
        - (α + 1) * (f θ ^ 2 * (Real.pi / 2 - θ) ^ α))
        = f t ^ 2 * (Real.pi / 2 - t) ^ (α + 1) - f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hHderiv (mkInt _ hH'cont)
    have hInt_ff' : IntervalIntegrable
        (fun θ : ℝ => f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)) volume c t :=
      mkInt _ (((hfcont.mono hsub).mul (hf'cont.mono hsub)).mul (hpow (α + 1)))
    have hInt_u : IntervalIntegrable u volume c t := mkInt _ hucont
    have hInt_w : IntervalIntegrable (fun θ : ℝ => f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))
        volume c t := mkInt _ (((hf'cont.mono hsub).pow 2).mul (hpow (α + 2)))
    have hsplit : (α + 1) * (∫ θ in c..t, u θ)
        = 2 * (∫ θ in c..t, f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1))
          + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1)
          - f t ^ 2 * (Real.pi / 2 - t) ^ (α + 1) := by
      have hcongr : ∫ θ in c..t, (2 * (f θ * f' θ) * (Real.pi / 2 - θ) ^ (α + 1)
            - (α + 1) * (f θ ^ 2 * (Real.pi / 2 - θ) ^ α))
          = ∫ θ in c..t, (2 * (f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1))
            - (α + 1) * u θ) :=
        intervalIntegral.integral_congr fun θ _ => by rw [hudef]; ring
      rw [hcongr, intervalIntegral.integral_sub (hInt_ff'.const_mul 2)
          (hInt_u.const_mul (α + 1)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
      linarith [hFTC]
    have hHt0 : 0 ≤ f t ^ 2 * (Real.pi / 2 - t) ^ (α + 1) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)
    have hamgm : ∫ θ in c..t, |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
        ≤ (1 / 2) * ((∫ θ in c..t, u θ)
            + ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) := by
      have h2 : IntervalIntegrable
          (fun θ : ℝ => (1 / 2) * (u θ + f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))) volume c t :=
        ((hInt_u.add hInt_w).const_mul (1 / 2))
      have hpt : ∀ θ ∈ Set.Icc c t,
          |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
            ≤ (1 / 2) * (u θ + f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) := by
        intro θ hθ
        have hd0 : 0 < Real.pi / 2 - θ := hdt θ hθ
        have hagg := amgm_weighted (p := α) hd0 (a := f θ) (b := f' θ)
        have h3 : |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
            = |f θ * f' θ| * (Real.pi / 2 - θ) ^ (α + 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hd0.le _)]
        rw [h3, hudef]
        linarith [hagg]
      have h1 : ∫ θ in c..t, |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
          ≤ ∫ θ in c..t, (1 / 2) * (u θ + f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) :=
        intervalIntegral.integral_mono_on hct
          (mkInt _ ((((hfcont.mono hsub).mul (hf'cont.mono hsub)).mul (hpow (α + 1))).abs))
          h2 hpt
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hInt_u hInt_w] at h1
      linarith [h1]
    have hmain : (α + 1) * (∫ θ in c..t, u θ)
        ≤ 2 * ((1 / 2) * ((∫ θ in c..t, u θ)
            + ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)))
          + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) := by
      have habs : IntervalIntegrable
          (fun θ : ℝ => |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|) volume c t :=
        mkInt _ ((((hfcont.mono hsub).mul (hf'cont.mono hsub)).mul (hpow (α + 1))).abs)
      have h1 : ∫ θ in c..t, f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)
          ≤ ∫ θ in c..t, |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)| :=
        intervalIntegral.integral_mono_on hct hInt_ff' habs (fun θ _ => le_abs_self _)
      linarith [hsplit, h1, hamgm, hHt0]
    have hwle : ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2) ≤ B := by
      rw [hBdef, intervalIntegral.integral_of_le hcle, intervalIntegral.integral_of_le hct]
      refine setIntegral_mono_set hwIoc ?_ ?_
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun θ hθ => ?_
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
      · exact Eventually.of_forall fun θ hθ =>
          ⟨hθ.1, le_trans hθ.2 (le_of_lt htlt)⟩
    have hcd : f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) = ε ^ (α + 1) * f c ^ 2 := by
      rw [hcε]; ring
    have hAc : ∫ θ in c..t, u θ ≤ 1 / α * (B + ε ^ (α + 1) * f c ^ 2) := by
      have hAc' : ∫ θ in c..t, u θ
          ≤ 1 / α * (B + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1)) := by
        have hbal : 2 * ((1 / 2) * ((∫ θ in c..t, u θ)
              + ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)))
            + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1)
            ≤ 2 * ((1 / 2) * ((∫ θ in c..t, u θ) + B))
              + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) := by
          linarith [hwle]
        have hfin : α * (∫ θ in c..t, u θ)
            ≤ B + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) := by linarith [hmain, hbal]
        rw [one_div, le_inv_mul_iff₀ hα]
        linarith [hfin]
      rw [hcd] at hAc'
      exact hAc'
    rw [hKdef, hBdef]
    exact hAc
  -- ### the AECover argument
  have hδtend : Tendsto (fun n : ℕ => Real.pi / 2 - ε / ((n : ℝ) + 1)) atTop (𝓝 (Real.pi / 2)) := by
    have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
    simpa using (tendsto_const_nhds (x := Real.pi / 2)).sub h1
  have hcover : AECover (volume.restrict (Set.Ioc c (Real.pi / 2))) atTop
      (fun n : ℕ => Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1))) :=
    aecover_Ioc_of_Ioc (μ := volume) (A := c) (B := Real.pi / 2) tendsto_const_nhds hδtend
  have hmem : ∀ n : ℕ, Real.pi / 2 - ε / ((n : ℝ) + 1) ∈ Set.Ico c (Real.pi / 2) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hpos : 0 < ε / ((n : ℝ) + 1) := div_pos hε hden
    have hle : ε / ((n : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ hden]; nlinarith
    refine ⟨?_, ?_⟩
    · simp only [hcdef]; linarith
    · linarith
  have hfi : ∀ n : ℕ, MeasureTheory.IntegrableOn u
      (Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)))
      (volume.restrict (Set.Ioc c (Real.pi / 2))) := by
    intro n
    have hbn : Real.pi / 2 - ε / ((n : ℝ) + 1) < Real.pi / 2 := (hmem n).2
    have hsub : Set.Icc c (Real.pi / 2 - ε / ((n : ℝ) + 1)) ⊆ Set.Ico c (Real.pi / 2) :=
      fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hbn⟩
    have hcu : ContinuousOn u (Set.Icc c (Real.pi / 2 - ε / ((n : ℝ) + 1))) := by
      rw [hudef]
      exact ((hfcont.mono hsub).pow 2).mul
        ((continuous_const.sub continuous_id).continuousOn.rpow_const
          (fun _ _ => Or.inr hα.le))
    have hI : MeasureTheory.IntegrableOn u (Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1))) volume :=
      (hcu.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    show Integrable u ((volume.restrict (Set.Ioc c (Real.pi / 2))).restrict
      (Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1))))
    have hsub2 : Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)) ⊆ Set.Ioc c (Real.pi / 2) :=
      fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hbn)⟩
    rw [Measure.restrict_restrict_of_subset hsub2]
    exact hI
  have hnng : 0 ≤ᵐ[volume.restrict (Set.Ioc c (Real.pi / 2))] u := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun θ hθ => ?_
    rw [hudef, Pi.zero_apply]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
  have hbounded : ∀ᶠ n : ℕ in atTop,
      (∫ x in Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)), u x
        ∂(volume.restrict (Set.Ioc c (Real.pi / 2)))) ≤ K := by
    filter_upwards with n
    have hbn : Real.pi / 2 - ε / ((n : ℝ) + 1) < Real.pi / 2 := (hmem n).2
    have hsub : Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)) ⊆ Set.Ioc c (Real.pi / 2) :=
      fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hbn)⟩
    rw [Measure.restrict_restrict_of_subset hsub]
    rw [← intervalIntegral.integral_of_le (hmem n).1]
    exact htrunc _ (hmem n)
  have hInt : Integrable u (volume.restrict (Set.Ioc c (Real.pi / 2))) :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae K hfi hnng hbounded
  have hle : ∫ x, u x ∂(volume.restrict (Set.Ioc c (Real.pi / 2))) ≤ K :=
    le_of_tendsto (hcover.integral_tendsto_of_countably_generated hInt) hbounded
  -- ### conclusion
  rw [hKdef, hBdef] at hle
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn u (Set.Ioc c (Real.pi / 2)) volume := hInt
    have h2 := MeasureTheory.IntegrableOn.congr_set_ae h1
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := c) (b := Real.pi / 2)).symm
    simpa only [hudef] using h2
  · rw [show c = Real.pi / 2 - ε from hcdef, intervalIntegral.integral_of_le hcle]
    exact hle

/-- **Region B integrability**: on `[π/2-1/8, π/2]` the fourth integrand is controlled by
the weighted Hardy inequality `hardy_local` applied to `∂_θ g`, together with
`sin 2θ ≤ 2 (π/2 - θ)` and `(π/2 - θ) ≤ sin 2θ`. -/
private lemma regionB_integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) := by
  have hμ : (2 : ℝ) - γ + 2 = 4 - γ := by ring
  -- integrability of `(g'')² (π/2-θ)^{4-γ}`, by comparison with `(g'')² sin(2θ)^{4-γ}`
  have hBregion : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :=
    hB.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2⟩)
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * (Real.pi / 2 - θ) ^ ((2 - γ) + 2))
      (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) := by
    rw [hμ]
    refine MeasureTheory.Integrable.mono hBregion ?_ ?_
    · exact (((measurable_deriv (deriv g)).pow_const 2).aestronglyMeasurable).mul
        (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
          (continuous_const.sub continuous_id).measurable)).aestronglyMeasurable
    · filter_upwards [ae_mem_Ioo_of_Icc (a := Real.pi / 2 - 1 / 8) (b := Real.pi / 2)]
        with θ hθ
      obtain ⟨hge, _hle⟩ := sin_two_between_pi_half ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hδ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have hpow : (Real.pi / 2 - θ) ^ (4 - γ) ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
        Real.rpow_le_rpow hδ0 hge (by linarith)
      have h1 : 0 ≤ (deriv (deriv g) θ) ^ 2 * (Real.pi / 2 - θ) ^ (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hδ0 _)
      have h2 : 0 ≤ (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans hδ0 hge) _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hHardy : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * (Real.pi / 2 - θ) ^ (2 - γ))
      (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) := by
    have hα : 0 < (2 : ℝ) - γ := by linarith
    -- regularity of `g`, `∂g` on the region, through `Lzero1 u`
    have hLz : ContDiffOn ℝ 2 (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1 2 hu
    have hLz1 : ContDiffOn ℝ 1 (deriv (Work.FTS.EllipticEst.Lzero1 u))
        (Set.Ioo 0 (Real.pi / 2)) := hLz.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hLz2 : ContDiffOn ℝ 0 (deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)))
        (Set.Ioo 0 (Real.pi / 2)) := hLz1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hsub : Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2⟩
    have hev1 : ∀ x ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
        deriv g x = deriv (Work.FTS.EllipticEst.Lzero1 u) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
      have hev : Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_Ioo.mem_nhds hx'] with t ht
        exact hode t ht
      exact hev.deriv_eq.symm
    have hev2 : ∀ x ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
        deriv (deriv g) x = deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
      have hev : Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_Ioo.mem_nhds hx'] with t ht
        exact hode t ht
      have h1 : deriv (Work.FTS.EllipticEst.Lzero1 u) =ᶠ[𝓝 x] deriv g := hev.deriv
      exact h1.deriv_eq.symm
    have hfcont : ContinuousOn (deriv g) (Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :=
      (hLz1.continuousOn.mono hsub).congr fun x hx => hev1 x hx
    have hf'cont : ContinuousOn (deriv (deriv g)) (Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :=
      (hLz2.continuousOn.mono hsub).congr fun x hx => hev2 x hx
    have hderivB : ∀ θ ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
        HasDerivAt (fun θ => deriv g θ) (deriv (deriv g) θ) θ := hasDerivAt_deriv_g hu hg'
    exact (hardy_local (α := 2 - γ) (f := fun θ => deriv g θ)
      (f' := fun θ => deriv (deriv g) θ) (ε := 1 / 8) hα (by norm_num)
      hfcont hf'cont hderivB hint).1
  refine MeasureTheory.Integrable.mono (hHardy.const_mul 4) ?_ ?_
  · exact (((measurable_deriv g).pow_const 2).aestronglyMeasurable).mul
      (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable)
  · filter_upwards [ae_mem_Ioo_of_Icc (a := Real.pi / 2 - 1 / 8) (b := Real.pi / 2)]
      with θ hθ
    obtain ⟨hge, hle⟩ := sin_two_between_pi_half ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs0 : 0 ≤ Real.sin (2 * θ) := le_trans (by linarith [hθ.2]) hge
    have hδ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have h1 : Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ Real.rpow (2 * (Real.pi / 2 - θ)) (2 - γ) :=
      Real.rpow_le_rpow hs0 hle (by linarith)
    have h2 : Real.rpow (2 * (Real.pi / 2 - θ)) (2 - γ)
        = 2 ^ (2 - γ) * (Real.pi / 2 - θ) ^ (2 - γ) :=
      Real.mul_rpow (by norm_num) hδ0
    have h3 : (2 : ℝ) ^ (2 - γ) ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : (2 : ℝ) - γ ≤ 2)
      rw [Real.rpow_two] at h
      norm_num at h
      exact h
    have hL : 0 ≤ (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hR : 0 ≤ 4 * ((deriv g θ) ^ 2 * (Real.pi / 2 - θ) ^ (2 - γ)) :=
      mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hδ0 _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR]
    calc (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (deriv g θ) ^ 2 * Real.rpow (2 * (Real.pi / 2 - θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (deriv g θ) ^ 2 * (2 ^ (2 - γ) * (Real.pi / 2 - θ) ^ (2 - γ)) := by rw [h2]
      _ ≤ (deriv g θ) ^ 2 * (4 * (Real.pi / 2 - θ) ^ (2 - γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          nlinarith [h3, Real.rpow_nonneg hδ0 (2 - γ)]
      _ = 4 * ((deriv g θ) ^ 2 * (Real.pi / 2 - θ) ^ (2 - γ)) := by ring

theorem sliceStep5Integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hupi : u (Real.pi / 2) = 0)
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (h4 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := by
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hV0 := sliceStep5_integrable_V0 γ hγ2 hu2 huc hu0 hupi h2
  have hV1 := sliceStep5_integrable_V1 γ hγ1 hγ2 hu2 huc hu0 hupi h2 h1 h0
  have hG0 := sliceStep5_integrable_G0 γ hγ1 hγ2 hu hode h2 h0 hV1
  refine ⟨hV0, hV1, hG0, ?_⟩
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hg' := deriv_g_eq_gE hu hode
  have hA_int := regionA_integrable γ hγ1 hγ2 hu hg' h3 h2 h1 h0
  have hB_int := regionB_integrable γ hγ1 hγ2 hu hode hg' hB
  have hunion := hA_int.union hB_int
  have hset : Set.Icc (0 : ℝ) (Real.pi / 2 - 1 / 8) ∪ Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)
      = Work.Spaces.Iθ := by
    rw [Iθ_eq_icc, Icc_split_pi_half]
  rwa [hset] at hunion

end Work.FTS.EllipticEst.H2W
