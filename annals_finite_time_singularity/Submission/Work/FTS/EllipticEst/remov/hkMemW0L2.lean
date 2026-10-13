import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hkMemW0L2`: the `L²`-slice and `L¹`-moments of `z² ∂_z²Ψ` are honest, with the
`√(π/2)` Cauchy–Schwarz bound

For a datum `(F, Ψ)` of the weak hypothesis class `TT.EllWeakPos α k F Ψ` with `k ≥ 1`:

1. for every `z ∈ Iz` the angular slice
   `θ ↦ ((z² ∂_z²Ψ) · w(z)/sin(2θ)^{η/2})²` is integrable on `Iθ` (this is the `i = 0`
   term of the weighted `ℋ^k`-integrand of `A = z²∂_z²Ψ`, and `HkMem α k A` is part of the
   hypothesis class);
2. the `θ`-integral of that slice is integrable in `z` on `Iz`;
3. for every `z > 0` the `L¹(sinθcos²θ)`-moment of `∂_z²Ψ` is controlled by the weighted
   `L²`-slice of `A` through Cauchy–Schwarz: since `sinθcos²θ ≤ 1 ≤ w(z)/sin(2θ)^{η/2}`
   on the open quadrant, `|∂_z²Ψ|·sinθcos²θ ≤ |A·w/sin^{η/2}|/z²`, and the Cauchy–Schwarz
   inequality with the constant function `1` on `Iθ` (whose mass is `π/2`) gives the factor
   `√(π/2)`.

These are precisely the hypotheses `hQJ` and `hCs` of
`Submission/Work/FTS/EllipticEst/remov/_scratch_core.lean`.
-/

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Elementary angular facts -/

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

private lemma sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rw [Work.Elliptic.sinCos2, h3]; ring
  · rw [Work.Elliptic.sinCos2, h3]; ring

/-- The radial weight is at least `1` on `z > 0`. -/
private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (pow_pos hz 2)]
  nlinarith [hz]

/-- `sinθcos²θ ≤ w(z)/sin(2θ)^{η/2}` on `Iθ`, for `z > 0`. -/
private lemma sinCos2_le_wdiv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hsin2 := sin_two_nonneg_Iθ hθ
  have hsc1 : Work.Elliptic.sinCos2 θ ≤ 1 := by
    obtain ⟨h0, h1⟩ := hθ
    have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
    have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
    have hc2 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.cos_le_one θ, hc0, Real.neg_one_le_cos θ]
    rw [Work.Elliptic.sinCos2]
    nlinarith [hs, hs0, hc2]
  by_cases h0 : Real.sin (2 * θ) = 0
  · rw [sinCos2_eq_zero_of_sin_two_eq_zero h0]
    exact div_nonneg (le_trans zero_le_one (one_le_w hz)) (Real.rpow_nonneg hsin2 _)
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin2 (Ne.symm h0)
    have hrpow : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsin2 (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
    have hr : 1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [one_le_div (Real.rpow_pos_of_pos hspos _)]
      exact le_trans hrpow (one_le_w hz)
    linarith

/-- `|x| ≤ x² + 1`. -/
private lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_abs x, sq_nonneg (|x| - 1), abs_nonneg x]

/-- `(1/z²)·|z²·(F·R)| = |F|·|R|` for `z > 0`. -/
private lemma one_div_zsq_mul_abs (z F R : ℝ) (hz : 0 < z) :
    (1 / z ^ 2) * |z ^ 2 * (F * R)| = |F| * |R| := by
  have hz2 : z ^ 2 ≠ 0 := ne_of_gt (pow_pos hz 2)
  rw [one_div, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2), ← mul_assoc,
    inv_mul_cancel₀ hz2, one_mul]

/-! ## The function `A = z²∂_z²Ψ` is smooth on the open quadrant -/

private lemma smoothOpen_zsq_pzIter2 {Ψ : ℝ → ℝ → ℝ}
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hs
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    Work.FTS.EllipticEst.Q0
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst.pow 2
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Work.FTS.EllipticEst.Q0 :=
    hsm.pzIter 2
  rw [show Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) from rfl]
  exact h2.mul h3

/-! ## The outer integrability of a single weighted `D_z`-summand on all of `Iz` -/

/-- **A single weighted `D_z`-summand of the `ℋ^k`-integrand has integrable `θ`-integral on
all of `Iz`** (the non-compact version of `Work.FTS.EllipticEst.integrableOn_slice_l2`, whose
proof establishes exactly this and then restricts to `[a,b]`). -/
private lemma outer_zSummand {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F s θ
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F s θ
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hjoint.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only using h
  refine hmem.2.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 s hs)
    (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α k F s θ i hi)

/-! ## Cauchy–Schwarz (`L¹(sinθcos²θ)` against the weighted `L²`-slice) -/

/-- **The `√(π/2)` bound.**  For `F` with `A := z²F`, on the open quadrant
`|F|·sinθcos²θ ≤ (1/z²)·|A·w/sin(2θ)^{η/2}|`, so Cauchy–Schwarz with the constant function
`1` on `Iθ` (whose mass is `π/2`) gives
`∫_θ |F|·sinθcos²θ ≤ (1/z²)√(π/2)√(∫_θ (A·w/sin(2θ)^{η/2})²)`. -/
private lemma L1_le_sqrt_aux {F : ℝ → ℝ → ℝ}
    (haesm : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (z ^ 2 * F z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hU : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * F z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ) :
    ∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, ((z ^ 2 * F z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  intro z hz
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  have hz2ne : z ^ 2 ≠ 0 := ne_of_gt hz2
  have hwpos : 0 < Work.Spaces.w z := lt_of_lt_of_le zero_lt_one (one_le_w hz)
  set β : ℝ → ℝ := fun θ => (z ^ 2 * F z θ)
    * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) with hβdef
  have hβeq : (fun θ : ℝ => (β θ) ^ 2)
      = fun θ : ℝ => ((z ^ 2 * F z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hβdef]
  have hUβ : MeasureTheory.IntegrableOn (fun θ => (β θ) ^ 2) Work.Spaces.Iθ := by
    simpa only [hβeq] using hU z hz
  have haesmβ : MeasureTheory.AEStronglyMeasurable β
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [hβdef] using haesm z hz
  have haesm_abs : MeasureTheory.AEStronglyMeasurable (fun θ => |β θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using haesmβ.norm
  -- `|β|` is integrable: `|β| ≤ β² + 1`.
  have hβabs : MeasureTheory.IntegrableOn (fun θ => |β θ|) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (g := fun θ => (β θ) ^ 2 + 1) ?_ haesm_abs ?_
    · have h1 : MeasureTheory.IntegrableOn (fun θ => (β θ) ^ 2 + 1) Work.Spaces.Iθ :=
        hUβ.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact MeasureTheory.IntegrableOn.integrable h1
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact abs_le_sq_add_one (β θ)
  have hβabsmul : MeasureTheory.IntegrableOn (fun θ => (1 / z ^ 2) * |β θ|) Work.Spaces.Iθ :=
    hβabs.const_mul _
  -- pointwise domination on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      |F z θ| * Work.Elliptic.sinCos2 θ ≤ (1 / z ^ 2) * |β θ| := by
    intro θ hθ
    have hsc := sinCos2_le_wdiv hz hθ
    have hr0 : 0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      div_nonneg (le_of_lt hwpos) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
    have hβval : β θ = z ^ 2 * (F z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) := by
      rw [hβdef]; ring
    rw [hβval, one_div_zsq_mul_abs z (F z θ)
      (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) hz, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
  have hmain : (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ)
      ≤ (1 / z ^ 2) * ∫ θ in Work.Spaces.Iθ, |β θ| := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (f := fun θ => |F z θ| * Work.Elliptic.sinCos2 θ)
      (g := fun θ => (1 / z ^ 2) * |β θ|)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ)))
      hβabsmul
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => hpt θ hθ))
    rwa [MeasureTheory.integral_const_mul] at h
  -- Cauchy–Schwarz with the constant function `1`
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Work.Spaces.Iθ, Measure.restrict_apply_univ, Real.volume_Icc];
        exact ENNReal.ofReal_lt_top⟩
  have hu : MeasureTheory.MemLp (fun θ => |β θ|) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm_abs).mpr
      (hUβ.congr (Filter.Eventually.of_forall fun θ => (sq_abs (β θ)).symm))
  have hv : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := MeasureTheory.memLp_const 1
  have hcs := Work.Spaces.cs_integral hu hv
  have hvval : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hcs' : (∫ θ in Work.Spaces.Iθ, |β θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * (Real.pi / 2) := by
    have h := hcs
    have h1 : (∫ x in Work.Spaces.Iθ, |β x| * (fun _ : ℝ => (1 : ℝ)) x)
        = ∫ x in Work.Spaces.Iθ, |β x| :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x _ => by simp)
    have h2 : (∫ x in Work.Spaces.Iθ, |β x| ^ 2)
        = ∫ x in Work.Spaces.Iθ, (β x) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x _ => sq_abs (β x))
    have h3 : (∫ x in Work.Spaces.Iθ, ((fun _ : ℝ => (1 : ℝ)) x) ^ 2)
        = Real.pi / 2 := by
      have hfun : (fun x : ℝ => ((fun _ : ℝ => (1 : ℝ)) x) ^ 2)
          = fun _ : ℝ => (1 : ℝ) := by
        funext x; simp
      rw [hfun]
      simpa using hvval
    rw [h1, h2, h3] at h
    exact h
  have hsnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |β θ| :=
    MeasureTheory.integral_nonneg fun θ => abs_nonneg _
  have hsqnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (β θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hsqrt : (∫ θ in Work.Spaces.Iθ, |β θ|)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * Real.sqrt (Real.pi / 2) := by
    calc (∫ θ in Work.Spaces.Iθ, |β θ|)
        = Real.sqrt ((∫ θ in Work.Spaces.Iθ, |β θ|) ^ 2) := (Real.sqrt_sq hsnn).symm
      _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * (Real.pi / 2)) :=
          Real.sqrt_le_sqrt hcs'
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * Real.sqrt (Real.pi / 2) :=
          Real.sqrt_mul hsqnn _
  have key : (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ)
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ)
        ≤ (1 / z ^ 2) * ∫ θ in Work.Spaces.Iθ, |β θ| := hmain
      _ ≤ (1 / z ^ 2) * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2)
            * Real.sqrt (Real.pi / 2)) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) := by ring
  rwa [hβeq] at key

/-! ## The target -/

theorem hkMemW0L2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ) ∧
    (MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz) ∧
    (∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
  := by
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq_pzIter2 h.smooth
  -- (1) the angular slices are integrable: the `i = 0` weighted `D_z`-summand of `A`
  have hpart1 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    intro z hz
    simpa only [Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.integrableOn_zSummand α k hA h.memA 0 (Nat.zero_le k) hz
  -- (2) the `θ`-integral of that slice is integrable in `z`
  have hpart2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
    simpa only [Work.Spaces.DzIter_zero] using
      outer_zSummand (α := α) (k := k)
        (F := fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hA h.memA 0 (Nat.zero_le k)
  -- (3) Cauchy-Schwarz
  have hpart3 : ∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    intro z hz
    exact L1_le_sqrt_aux (F := fun z θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ)
      (fun z hz => by
        simpa only [Work.Spaces.DzIter_zero] using hA.aesm_slice_summand 0 hz)
      (fun z hz => hpart1 z (Set.mem_Ici.mpr (le_of_lt hz)))
      z hz
  exact ⟨hpart1, hpart2, hpart3⟩

end

end Work.FTS.EllipticEst.remov
