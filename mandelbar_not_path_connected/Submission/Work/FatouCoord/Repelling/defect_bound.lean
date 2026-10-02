import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound
import Submission.Work.FatouCoord.Repelling.second_order_mod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The defect of the corrected ansatz is `O((1 + log ‖w‖)/‖w‖²)` on the left half-plane

For the parabolic germ `f z = z + z ^ 2 h z` (`h 0 = 1`, `ParabolicBounds f h a r A A'`) the
repelling coordinate is built from the corrected ansatz `V w = w + (1 - a) Λ w + Z w` on a
left half-plane `{Re w < -R}`, where `Λ w = log(-w) + π i`.  The *defect*
`Petal.defect f a w ζ` measures how far the ansatz is from solving `V (w+1) = wMap f (V w)`;
this file shows that it is `O((1 + log ‖w‖)/‖w‖²)`, uniformly for `‖ζ‖ ≤ 1`.

The strategy is: with `V = w + (1-a) Λ w + ζ`,

`defect = (wMap f V - V - 1 - (1-a)/V) + (1-a) (1/V - (Λ (w+1) - Λ w))`.

The first summand is `O(1/‖V‖²) = O(1/‖w‖²)` by `second_order_mod`.  For the second one, `1/V`
differs from `1/w` by `O(log ‖w‖/‖w‖²)` (because `V - w = O(log ‖w‖)` while `‖V‖ ≥ ‖w‖/2`),
and `Λ (w+1) - Λ w` differs from `1/w` by `O(1/‖w‖²)` (mean value inequality, using that
`Λ' = 1/s` on the left half-plane).  The logarithm is absorbed because `w` ranges over a
half-plane of large radius: `log t / t → 0` as `t → ∞`.
-/

open scoped Topology
open Set Filter Metric

namespace Work.FatouCoord.Repelling

open Work.FatouCoord Work.FatouCoord.Petal

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Three elementary estimates -/

/-- On the left half-plane, `‖Λ w‖ ≤ log ‖w‖ + 2π` (for `‖w‖ ≥ 1`): the real part of `Λ w`
is `log ‖w‖` and its imaginary part is `arg (-w) + π ∈ (0, 2π]`. -/
private lemma norm_Lambda_le {w : ℂ} (h1 : 1 ≤ ‖w‖) :
    ‖Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := by
  have hrev : (Lambda w).re = Real.log ‖w‖ := by simp [Lambda, Complex.log_re]
  have himv : (Lambda w).im = (-w).arg + Real.pi := by simp [Lambda, Complex.log_im]
  have harg := Complex.arg_mem_Ioc (-w)
  rw [Set.mem_Ioc] at harg
  have hlog0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg h1
  have himabs : |(Lambda w).im| ≤ 2 * Real.pi := by
    rw [himv, abs_le]; constructor <;> linarith [harg.1, harg.2]
  calc ‖Lambda w‖ ≤ |(Lambda w).re| + |(Lambda w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖w‖ + |(Lambda w).im| := by rw [hrev, abs_of_nonneg hlog0]
    _ ≤ Real.log ‖w‖ + 2 * Real.pi := by linarith

/-- For large `t`, `C * (1 + log t) ≤ t / 2`. -/
private lemma log_growth (C : ℝ) (hC : 0 ≤ C) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → C * (1 + Real.log t) ≤ t / 2 := by
  have h1 : ∀ᶠ t : ℝ in Filter.atTop, C * Real.log t ≤ t / 4 := by
    have h := Real.isLittleO_log_id_atTop.const_mul_left (4 * C)
    filter_upwards [h.eventuallyLE, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht0, abs_mul, abs_of_nonneg hC,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at ht
    have h3 : C * Real.log t ≤ C * |Real.log t| := mul_le_mul_of_nonneg_left (le_abs_self _) hC
    linarith
  have h2 : ∀ᶠ t : ℝ in Filter.atTop, (4 : ℝ) * C ≤ t := Filter.eventually_ge_atTop (4 * C)
  have hmain : ∀ᶠ t : ℝ in Filter.atTop, C * (1 + Real.log t) ≤ t / 2 := by
    filter_upwards [h1, h2] with t ht1 ht2
    have hh : C ≤ t / 4 := by linarith
    linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨T, fun t ht => hT t ht⟩

/-- `Λ` is a primitive of `1/s` on the left half-plane, so the mean value inequality along the
segment from `w` to `w + 1` gives `‖Λ (w+1) - Λ w - 1/w‖ ≤ 2/‖w‖²` as soon as `Re w < -1`
(which keeps the whole segment inside the left half-plane) and `‖w‖ ≥ 2`. -/
private lemma Lambda_sub_bound {w : ℂ} (hre : w.re < -1) (h2 : 2 ≤ ‖w‖) :
    ‖Lambda (w + 1) - Lambda w - 1 / w‖ ≤ 2 / ‖w‖ ^ 2 := by
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) h2
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwn)
  have hconv_re : Convex ℝ {x : ℂ | x.re ≤ w.re + 1} :=
    (convex_Iic (w.re + 1)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have hmem_re : ∀ x ∈ segment ℝ w (w + 1), x.re < 0 := by
    intro x hx
    have h1 : w ∈ {x : ℂ | x.re ≤ w.re + 1} := by simp
    have h2' : w + 1 ∈ {x : ℂ | x.re ≤ w.re + 1} := by simp
    have hx' : x.re ≤ w.re + 1 := hconv_re.segment_subset h1 h2' hx
    linarith
  have hmem_norm : ∀ x ∈ segment ℝ w (w + 1), ‖w‖ / 2 ≤ ‖x‖ := by
    intro x hx
    have h1 : w ∈ Metric.closedBall w 1 := by simp
    have h2' : w + 1 ∈ Metric.closedBall w 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; simp
    have hx' := (convex_closedBall w 1).segment_subset h1 h2' hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    have h3 : ‖w‖ ≤ ‖w - x‖ + ‖x‖ := by
      have hh := norm_add_le (w - x) x
      rwa [sub_add_cancel] at hh
    have h4 : ‖w - x‖ ≤ 1 := by rw [norm_sub_rev] at hx'; exact hx'
    linarith
  have hderiv : ∀ x ∈ segment ℝ w (w + 1),
      HasDerivAt (fun y : ℂ => Lambda y - y / w) (1 / x - 1 / w) x := by
    intro x hx
    have hxre : x.re < 0 := hmem_re x hx
    have hxs : -x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; exact Or.inl (by simpa using hxre)
    have h1 : HasDerivAt Complex.log ((-x)⁻¹) (-x) := Complex.hasDerivAt_log hxs
    have h2d : HasDerivAt (fun y : ℂ => Complex.log (-y)) (((-x)⁻¹) * (-1)) x :=
      h1.comp x (hasDerivAt_neg x)
    have h3 : HasDerivAt Lambda (((-x)⁻¹ * (-1)) + 0) x := by
      have hh := h2d.add_const ((Real.pi : ℂ) * Complex.I)
      convert hh using 1
      · funext y; simp [Lambda]
      · ring
    have h4 : HasDerivAt (fun y : ℂ => y / w) (1 / w) x := (hasDerivAt_id x).div_const w
    have h5 := h3.sub h4
    have hval : ((-x)⁻¹ * (-1) + 0) - 1 / w = 1 / x - 1 / w := by
      have hx0 : x ≠ 0 := by intro h; rw [h] at hxre; simp at hxre
      field_simp
      ring
    rwa [hval] at h5
  have hbnd : ∀ x ∈ segment ℝ w (w + 1),
      ‖deriv (fun y : ℂ => Lambda y - y / w) x‖ ≤ 2 / ‖w‖ ^ 2 := by
    intro x hx
    have hxre : x.re < 0 := hmem_re x hx
    have hxn : ‖w‖ / 2 ≤ ‖x‖ := hmem_norm x hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hxre; simp at hxre
    have hxn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    rw [(hderiv x hx).deriv]
    have hxw : ‖w - x‖ ≤ 1 := by
      have h1 : w ∈ Metric.closedBall w 1 := by simp
      have h2' : w + 1 ∈ Metric.closedBall w 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]; simp
      have hx' := (convex_closedBall w 1).segment_subset h1 h2' hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx'
      rwa [norm_sub_rev]
    have heq : (1:ℂ) / x - 1 / w = (w - x) / (x * w) := by
      field_simp
    rw [heq, norm_div, norm_mul]
    have hden : 0 < ‖x‖ * ‖w‖ := mul_pos hxn0 hwn
    have hden2 : 0 < (‖w‖ / 2) * ‖w‖ := by positivity
    calc ‖w - x‖ / (‖x‖ * ‖w‖) ≤ 1 / (‖x‖ * ‖w‖) :=
          div_le_div_of_nonneg_right hxw hden.le
      _ ≤ 1 / ((‖w‖ / 2) * ‖w‖) := by
          apply one_div_le_one_div_of_le hden2
          nlinarith [hxn, hwn]
      _ = 2 / ‖w‖ ^ 2 := by
          rw [show (‖w‖ / 2) * ‖w‖ = ‖w‖ ^ 2 / 2 by ring, one_div_div]
  have hmvt := (convex_segment (𝕜 := ℝ) w (w + 1)).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hderiv x hx).differentiableAt) hbnd
      (left_mem_segment ℝ w (w + 1)) (right_mem_segment ℝ w (w + 1))
  have hww : w / w = 1 := div_self hw0
  rw [hww] at hmvt
  have e : (Lambda (w + 1) - (w + 1) / w) - (Lambda w - 1)
      = Lambda (w + 1) - Lambda w - 1 / w := by
    rw [show (w + 1) / w = 1 + 1 / w by field_simp]; ring
  rw [e] at hmvt
  simpa using hmvt

/-- Comparison of reciprocals: if `‖w‖/2 ≤ ‖V‖` then `‖1/V - 1/w‖ ≤ 2‖V - w‖/‖w‖²`. -/
private lemma norm_inv_sub_inv_le {V w : ℂ} (hw : 0 < ‖w‖) (hV : ‖w‖ / 2 ≤ ‖V‖) :
    ‖1 / V - 1 / w‖ ≤ 2 * ‖V - w‖ / ‖w‖ ^ 2 := by
  have hVpos : 0 < ‖V‖ := by linarith
  have hVne : V ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hVpos)
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hw)
  rw [show (1:ℂ) / V - 1 / w = (w - V) / (V * w) by
        field_simp, norm_div, norm_mul]
  rw [div_le_div_iff₀ (mul_pos hVpos hw) (by positivity)]
  rw [norm_sub_rev w V]
  have hdnn : 0 ≤ ‖V - w‖ := norm_nonneg _
  rw [show 2 * ‖V - w‖ * (‖V‖ * ‖w‖) = ‖V - w‖ * (2 * ‖V‖ * ‖w‖) by ring]
  apply mul_le_mul_of_nonneg_left _ hdnn
  have h : ‖w‖ ≤ 2 * ‖V‖ := by linarith
  calc ‖w‖ ^ 2 = ‖w‖ * ‖w‖ := by ring
    _ ≤ (2 * ‖V‖) * ‖w‖ := mul_le_mul_of_nonneg_right h hw.le
    _ = 2 * ‖V‖ * ‖w‖ := by ring

/-! ## The main estimate -/

theorem defect_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ R K : ℝ, 0 < R ∧ 1 / r < R ∧ 0 ≤ K ∧ ∀ w ζ : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖ζ‖ ≤ 1 → ‖Work.FatouCoord.Petal.defect f a w ζ‖ ≤ K * (1 + Real.log ‖w‖) / ‖w‖ ^ 2 := by
  obtain ⟨K2, hK2nn, hK2⟩ := second_order_mod hb
  set C : ℝ := ‖1 - a‖ * (1 + 2 * Real.pi) + 1 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨T, hT⟩ := log_growth C hCnn
  set K : ℝ := 4 * K2 + ‖1 - a‖ * (2 * C + 2) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 4 * K2 := by linarith
    have h2 : 0 ≤ ‖1 - a‖ * (2 * C + 2) := by
      apply mul_nonneg (norm_nonneg _); linarith
    linarith
  set R : ℝ := max 8 (max (2 / r) T) + 1 with hRdef
  have hR8 : 8 < R := by
    rw [hRdef]
    have := le_max_left (8:ℝ) (max (2 / r) T); linarith
  have hR2r : 2 / r < R := by
    rw [hRdef]
    have := le_trans (le_max_left (2 / r) T) (le_max_right (8:ℝ) (max (2 / r) T))
    linarith
  have hRT : T < R := by
    rw [hRdef]
    have := le_trans (le_max_right (2 / r) T) (le_max_right (8:ℝ) (max (2 / r) T))
    linarith
  have hRpos : 0 < R := by linarith
  have h2r : (2:ℝ) / r = 2 * (1 / r) := by ring
  have hr1 : 0 < 1 / r := one_div_pos.mpr hb.hr
  have hRr : 1 / r < R := by rw [h2r] at hR2r; linarith
  refine ⟨R, K, hRpos, hRr, hKnn, ?_⟩
  intro w ζ hw hζ
  rw [mem_LeftHalfPlane] at hw
  have hwnR : R < ‖w‖ := by
    have h1 : -w.re ≤ ‖w‖ := le_trans (neg_le_abs _) (Complex.abs_re_le_norm w)
    linarith
  have hwn : 0 < ‖w‖ := by linarith
  have hlog0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg (by linarith)
  have hw1 : 1 ≤ ‖w‖ := by linarith
  set V : ℂ := w + (1 - a) * Lambda w + ζ with hV
  have hVw : ‖V - w‖ ≤ C * (1 + Real.log ‖w‖) := by
    have h1 : V - w = (1 - a) * Lambda w + ζ := by rw [hV]; ring
    rw [h1]
    have h3 : ‖Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := norm_Lambda_le hw1
    have hL : 0 ≤ ‖1 - a‖ := norm_nonneg _
    calc ‖(1 - a) * Lambda w + ζ‖ ≤ ‖(1 - a) * Lambda w‖ + ‖ζ‖ := norm_add_le _ _
      _ = ‖1 - a‖ * ‖Lambda w‖ + ‖ζ‖ := by rw [norm_mul]
      _ ≤ ‖1 - a‖ * (Real.log ‖w‖ + 2 * Real.pi) + 1 := by
          have h4 : ‖1 - a‖ * ‖Lambda w‖ ≤ ‖1 - a‖ * (Real.log ‖w‖ + 2 * Real.pi) :=
            mul_le_mul_of_nonneg_left h3 hL
          linarith
      _ ≤ C * (1 + Real.log ‖w‖) := by
          rw [hCdef]
          have he : (‖1 - a‖ * (1 + 2 * Real.pi) + 1) * (1 + Real.log ‖w‖)
              = ‖1 - a‖ * (Real.log ‖w‖ + 2 * Real.pi) + 1
                + (‖1 - a‖ + 2 * Real.pi * (‖1 - a‖ * Real.log ‖w‖) + Real.log ‖w‖) := by
            ring
          rw [he]
          have h5 : 0 ≤ 2 * Real.pi * (‖1 - a‖ * Real.log ‖w‖) :=
            mul_nonneg (by positivity) (mul_nonneg hL hlog0)
          linarith
  have hVw2 : ‖V - w‖ ≤ ‖w‖ / 2 := by
    have h := hT ‖w‖ (by linarith)
    linarith
  have hVnorm : ‖w‖ / 2 ≤ ‖V‖ := by
    have h := norm_le_add_norm_add w (V - w)
    rw [add_sub_cancel] at h
    linarith
  have hVne : V ≠ 0 := by
    intro h0; rw [h0] at hVnorm; simp at hVnorm; linarith
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hVne
  have hVr : 1 / r < ‖V‖ := by
    have hR2 : 1 / r < R / 2 := by linarith
    linarith
  have hV4 : 4 ≤ ‖V‖ := by linarith
  have h2nd := hK2 V hVr hV4
  have hre1 : w.re < -1 := by linarith
  have hLam : ‖Lambda (w + 1) - Lambda w - 1 / w‖ ≤ 2 / ‖w‖ ^ 2 :=
    Lambda_sub_bound hre1 (by linarith)
  have hinv : ‖1 / V - 1 / w‖ ≤ 2 * C * (1 + Real.log ‖w‖) / ‖w‖ ^ 2 := by
    have h := norm_inv_sub_inv_le hwn hVnorm
    calc ‖1 / V - 1 / w‖ ≤ 2 * ‖V - w‖ / ‖w‖ ^ 2 := h
      _ ≤ 2 * (C * (1 + Real.log ‖w‖)) / ‖w‖ ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
      _ = 2 * C * (1 + Real.log ‖w‖) / ‖w‖ ^ 2 := by ring
  have hbracket : ‖1 / V - (Lambda (w + 1) - Lambda w)‖
      ≤ (2 * C * (1 + Real.log ‖w‖) + 2) / ‖w‖ ^ 2 := by
    have h1 : 1 / V - (Lambda (w + 1) - Lambda w)
        = (1 / V - 1 / w) + (1 / w - (Lambda (w + 1) - Lambda w)) := by ring
    rw [h1]
    have h2 : ‖1 / w - (Lambda (w + 1) - Lambda w)‖ ≤ 2 / ‖w‖ ^ 2 := by
      rw [norm_sub_rev]; exact hLam
    calc ‖(1 / V - 1 / w) + (1 / w - (Lambda (w + 1) - Lambda w))‖
        ≤ ‖1 / V - 1 / w‖ + ‖1 / w - (Lambda (w + 1) - Lambda w)‖ := norm_add_le _ _
      _ ≤ 2 * C * (1 + Real.log ‖w‖) / ‖w‖ ^ 2 + 2 / ‖w‖ ^ 2 := add_le_add hinv h2
      _ = (2 * C * (1 + Real.log ‖w‖) + 2) / ‖w‖ ^ 2 := by ring
  have hdec : defect f a w ζ = (wMap f V - V - 1 - (1 - a) / V)
      + (1 - a) * (1 / V - (Lambda (w + 1) - Lambda w)) := by
    rw [defect_apply, corr_apply, hV]
    ring
  have hI : K2 / ‖V‖ ^ 2 ≤ 4 * K2 / ‖w‖ ^ 2 := by
    have hV2 : ‖w‖ ^ 2 / 4 ≤ ‖V‖ ^ 2 := by nlinarith [hVnorm, hwn]
    have h1 : 1 / ‖V‖ ^ 2 ≤ 4 / ‖w‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hV2]
    calc K2 / ‖V‖ ^ 2 = K2 * (1 / ‖V‖ ^ 2) := by ring
      _ ≤ K2 * (4 / ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hK2nn
      _ = 4 * K2 / ‖w‖ ^ 2 := by ring
  have hnum : 4 * K2 + ‖1 - a‖ * (2 * C * (1 + Real.log ‖w‖) + 2)
      ≤ (4 * K2 + ‖1 - a‖ * (2 * C + 2)) * (1 + Real.log ‖w‖) := by
    have hL : 0 ≤ ‖1 - a‖ := norm_nonneg _
    have he : (4 * K2 + ‖1 - a‖ * (2 * C + 2)) * (1 + Real.log ‖w‖)
        = 4 * K2 + ‖1 - a‖ * (2 * C * (1 + Real.log ‖w‖) + 2)
          + (4 * K2 * Real.log ‖w‖ + ‖1 - a‖ * (2 * Real.log ‖w‖)) := by ring
    rw [he]
    have h4 : 0 ≤ 4 * K2 * Real.log ‖w‖ := mul_nonneg (by linarith) hlog0
    have h5 : 0 ≤ ‖1 - a‖ * (2 * Real.log ‖w‖) := mul_nonneg hL (by linarith)
    linarith
  calc ‖defect f a w ζ‖
      = ‖(wMap f V - V - 1 - (1 - a) / V)
          + (1 - a) * (1 / V - (Lambda (w + 1) - Lambda w))‖ := by rw [hdec]
    _ ≤ ‖wMap f V - V - 1 - (1 - a) / V‖
          + ‖(1 - a) * (1 / V - (Lambda (w + 1) - Lambda w))‖ := norm_add_le _ _
    _ ≤ 4 * K2 / ‖w‖ ^ 2 + ‖1 - a‖ * ((2 * C * (1 + Real.log ‖w‖) + 2) / ‖w‖ ^ 2) := by
        have h3 : ‖(1 - a) * (1 / V - (Lambda (w + 1) - Lambda w))‖
            ≤ ‖1 - a‖ * ((2 * C * (1 + Real.log ‖w‖) + 2) / ‖w‖ ^ 2) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hbracket (norm_nonneg _)
        exact add_le_add (le_trans h2nd hI) h3
    _ ≤ K * (1 + Real.log ‖w‖) / ‖w‖ ^ 2 := by
        rw [hKdef]
        have h3 : ‖1 - a‖ * ((2 * C * (1 + Real.log ‖w‖) + 2) / ‖w‖ ^ 2)
            = ‖1 - a‖ * (2 * C * (1 + Real.log ‖w‖) + 2) / ‖w‖ ^ 2 := by ring
        rw [h3]
        rw [← add_div]
        exact div_le_div_of_nonneg_right hnum (by positivity)

end

end Work.FatouCoord.Repelling
