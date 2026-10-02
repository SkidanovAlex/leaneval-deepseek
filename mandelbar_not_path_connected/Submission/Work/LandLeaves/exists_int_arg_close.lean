/-
# `exists_int_arg_close`: the directions of the dynamic ray points tend to their angle

For `θ ∈ ℝ` and a fixed point `y`, the points `p_θ(t) = Work.EL.rayPt hN θ t` of the dynamical
ray of angle `θ` at level `t` leave every compact set as `t → ∞`
(`Work.LandLeaves.tendsto_norm_rayPt_atTop`), and the Böttcher coordinate `φ` is asymptotic to
the identity at infinity (`Work.ParamRays.IsDynBottcher`), so `p_θ(t) / (t e^{2πiθ}) → 1`.  As a
consequence the *direction* of `p_θ(t)` as seen from `y` tends to `θ` modulo `1`: for every
`ϑ > 0` and all large `t` there is `m : ℤ` with
`|arg (p_θ(t) - y) / (2π) - (θ + m)| ≤ ϑ`.

This is the analytic estimate behind the large-level half of the local-order dichotomy
(`Work.LandLeaves.rayArg_ccBet_of_large`, `Work.LandLeaves.rayArg_largeLevel_ccBet`).
-/
import Mathlib
import Submission.Work.LandLeaves.tendsto_norm_rayPt_atTop
import Submission.Work.LandLeaves.rayArg_ccBet_of_large

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

namespace Work.LandLeaves
/-- **The Böttcher coordinate is asymptotic to the identity at infinity.** -/
private theorem tendsto_phi_div_self_of_isDynBottcher {c : ℂ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Tendsto (fun z : ℂ => φ z / z) (cocompact ℂ) (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have h1 : ∀ᶠ z : ℂ in cocompact ℂ, ‖φ z - z‖ ≤ ε / 2 * ‖z‖ := hφ.2.2 (ε / 2) hε2
  have h2 : ∀ᶠ z : ℂ in cocompact ℂ, (1 : ℝ) ≤ ‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually_ge_atTop 1
  filter_upwards [h1, h2] with z hz hz1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [dist_eq_norm, div_sub_one hz0, norm_div, div_lt_iff₀ hzn]
  nlinarith [hz, hzn, hε]

/-- The reciprocal form of the previous asymptotic. -/
private theorem tendsto_self_div_phi_of_isDynBottcher {c : ℂ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Tendsto (fun z : ℂ => z / φ z) (cocompact ℂ) (nhds 1) := by
  have h := tendsto_phi_div_self_of_isDynBottcher hφ
  have h2 : Tendsto (fun w : ℂ => w⁻¹) (nhds (1 : ℂ)) (nhds (1 : ℂ)) := by
    have := (continuousAt_inv₀ (x := (1 : ℂ)) (by norm_num)).tendsto
    simpa using this
  refine Filter.Tendsto.congr' (Eventually.of_forall fun z => inv_div (φ z) z) ?_
  exact h2.comp h

/-- The `φ`-image of the level-`t` ray point: `φ (rayPt θ t) = t · e^{2πiθ}`. -/
private theorem phi_rayPt_eq_mul_exp {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t : ℝ}
    (ht : 1 < t) :
    φ (Work.EL.rayPt hN θ t)
      = (t : ℂ) * Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
  have hK : Work.EL.rayPt hN θ t ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN ht
  rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hK, Work.Top.NakaneData.Phi_rayPt hN ht,
    Work.Top.NakaneData.rayPoint,
    show (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = (((2 * Real.pi * θ : ℝ)) : ℂ) * Complex.I by push_cast; ring]

/-- **The directions of the level-`t` ray points tend to `2πθ`.**  For every `ϑ > 0` and every
fixed `y`, the argument of `rayPt hN θ t - y`, measured in turns, is within `ϑ` of `θ` modulo `1`
for all sufficiently large levels `t`. -/
private theorem exists_int_arg_close_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) (y : ℂ) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ m : ℤ,
      |Complex.arg (Work.EL.rayPt hN θ t - y) / (2 * Real.pi) - (θ + (m : ℝ))| ≤ ϑ := by
  set D : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) with hD
  have hD0 : D ≠ 0 := Complex.exp_ne_zero _
  -- the ray points leave every compact set
  have hcoc : Tendsto (fun t : ℝ => Work.EL.rayPt hN θ t) atTop (cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by
      simpa only [dist_zero_right] using Work.LandLeaves.tendsto_norm_rayPt_atTop hN θ)
  have hdiv : Tendsto (fun t : ℝ => Work.EL.rayPt hN θ t / φ (Work.EL.rayPt hN θ t))
      atTop (nhds 1) := (tendsto_self_div_phi_of_isDynBottcher hφ).comp hcoc
  have hphi : ∀ᶠ t : ℝ in atTop, φ (Work.EL.rayPt hN θ t) = (t : ℂ) * D := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simpa only [hD] using phi_rayPt_eq_mul_exp hN ht
  -- the numerator `y` is negligible
  have hy0 : Tendsto (fun t : ℝ => y / ((t : ℂ) * D)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbase : Tendsto (fun t : ℝ => ‖y‖ / t) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop (f := fun _ : ℝ => ‖y‖) (g := fun t : ℝ => t)
        tendsto_const_nhds Filter.tendsto_id
    refine Filter.Tendsto.congr' ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht_norm : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
    have hD_norm : ‖D‖ = 1 := by
      rw [hD, Complex.norm_exp]
      have hre : (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
      rw [hre, Real.exp_zero]
    rw [norm_div, norm_mul, ht_norm, hD_norm, mul_one]
  -- the ratio tends to `1`
  have hmain : Tendsto (fun t : ℝ => (Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D))
      atTop (nhds 1) := by
    have heq : (fun t : ℝ => (Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) =ᶠ[atTop]
        (fun t : ℝ => Work.EL.rayPt hN θ t / φ (Work.EL.rayPt hN θ t)
          - y / φ (Work.EL.rayPt hN θ t)) := by
      filter_upwards [hphi] with t ht
      rw [ht, sub_div]
    have hyφ : Tendsto (fun t : ℝ => y / φ (Work.EL.rayPt hN θ t)) atTop (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ hy0
      filter_upwards [hphi] with t ht
      rw [ht]
    have h2 : Tendsto (fun t : ℝ => Work.EL.rayPt hN θ t / φ (Work.EL.rayPt hN θ t)
        - y / φ (Work.EL.rayPt hN θ t)) atTop (nhds 1) := by
      simpa using hdiv.sub hyφ
    exact Filter.Tendsto.congr' heq.symm h2
  have harg : Tendsto (fun t : ℝ => Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)))
      atTop (nhds 0) := by
    have h1 : ContinuousAt Complex.arg (1 : ℂ) := Complex.continuousAt_arg (x := 1) (by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by norm_num))
    have h2 : Tendsto (fun t : ℝ => Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)))
        atTop (nhds (Complex.arg 1)) := h1.tendsto.comp hmain
    simpa only [Complex.arg_one] using h2
  have hnb : {x : ℝ | |x| < 2 * Real.pi * ϑ} ∈ nhds (0 : ℝ) := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : ℝ) (ε := 2 * Real.pi * ϑ) (by positivity)) ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    simpa using hx
  have hev1 : ∀ᶠ t : ℝ in atTop,
      |Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D))| < 2 * Real.pi * ϑ :=
    harg.eventually hnb
  have hev2 : ∀ᶠ t : ℝ in atTop, 1 < t ∧ 2 * ‖y‖ + 1 ≤ ‖Work.EL.rayPt hN θ t‖ :=
    (eventually_gt_atTop (1 : ℝ)).and
      ((Work.LandLeaves.tendsto_norm_rayPt_atTop hN θ).eventually (eventually_ge_atTop (2 * ‖y‖ + 1)))
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hev1.and hev2)
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hargt, ht1, htnorm⟩ := hT t ht
  have hne : Work.EL.rayPt hN θ t - y ≠ 0 := by
    intro h0
    have h1 : ‖Work.EL.rayPt hN θ t‖ = ‖y‖ := by rw [sub_eq_zero.mp h0]
    linarith [norm_nonneg y]
  have ht0 : (0 : ℝ) < t := by linarith
  have htC : (t : ℂ) ≠ 0 := by
    intro h
    exact absurd (Complex.ofReal_inj.mp h) (ne_of_gt ht0)
  have hden : ((t : ℂ) * D) ≠ 0 := mul_ne_zero htC hD0
  have hnum : (Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D) ≠ 0 := div_ne_zero hne hden
  have hA : (Complex.arg (Work.EL.rayPt hN θ t - y) : Real.Angle)
      = (Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) : Real.Angle)
        + (Complex.arg ((t : ℂ) * D) : Real.Angle) := by
    have h := Complex.arg_mul_coe_angle hnum hden
    rwa [div_mul_cancel₀ _ hden] at h
  have hB : (Complex.arg ((t : ℂ) * D) : Real.Angle)
      = ((2 * Real.pi * θ : ℝ) : Real.Angle) := by
    rw [Complex.arg_real_mul D ht0, hD, Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]
  have hE : (((Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D))
        + 2 * Real.pi * θ : ℝ)) : Real.Angle)
      = ((Complex.arg (Work.EL.rayPt hN θ t - y) : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    have hA' := hA
    rw [hB] at hA'
    exact hA'.symm
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hE
  refine ⟨-k, ?_⟩
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hk' : Complex.arg (Work.EL.rayPt hN θ t - y)
      = Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) + 2 * Real.pi * θ
        - 2 * Real.pi * (k : ℝ) := by
    linarith [hk]
  have hsub : (Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) + 2 * Real.pi * θ
        - 2 * Real.pi * (k : ℝ)) / (2 * Real.pi)
      - Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) / (2 * Real.pi)
      = θ + ((-k : ℤ) : ℝ) := by
    rw [div_sub_div_same]
    have hX : (Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) + 2 * Real.pi * θ
          - 2 * Real.pi * (k : ℝ))
        - Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D))
        = 2 * Real.pi * (θ + ((-k : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [hX, mul_div_cancel_left₀ _ h2pi]
  have hkey : Complex.arg (Work.EL.rayPt hN θ t - y) / (2 * Real.pi) - (θ + ((-k : ℤ) : ℝ))
      = Complex.arg ((Work.EL.rayPt hN θ t - y) / ((t : ℂ) * D)) / (2 * Real.pi) := by
    rw [hk']
    linarith
  rw [hkey]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  linarith

/-- **The directions of the level-`t` ray points tend to `2πθ`.**  For every `ϑ > 0` and every
fixed `y`, the argument of `rayPt hN θ t - y`, measured in turns, is within `ϑ` of `θ` modulo `1`
for all sufficiently large levels `t`. -/
theorem exists_int_arg_close {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) (y : ℂ) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ m : ℤ,
      |Complex.arg (Work.EL.rayPt hN θ t - y) / (2 * Real.pi) - (θ + (m : ℝ))| ≤ ϑ :=
  exists_int_arg_close_aux hN hφ θ y hϑ

end Work.LandLeaves
