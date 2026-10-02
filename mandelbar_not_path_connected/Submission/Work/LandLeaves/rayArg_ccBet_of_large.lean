import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.ELTop.Defs
import Submission.Work.LandLeaves.gmLocalOrder
import Submission.Work.LandLeaves.ccBet_perturb

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The large-level regime of the local order at a landing point

For `θ ∈ ℝ` and a point `y`, let `p_θ(t) = Work.EL.rayPt hN θ t` be the point of level `t` of the
dynamic ray of angle `θ`.  Since the Böttcher coordinate is asymptotic to the identity at infinity
(`Work.ParamRays.IsDynBottcher`, third clause: `‖φ z - z‖ ≤ ε ‖z‖` for `z` outside a compact set)
and `φ (p_θ(t)) = t · e^{2πiθ}`, the level-`t` ray points are asymptotic to the radial lines
`t ↦ t e^{2πiθ}`:

  `p_θ(t) / (t e^{2πiθ}) → 1`  as `t → ∞`,

and consequently the *directions* of the ray points as seen from the fixed point `y` tend to the
angle directions: for every `ϑ > 0` and all large `t` there is an integer `m` with

  `|arg (p_θ(t) - y) / (2π) - (θ + m)| ≤ ϑ`.

Combining this asymptotic with the perturbation stability of the cyclic betweenness
`Work.LandLeaves.ccBet_perturb` (`ccBet` is locally constant wherever the three angles keep a
positive distance from each other on the circle) gives the *large-level half* of the local-order
dichotomy: the cyclic order of the three directions as seen from `y` is, for all large levels,
the cyclic order of the angles.

## Main result

* `Work.LandLeaves.rayArg_ccBet_of_large`.
-/

open Classical Filter
open scoped Topology

namespace Work.LandLeaves

noncomputable section

set_option linter.unusedVariables false

/-! ## Arithmetic of `Int.fract`: independent integer shifts -/

/-- `ccBet` is invariant under shifting the three arguments by *independent* integers (the
`Int.fract`'s in its definition depend only on the residue classes of the differences). -/
theorem ccBet_add_int_three (a b x : ℝ) (m n p : ℤ) :
    ccBet (a + m) (b + n) (x + p) ↔ ccBet a b x := by
  have h1 : x + (p : ℝ) - (a + (m : ℝ)) = (x - a) + ((p - m : ℤ) : ℝ) := by push_cast; ring
  have h2 : b + (n : ℝ) - (a + (m : ℝ)) = (b - a) + ((n - m : ℤ) : ℝ) := by push_cast; ring
  simp only [ccBet, h1, h2, Int.fract_add_intCast]

/-- The distance of a real number from the integers is at least the smaller of its fractional
part and the complement of the latter. -/
private theorem min_fract_le_abs_sub_int (x : ℝ) (m : ℤ) :
    min (Int.fract x) (1 - Int.fract x) ≤ |x - m| := by
  have hx : x - (m : ℝ) = Int.fract x + ((⌊x⌋ - m : ℤ) : ℝ) := by
    have := Int.fract_add_floor x
    push_cast
    linarith
  rw [hx]
  by_cases hj : 0 ≤ (((⌊x⌋ - m : ℤ) : ℝ))
  · have h0 : 0 ≤ Int.fract x + ((⌊x⌋ - m : ℤ) : ℝ) := by linarith [Int.fract_nonneg x]
    rw [abs_of_nonneg h0]
    exact le_trans (min_le_left _ _) (by linarith [Int.fract_nonneg x])
  · have hlt : ((⌊x⌋ - m : ℤ) : ℝ) < 0 := lt_of_not_ge hj
    have hj' : (⌊x⌋ - m : ℤ) ≤ -1 := by
      have hneg : (⌊x⌋ - m : ℤ) < 0 := by exact_mod_cast hlt
      omega
    have hcast : ((⌊x⌋ - m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hj'
    have h0 : Int.fract x + ((⌊x⌋ - m : ℤ) : ℝ) < 0 := by
      have := Int.fract_lt_one x
      linarith
    rw [abs_of_neg h0]
    exact le_trans (min_le_right _ _) (by linarith)

/-- Three angles in the cyclic betweenness relation keep a *uniform* positive distance from the
integers: this is the separation hypothesis consumed by `Work.LandLeaves.ccBet_perturb`. -/
private theorem gap_of_ccBet {u v w : ℝ} (h : ccBet u v w) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ m : ℤ, δ ≤ |u - v - m|) ∧ (∀ m : ℤ, δ ≤ |v - w - m|) ∧
      (∀ m : ℤ, δ ≤ |w - u - m|) := by
  have hp0 : 0 < Int.fract (w - u) := h.1
  have hpq : Int.fract (w - u) < Int.fract (v - u) := h.2
  have hq0 : 0 < Int.fract (v - u) := lt_trans hp0 hpq
  have hq1 : Int.fract (v - u) < 1 := Int.fract_lt_one _
  have hp1 : Int.fract (w - u) < 1 := lt_trans hpq hq1
  have hqp0 : 0 < Int.fract (v - u) - Int.fract (w - u) := by linarith
  have hqp1 : Int.fract (v - u) - Int.fract (w - u) < 1 := by linarith
  -- the fractional part of `v - w`
  have hvw : Int.fract (v - w) = Int.fract (v - u) - Int.fract (w - u) := by
    have key : Int.fract (v - w)
        = Int.fract (Int.fract (v - u) - Int.fract (w - u)) := by
      have h1 : Int.fract (v - w) = Int.fract ((v - u) - Int.fract (w - u)) := by
        rw [Int.fract_sub_fract]
        congr 1
        ring
      have h2 : Int.fract ((v - u) - Int.fract (w - u))
          = Int.fract (Int.fract (v - u) - Int.fract (w - u)) := by
        rw [show (v - u) - Int.fract (w - u)
            = (Int.fract (v - u) - Int.fract (w - u)) + ((⌊v - u⌋ : ℤ) : ℝ) by
          have := Int.fract_add_floor (v - u)
          push_cast
          linarith]
        rw [Int.fract_add_intCast]
      rw [h1, h2]
    rw [key, Int.fract_eq_self.mpr ⟨le_of_lt hqp0, hqp1⟩]
  set δ : ℝ := min (min (Int.fract (w - u)) (1 - Int.fract (w - u)))
      (min (min (Int.fract (v - u)) (1 - Int.fract (v - u)))
        (min (Int.fract (v - u) - Int.fract (w - u))
          (1 - (Int.fract (v - u) - Int.fract (w - u))))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (lt_min hp0 (by linarith)) (lt_min (lt_min hq0 (by linarith))
      (lt_min hqp0 (by linarith)))
  refine ⟨δ, hδpos, ?_, ?_, ?_⟩
  · -- `u - v`
    intro m
    have hle : min (Int.fract (v - u)) (1 - Int.fract (v - u)) ≤ |u - v - m| := by
      have h := min_fract_le_abs_sub_int (v - u) (-m)
      have heq : (v - u) - (((-m : ℤ)) : ℝ) = -(u - v - m) := by push_cast; ring
      rw [heq, abs_neg] at h
      exact h
    have hδle : δ ≤ min (Int.fract (v - u)) (1 - Int.fract (v - u)) := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    exact le_trans hδle hle
  · -- `v - w`
    intro m
    have hle : min (Int.fract (v - u) - Int.fract (w - u))
        (1 - (Int.fract (v - u) - Int.fract (w - u))) ≤ |v - w - m| := by
      rw [← hvw]
      exact min_fract_le_abs_sub_int (v - w) m
    have hδle : δ ≤ min (Int.fract (v - u) - Int.fract (w - u))
        (1 - (Int.fract (v - u) - Int.fract (w - u))) := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact le_trans hδle hle
  · -- `w - u`
    intro m
    have hδle : δ ≤ min (Int.fract (w - u)) (1 - Int.fract (w - u)) := by
      rw [hδ]
      exact min_le_left _ _
    exact le_trans hδle (min_fract_le_abs_sub_int (w - u) m)

/-! ## The asymptotic of the ray points at large level -/

private theorem tendsto_norm_rayPt_atTop_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (θ : ℝ) :
    Tendsto (fun t : ℝ => ‖Work.EL.rayPt hN θ t‖) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  by_cases hR : R ≤ 0
  · exact Eventually.of_forall fun t => le_trans hR (norm_nonneg _)
  · have hRpos : 0 < R := lt_of_not_ge hR
    obtain ⟨z₀, -, hmax⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
      ⟨0, by rw [Metric.mem_closedBall, dist_zero_right, norm_zero]; exact hRpos.le⟩
      hN.continuous_potential.continuousOn
    refine eventually_atTop.mpr ⟨max (Real.exp (Work.EL.pot hN z₀) + 1) 2, fun t ht => ?_⟩
    by_contra hcon
    push_neg at hcon
    have ht1 : 1 < t := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) ht)
    have hmem : Work.EL.rayPt hN θ t ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hcon
    have h1 : Work.EL.pot hN (Work.EL.rayPt hN θ t) ≤ Work.EL.pot hN z₀ := hmax hmem
    have h2 : Work.EL.pot hN (Work.EL.rayPt hN θ t) = Real.log t := Work.EL.pot_rayPt hN ht1
    have h3 : Work.EL.pot hN z₀ < Real.log t := by
      have ht0 : 0 < t := by linarith
      have hlt : Real.exp (Work.EL.pot hN z₀) < t :=
        lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_left _ _) ht)
      exact (Real.lt_log_iff_exp_lt ht0).mpr hlt
    linarith

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
      simpa only [dist_zero_right] using tendsto_norm_rayPt_atTop_aux hN θ)
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
      ((tendsto_norm_rayPt_atTop_aux hN θ).eventually (eventually_ge_atTop (2 * ‖y‖ + 1)))
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

/-! ## The large-level betweenness of the arguments -/

/-- **The large-level regime of the local order.** Far from the landing point the external rays are asymptotic to the radial lines `t ↦ t e^{2πiθ}` (the normalisation `φ z ~ z` of the Böttcher coordinate, `hN.Phi_rayPt`), hence for large levels the *directions* of the three level-`t` points as seen from `y` are in the same counterclockwise order as their angles. This is the provable half of the local-order dichotomy: it determines the value of the (eventually constant) local order, so a proof of eventual constancy near `t = 1` yields the first disjunct of `Work.LandLeaves.localOrderDichotomy_crux`. -/
theorem rayArg_ccBet_of_large {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {hN : Work.EL.DynB c φ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {u v w : ℝ} (hu : Work.Landing.rayAccum c φ u = {y})
    (hv : Work.Landing.rayAccum c φ v = {y}) (hw : Work.Landing.rayAccum c φ w = {y})
    (h : Work.LandLeaves.ccBet u v w) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      Work.LandLeaves.ccBet (Complex.arg (Work.EL.rayPt hN u t - y) / (2 * Real.pi))
        (Complex.arg (Work.EL.rayPt hN v t - y) / (2 * Real.pi))
        (Complex.arg (Work.EL.rayPt hN w t - y) / (2 * Real.pi)) := by
  obtain ⟨δ, hδpos, huv, hvw, hwu⟩ := gap_of_ccBet h
  have hϑpos : (0 : ℝ) < δ / 4 := by linarith
  have h3 : 3 * (δ / 4) < δ := by linarith
  obtain ⟨Tu, hTu⟩ := exists_int_arg_close_aux hN hφ u y hϑpos
  obtain ⟨Tv, hTv⟩ := exists_int_arg_close_aux hN hφ v y hϑpos
  obtain ⟨Tw, hTw⟩ := exists_int_arg_close_aux hN hφ w y hϑpos
  refine ⟨max Tu (max Tv Tw), fun t ht => ?_⟩
  have htu : Tu ≤ t := le_trans (le_max_left _ _) ht
  have htv : Tv ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htw : Tw ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  obtain ⟨mu, hmu⟩ := hTu t htu
  obtain ⟨mv, hmv⟩ := hTv t htv
  obtain ⟨mw, hmw⟩ := hTw t htw
  set Au : ℝ := Complex.arg (Work.EL.rayPt hN u t - y) / (2 * Real.pi) with hAu
  set Av : ℝ := Complex.arg (Work.EL.rayPt hN v t - y) / (2 * Real.pi) with hAv
  set Aw : ℝ := Complex.arg (Work.EL.rayPt hN w t - y) / (2 * Real.pi) with hAw
  -- the integer shifts are invisible to `ccBet`
  have hshift : ccBet Au Av Aw ↔ ccBet (Au - (mu : ℝ)) (Av - (mv : ℝ)) (Aw - (mw : ℝ)) := by
    have h1 := ccBet_add_int_three (Au - (mu : ℝ)) (Av - (mv : ℝ)) (Aw - (mw : ℝ)) mu mv mw
    simpa only [sub_add_cancel] using h1
  -- the perturbations are small, so `ccBet` is preserved
  have hclose := ccBet_perturb (a := u) (b := v) (x := w) (ϑ := δ / 4) (δ := δ)
    (le_of_lt hϑpos) h3 huv hvw hwu
  have hmain : ccBet (Au - (mu : ℝ)) (Av - (mv : ℝ)) (Aw - (mw : ℝ)) := by
    have h1 : |Au - (mu : ℝ) - u| ≤ δ / 4 := by
      have : Au - (mu : ℝ) - u = Au - (u + (mu : ℝ)) := by ring
      rw [this]
      exact hmu
    have h2 : |Av - (mv : ℝ) - v| ≤ δ / 4 := by
      have : Av - (mv : ℝ) - v = Av - (v + (mv : ℝ)) := by ring
      rw [this]
      exact hmv
    have h3' : |Aw - (mw : ℝ) - w| ≤ δ / 4 := by
      have : Aw - (mw : ℝ) - w = Aw - (w + (mw : ℝ)) := by ring
      rw [this]
      exact hmw
    have hthis := (hclose (Au - (mu : ℝ) - u) (Av - (mv : ℝ) - v) (Aw - (mw : ℝ) - w)
      h1 h2 h3').mp h
    convert hthis using 1 <;> ring
  exact hshift.mpr hmain

end

end Work.LandLeaves
