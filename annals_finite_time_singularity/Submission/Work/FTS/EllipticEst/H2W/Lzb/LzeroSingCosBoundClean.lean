import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.LzeroSingDefs
import Submission.Work.FTS.EllipticEst.LzeroSingWronskian

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Lzb

open MeasureTheory

/-!
## Boundedness of `θ ↦ LzeroSing θ · cos θ` on `(0, π/2)`

`LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} I(s) ds` with `I(s) = 1/(sin s · sin(2s)²)`, so it
suffices to bound `J(θ) = ∫_{π/4}^{π/2-θ} I` from the two sides by the elementary pointwise
bounds `I(s) ≤ π²/(2 (π/2-s)²)` (for `s ≥ π/4`) and `I(s) ≤ π³/(8 s³)` (for `s ≤ π/4`),
combined with the exact evaluations of the two model integrals `∫ ds/(π/2-s)²` and `∫ ds/s³`.
-/

/-! ## Elementary positivity and integrability of the singular weight -/

/-- `LzeroSingIntegrand` is nonnegative on the open angular interval. -/
lemma LzeroSingIntegrand_nonneg {s : ℝ} (hs1 : 0 < s) (hs2 : s < Real.pi / 2) :
    0 ≤ LzeroSingIntegrand s := by
  unfold LzeroSingIntegrand
  apply div_nonneg zero_le_one
  exact le_of_lt (mul_pos (Real.sin_pos_of_pos_of_lt_pi hs1 (by linarith))
    (pow_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)) 2))

/-- `LzeroSingIntegrand` is interval-integrable on any interval contained in `(0, π/2)`. -/
lemma intervalIntegrable_LzeroSingIntegrand {a b : ℝ} (ha : 0 < min a b)
    (hb : max a b < Real.pi / 2) : IntervalIntegrable LzeroSingIntegrand volume a b := by
  refine (continuousOn_LzeroSingIntegrand.mono ?_).intervalIntegrable
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith [min_le_left a b, h1], by linarith [h2, le_max_right a b]⟩
  · exact ⟨by linarith [min_le_right a b, h1], by linarith [h2, le_max_left a b]⟩

/-! ## The two pointwise bounds on the weight -/

/-- On `[π/4, π/2)` the weight is dominated by `π²/(2 (π/2-s)²)`: there `sin s ≥ √2/2 ≥ 2/3`
and `cos s ≥ (2/π)(π/2-s)` (Jordan), so `4 sin³s cos²s ≥ (64/27)(π/2-s)²`.
(Strictly, only `s < π/2` is needed; used on subintervals of `(0, π/2)`.) -/
lemma LzeroSingIntegrand_le_left {s : ℝ} (hs1 : Real.pi / 4 ≤ s) (hs2 : s < Real.pi / 2) :
    LzeroSingIntegrand s ≤ (Real.pi ^ 2 / 2) / (Real.pi / 2 - s) ^ 2 := by
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2p : 0 < Real.sin (2 * s) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hden : 0 < Real.sin s * Real.sin (2 * s) ^ 2 := mul_pos hs0 (pow_pos hs2p 2)
  have htpos : 0 < Real.pi / 2 - s := by linarith
  unfold LzeroSingIntegrand
  rw [div_le_div_iff₀ hden (pow_pos htpos 2)]
  have hsin_ge : (2 : ℝ) / 3 ≤ Real.sin s := by
    have hsinsqrt : Real.sqrt 2 / 2 ≤ Real.sin s := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := s)
        (by linarith) (le_of_lt hs2) hs1
      rwa [Real.sin_pi_div_four] at h
    have h23 : (2 : ℝ) / 3 ≤ Real.sqrt 2 / 2 := by
      have h1 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (4 : ℝ) / 3 by norm_num)]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    linarith
  have hcos_ge : 2 / Real.pi * (Real.pi / 2 - s) ≤ Real.cos s := by
    have h := Real.mul_le_sin (x := Real.pi / 2 - s) (by linarith) (by linarith)
    rwa [Real.sin_pi_div_two_sub] at h
  have hsin_nn : 0 ≤ Real.sin s := le_of_lt hs0
  have hs2e : Real.sin (2 * s) ^ 2 = 4 * (Real.sin s) ^ 2 * (Real.cos s) ^ 2 := by
    rw [Real.sin_two_mul]; ring
  rw [hs2e, show Real.sin s * (4 * (Real.sin s) ^ 2 * (Real.cos s) ^ 2)
      = 4 * (Real.sin s) ^ 3 * (Real.cos s) ^ 2 from by ring]
  have hcube : ((2 : ℝ) / 3) ^ 3 ≤ (Real.sin s) ^ 3 := pow_le_pow_left₀ (by norm_num) hsin_ge 3
  have hb_nn : 0 ≤ 2 / Real.pi * (Real.pi / 2 - s) := by positivity
  have hsq : (2 / Real.pi * (Real.pi / 2 - s)) ^ 2 ≤ (Real.cos s) ^ 2 :=
    pow_le_pow_left₀ hb_nn hcos_ge 2
  have hprod : 4 * ((2 : ℝ) / 3) ^ 3 * (2 / Real.pi * (Real.pi / 2 - s)) ^ 2
      ≤ 4 * (Real.sin s) ^ 3 * (Real.cos s) ^ 2 := by
    have h1 : 4 * ((2 : ℝ) / 3) ^ 3 ≤ 4 * (Real.sin s) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    exact mul_le_mul h1 hsq (sq_nonneg _) (mul_nonneg (by norm_num) (pow_nonneg hsin_nn 3))
  have hconst : (Real.pi ^ 2 / 2) * (4 * ((2 : ℝ) / 3) ^ 3 * (2 / Real.pi * (Real.pi / 2 - s)) ^ 2)
      = (64 / 27) * (Real.pi / 2 - s) ^ 2 := by
    field_simp
    ring
  have hbase : (Real.pi / 2 - s) ^ 2 ≤
      (Real.pi ^ 2 / 2) * (4 * ((2 : ℝ) / 3) ^ 3 * (2 / Real.pi * (Real.pi / 2 - s)) ^ 2) := by
    rw [hconst]
    nlinarith [sq_nonneg (Real.pi / 2 - s)]
  calc (1 : ℝ) * (Real.pi / 2 - s) ^ 2 = (Real.pi / 2 - s) ^ 2 := by ring
    _ ≤ (Real.pi ^ 2 / 2) * (4 * ((2 : ℝ) / 3) ^ 3 * (2 / Real.pi * (Real.pi / 2 - s)) ^ 2) :=
        hbase
    _ ≤ (Real.pi ^ 2 / 2) * (4 * (Real.sin s) ^ 3 * (Real.cos s) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- On `(0, π/4]` the weight is dominated by `(π³/8)/s³`: there `sin s ≥ 2s/π` (Jordan) and
`cos s ≥ √2/2 ≥ 2/3`, so `4 sin³s cos²s ≥ (16/9) s³`. -/
lemma LzeroSingIntegrand_le_right {s : ℝ} (hs1 : 0 < s) (hs2 : s ≤ Real.pi / 4) :
    LzeroSingIntegrand s ≤ (Real.pi ^ 3 / 8) / s ^ 3 := by
  have hpi := Real.pi_pos
  have hslt : s < Real.pi / 2 := by linarith
  have hs0 : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs1 (by linarith)
  have hs2p : 0 < Real.sin (2 * s) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hden : 0 < Real.sin s * Real.sin (2 * s) ^ 2 := mul_pos hs0 (pow_pos hs2p 2)
  unfold LzeroSingIntegrand
  rw [div_le_div_iff₀ hden (pow_pos hs1 3)]
  have hsin_ge : 2 / Real.pi * s ≤ Real.sin s :=
    Real.mul_le_sin (x := s) (le_of_lt hs1) (by linarith)
  have hcos_ge : (2 : ℝ) / 3 ≤ Real.cos s := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := s) (y := Real.pi / 4)
      (le_of_lt hs1) (by linarith) hs2
    have h23 : (2 : ℝ) / 3 ≤ Real.sqrt 2 / 2 := by
      have h1 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (4 : ℝ) / 3 by norm_num)]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    rw [Real.cos_pi_div_four] at h
    linarith
  have hsin_nn : 0 ≤ Real.sin s := le_of_lt hs0
  have hs2e : Real.sin (2 * s) ^ 2 = 4 * (Real.sin s) ^ 2 * (Real.cos s) ^ 2 := by
    rw [Real.sin_two_mul]; ring
  rw [hs2e, show Real.sin s * (4 * (Real.sin s) ^ 2 * (Real.cos s) ^ 2)
      = 4 * (Real.sin s) ^ 3 * (Real.cos s) ^ 2 from by ring]
  have hcube : (2 / Real.pi * s) ^ 3 ≤ (Real.sin s) ^ 3 := pow_le_pow_left₀ (by positivity) hsin_ge 3
  have hsq : ((2 : ℝ) / 3) ^ 2 ≤ (Real.cos s) ^ 2 := pow_le_pow_left₀ (by norm_num) hcos_ge 2
  have hprod : 4 * (2 / Real.pi * s) ^ 3 * ((2 : ℝ) / 3) ^ 2 ≤ 4 * (Real.sin s) ^ 3 * (Real.cos s) ^ 2 := by
    have h1 : 4 * (2 / Real.pi * s) ^ 3 ≤ 4 * (Real.sin s) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    exact mul_le_mul h1 hsq (sq_nonneg _) (mul_nonneg (by norm_num) (pow_nonneg hsin_nn 3))
  have hconst : (Real.pi ^ 3 / 8) * (4 * (2 / Real.pi * s) ^ 3 * ((2 : ℝ) / 3) ^ 2)
      = (16 / 9) * s ^ 3 := by
    field_simp
    ring
  have hbase : s ^ 3 ≤ (Real.pi ^ 3 / 8) * (4 * (2 / Real.pi * s) ^ 3 * ((2 : ℝ) / 3) ^ 2) := by
    rw [hconst]; nlinarith [pow_nonneg (le_of_lt hs1) 3]
  calc (1 : ℝ) * s ^ 3 = s ^ 3 := by ring
    _ ≤ (Real.pi ^ 3 / 8) * (4 * (2 / Real.pi * s) ^ 3 * ((2 : ℝ) / 3) ^ 2) := hbase
    _ ≤ (Real.pi ^ 3 / 8) * (4 * (Real.sin s) ^ 3 * (Real.cos s) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-! ## The two model integrals -/

/-- `∫_{π/4}^{π/2-θ} ds/(π/2-s)² = 1/θ - 4/π` for `θ > 0`, by the fundamental theorem with the
antiderivative `s ↦ (π/2-s)⁻¹`. -/
lemma integral_inv_sq_pi {θ : ℝ} (hθ : 0 < θ) :
    ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ), ((Real.pi / 2 - s) ^ 2)⁻¹
      = 1 / θ - 4 / Real.pi := by
  have hpi := Real.pi_pos
  have hderiv : ∀ x ∈ Set.uIcc (Real.pi / 4) (Real.pi / 2 - θ),
      HasDerivAt (fun y => (Real.pi / 2 - y)⁻¹) (((Real.pi / 2 - x) ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    have hxlt : x < Real.pi / 2 := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    have hp : Real.pi / 2 - x ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-((Real.pi / 2 - x) ^ 2)⁻¹) (Real.pi / 2 - x) :=
      hasDerivAt_inv hp
    have h2 : HasDerivAt (fun y : ℝ => Real.pi / 2 - y) (-1) x := by
      have h := (hasDerivAt_const (x := x) (Real.pi / 2)).sub (hasDerivAt_id x)
      exact h.congr_deriv (by norm_num)
    exact (h1.comp x h2).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x : ℝ => ((Real.pi / 2 - x) ^ 2)⁻¹) volume
      (Real.pi / 4) (Real.pi / 2 - θ) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact ((continuous_const.sub continuous_id).pow 2).continuousOn
    · intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : x < Real.pi / 2 := by linarith
        positivity
      · have : x < Real.pi / 2 := by linarith
        positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ
  field_simp
  ring

/-- `∫_{π/2-θ}^{π/4} ds/s³ = 1/(2(π/2-θ)²) - 8/π²` for `θ < π/2`, by the fundamental theorem with
the antiderivative `s ↦ -(1/2) (s²)⁻¹`. -/
lemma integral_inv_cube {θ : ℝ} (hθ : θ < Real.pi / 2) :
    ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), (s ^ 3)⁻¹
      = 1 / (2 * (Real.pi / 2 - θ) ^ 2) - 8 / Real.pi ^ 2 := by
  have hpi := Real.pi_pos
  have hderiv : ∀ x ∈ Set.uIcc (Real.pi / 2 - θ) (Real.pi / 4),
      HasDerivAt (fun y => -(1 / 2) * (y ^ 2)⁻¹) ((x ^ 3)⁻¹) x := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    have hxpos : 0 < x := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x :=
      h1.inv (pow_ne_zero 2 hx0)
    have h3 : HasDerivAt (fun y : ℝ => -(1 / 2) * (y ^ 2)⁻¹)
        (-(1 / 2) * (-(2 * x) / (x ^ 2) ^ 2)) x := h2.const_mul (-(1 / 2))
    exact h3.congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 3)⁻¹) volume
      (Real.pi / 2 - θ) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact (continuous_id.pow 3).continuousOn
    · intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : 0 < x := by linarith
        positivity
      · have : 0 < x := by linarith
        positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi
  have hθne : Real.pi / 2 - θ ≠ 0 := by linarith
  field_simp
  ring

/-- **IMPORTANT — module-compatibility constraint.**  This claim must be provable from the
imports `Submission.Work.FTS.EllipticEst.LzeroSingDefs` and
`Submission.Work.FTS.EllipticEst.LzeroSingWronskian` ONLY (both already in `depends_on`).
In particular do NOT import `Submission.Work.FTS.EllipticEst.LzeroSingPole`: that module
redeclares the name `Work.FTS.EllipticEst.continuousOn_LzeroSingIntegrand`, which also lives in
`LzeroSingWronskian`, and the two together make an unimportable environment.  (Everything needed
is available: `LzeroSingIntegrand` and its continuity on `(0,π/2)` are in `LzeroSingDefs` /
`LzeroSingWronskian`.)

`θ ↦ LzeroSing θ * cos θ` is bounded on `(0, π/2)`.

`Work.FTS.EllipticEst.LzeroSing θ = sin(2θ) * ∫_{π/4}^{π/2-θ} I(s) ds` with
`I(s) = 1/(sin s * sin(2s)^2) = 1/(4 sin^3 s cos^2 s)`, so
`LzeroSing θ * cos θ = sin(2θ) cos θ * J(θ)`, `J(θ) = ∫_{π/4}^{π/2-θ} I`.

Proof sketch (no change of variables needed; only `Real.mul_le_sin` (Jordan), monotonicity of
`Real.cos` on `[0,π/2]` and interval-integral monotonicity):
* `θ ≤ π/4`: `J(θ) = ∫_{π/4}^{π/2-θ} I ≥ 0`, and on `[π/4, π/2-θ]` we have
  `sin s ≥ sin(π/4) = √2/2` and, since `π/2 - s ∈ [θ, π/4]`, Jordan gives
  `cos s = sin(π/2-s) ≥ (2/π)(π/2-s)`, so `I(s) ≤ π^2/(2 (π/2-s)^2)`; hence
  `∫_{π/4}^{π/2-θ} ds/(π/2-s)^2 = 1/θ - 4/π ≤ 1/θ`, so `J(θ) ≤ π^2/(2θ)`, while
  `sin(2θ) cos θ ≤ sin(2θ) ≤ 2θ`.
* `θ ≥ π/4`: `J(θ) = -∫_{π/2-θ}^{π/4} I`, and on `[π/2-θ, π/4]` we have `cos s ≥ √2/2` and
  `sin s ≥ 2s/π`, so `I(s) ≤ π^3/(16 s^3)`; hence `|J(θ)| ≤ π^3/32 * (π/2-θ)^{-2}`, while
  `sin(2θ) = sin(π - 2(π/2-θ)) ≤ 2(π/2-θ)` and `cos θ = sin(π/2-θ) ≤ π/2-θ`.
So both cases give an absolute bound (`π^2` resp. `π^3/16`); e.g. `C = 10` works. -/
theorem LzeroSingCosBoundClean :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ C := by
  refine ⟨100, by norm_num, ?_⟩
  intro θ hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hcos_nn : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩)
  have hsin2_nn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsc_nn : 0 ≤ Real.sin (2 * θ) * Real.cos θ := mul_nonneg hsin2_nn hcos_nn
  set J : ℝ := ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ), LzeroSingIntegrand s with hJ
  have hLS : Work.FTS.EllipticEst.LzeroSing θ = Real.sin (2 * θ) * J := rfl
  have hprod : Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ
      = (Real.sin (2 * θ) * Real.cos θ) * J := by rw [hLS]; ring
  have habs : |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ|
      = (Real.sin (2 * θ) * Real.cos θ) * |J| := by
    rw [hprod, abs_mul, abs_of_nonneg hsc_nn]
  rw [habs]
  rcases le_or_gt θ (Real.pi / 4) with hle | hlt
  · -- Case `θ ≤ π/4`: the integral runs to the right of `π/4`.
    have ha : Real.pi / 4 ≤ Real.pi / 2 - θ := by linarith
    have hII := intervalIntegrable_LzeroSingIntegrand
      (a := Real.pi / 4) (b := Real.pi / 2 - θ)
      (lt_min (by linarith [Real.pi_pos]) (by linarith [hθπ]))
      (max_lt (by linarith [Real.pi_pos]) (by linarith [hθ0]))
    have hII' : IntervalIntegrable (fun s : ℝ => (Real.pi ^ 2 / 2) / (Real.pi / 2 - s) ^ 2)
        volume (Real.pi / 4) (Real.pi / 2 - θ) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact ((continuous_const.sub continuous_id).pow 2).continuousOn
      · intro x hx
        rw [Set.mem_uIcc] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have : x < Real.pi / 2 := by linarith
          positivity
        · have : x < Real.pi / 2 := by linarith
          positivity
    have hJnn : 0 ≤ J := by
      rw [hJ]
      refine intervalIntegral.integral_nonneg ha ?_
      intro s hs
      exact LzeroSingIntegrand_nonneg (by linarith [hs.1]) (by linarith [hs.2, hθ0])
    have hmono : J ≤ (Real.pi ^ 2 / 2) * (1 / θ - 4 / Real.pi) := by
      rw [hJ]
      have h1 : ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ), LzeroSingIntegrand s
          ≤ ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ),
              (Real.pi ^ 2 / 2) / (Real.pi / 2 - s) ^ 2 := by
        refine intervalIntegral.integral_mono_on ha hII hII' ?_
        intro s hs
        exact LzeroSingIntegrand_le_left hs.1 (by linarith [hs.2, hθ0])
      have h2 : ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ),
            (Real.pi ^ 2 / 2) / (Real.pi / 2 - s) ^ 2
          = (Real.pi ^ 2 / 2) * (1 / θ - 4 / Real.pi) := by
        have hsplit : (fun s : ℝ => (Real.pi ^ 2 / 2) / (Real.pi / 2 - s) ^ 2)
            = fun s : ℝ => (Real.pi ^ 2 / 2) * ((Real.pi / 2 - s) ^ 2)⁻¹ := by
          funext s
          rw [div_eq_mul_inv]
        rw [hsplit, intervalIntegral.integral_const_mul, integral_inv_sq_pi hθ0]
      linarith
    have hJabs : |J| ≤ (Real.pi ^ 2 / 2) * (1 / θ) := by
      rw [abs_of_nonneg hJnn]
      have h4 : (1 : ℝ) / θ - 4 / Real.pi ≤ 1 / θ := by
        have h5 : 0 ≤ 4 / Real.pi := by positivity
        linarith
      exact le_trans hmono (mul_le_mul_of_nonneg_left h4 (by positivity))
    have hsc_le : Real.sin (2 * θ) * Real.cos θ ≤ 2 * θ := by
      have h1 : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
      calc Real.sin (2 * θ) * Real.cos θ ≤ (2 * θ) * Real.cos θ :=
            mul_le_mul_of_nonneg_right h1 hcos_nn
        _ ≤ (2 * θ) * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (by linarith)
        _ = 2 * θ := by ring
    have hmain : (Real.sin (2 * θ) * Real.cos θ) * |J| ≤ 100 := by
      have h4 : (Real.sin (2 * θ) * Real.cos θ) * |J|
          ≤ (2 * θ) * ((Real.pi ^ 2 / 2) * (1 / θ)) :=
        mul_le_mul hsc_le hJabs (abs_nonneg J) (by linarith)
      have h5 : (2 * θ) * ((Real.pi ^ 2 / 2) * (1 / θ)) = Real.pi ^ 2 := by
        have hθne : θ ≠ 0 := ne_of_gt hθ0
        calc (2 * θ) * ((Real.pi ^ 2 / 2) * (1 / θ)) = Real.pi ^ 2 * (θ * (1 / θ)) := by ring
          _ = Real.pi ^ 2 * 1 := by rw [mul_div_cancel₀ (1 : ℝ) hθne]
          _ = Real.pi ^ 2 := by ring
      have h7 : Real.pi ^ 2 ≤ 100 := by
        have h8 : Real.pi ^ 2 ≤ 4 ^ 2 :=
          pow_le_pow_left₀ (by linarith [Real.pi_pos]) (le_of_lt Real.pi_lt_four) 2
        norm_num at h8
        linarith
      linarith
    exact hmain
  · -- Case `π/4 < θ`: the integral runs to the left of `π/4`; reverse the orientation.
    have ha : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
    have hb : 0 < Real.pi / 2 - θ := by linarith
    have hIIp : IntervalIntegrable LzeroSingIntegrand volume (Real.pi / 2 - θ) (Real.pi / 4) :=
      intervalIntegrable_LzeroSingIntegrand (a := Real.pi / 2 - θ) (b := Real.pi / 4)
        (lt_min (by linarith [hθπ]) (by linarith [Real.pi_pos]))
        (max_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
    have hJp_nn : 0 ≤ ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), LzeroSingIntegrand s := by
      refine intervalIntegral.integral_nonneg ha ?_
      intro s hs
      exact LzeroSingIntegrand_nonneg (by linarith [hb, hs.1]) (by linarith [hs.2])
    have hJeq : J = - ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), LzeroSingIntegrand s := by
      rw [hJ, intervalIntegral.integral_symm]
    have hJabs : |J| ≤ (Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2)) := by
      have hmono : ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), LzeroSingIntegrand s
          ≤ (Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2)) := by
        have hIIp' : IntervalIntegrable (fun s : ℝ => (Real.pi ^ 3 / 8) / s ^ 3)
            volume (Real.pi / 2 - θ) (Real.pi / 4) := by
          refine ContinuousOn.intervalIntegrable ?_
          refine ContinuousOn.div continuousOn_const ?_ ?_
          · exact (continuous_id.pow 3).continuousOn
          · intro x hx
            rw [Set.mem_uIcc] at hx
            rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have : 0 < x := by linarith
              positivity
            · have : 0 < x := by linarith
              positivity
        have hm : ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), LzeroSingIntegrand s
            ≤ ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), (Real.pi ^ 3 / 8) / s ^ 3 := by
          refine intervalIntegral.integral_mono_on ha hIIp hIIp' ?_
          intro s hs
          exact LzeroSingIntegrand_le_right (by linarith [hb, hs.1]) (by linarith [hs.2])
        have hv : ∫ s in (Real.pi / 2 - θ)..(Real.pi / 4), (Real.pi ^ 3 / 8) / s ^ 3
            = (Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2) - 8 / Real.pi ^ 2) := by
          have hsplit : (fun s : ℝ => (Real.pi ^ 3 / 8) / s ^ 3)
              = fun s : ℝ => (Real.pi ^ 3 / 8) * (s ^ 3)⁻¹ := by
            funext s
            rw [div_eq_mul_inv]
          rw [hsplit, intervalIntegral.integral_const_mul, integral_inv_cube hθπ]
        have hle : (Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2) - 8 / Real.pi ^ 2)
            ≤ (Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h2 : 0 ≤ 8 / Real.pi ^ 2 := by positivity
          linarith
        linarith
      rw [hJeq, abs_neg, abs_of_nonneg hJp_nn]
      exact hmono
    have hsc_le : Real.sin (2 * θ) * Real.cos θ ≤ 2 * (Real.pi / 2 - θ) ^ 2 := by
      have hsin2eq : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
        rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring]
        exact (Real.sin_pi_sub (2 * θ)).symm
      have hcoseq : Real.cos θ = Real.sin (Real.pi / 2 - θ) :=
        (Real.sin_pi_div_two_sub θ).symm
      rw [hsin2eq, hcoseq]
      have hs1 : Real.sin (2 * (Real.pi / 2 - θ)) ≤ 2 * (Real.pi / 2 - θ) :=
        Real.sin_le (by linarith)
      have hs2 : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le (le_of_lt hb)
      have hs2nn : 0 ≤ Real.sin (Real.pi / 2 - θ) :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi hb (by linarith))
      calc Real.sin (2 * (Real.pi / 2 - θ)) * Real.sin (Real.pi / 2 - θ)
          ≤ (2 * (Real.pi / 2 - θ)) * Real.sin (Real.pi / 2 - θ) :=
            mul_le_mul_of_nonneg_right hs1 hs2nn
        _ ≤ (2 * (Real.pi / 2 - θ)) * (Real.pi / 2 - θ) :=
            mul_le_mul_of_nonneg_left hs2 (by linarith)
        _ = 2 * (Real.pi / 2 - θ) ^ 2 := by ring
    have hmain : (Real.sin (2 * θ) * Real.cos θ) * |J| ≤ 100 := by
      have h4 : (Real.sin (2 * θ) * Real.cos θ) * |J|
          ≤ (2 * (Real.pi / 2 - θ) ^ 2)
              * ((Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2))) :=
        mul_le_mul hsc_le hJabs (abs_nonneg J) (by positivity)
      have h5 : (2 * (Real.pi / 2 - θ) ^ 2)
            * ((Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2))) = Real.pi ^ 3 / 8 := by
        have ht2 : (2 : ℝ) * (Real.pi / 2 - θ) ^ 2 ≠ 0 := by positivity
        calc (2 * (Real.pi / 2 - θ) ^ 2)
              * ((Real.pi ^ 3 / 8) * (1 / (2 * (Real.pi / 2 - θ) ^ 2)))
            = (Real.pi ^ 3 / 8)
              * ((2 * (Real.pi / 2 - θ) ^ 2) * (1 / (2 * (Real.pi / 2 - θ) ^ 2))) := by ring
          _ = (Real.pi ^ 3 / 8) * 1 := by rw [mul_div_cancel₀ (1 : ℝ) ht2]
          _ = Real.pi ^ 3 / 8 := by ring
      have h7 : Real.pi ^ 3 / 8 ≤ 100 := by
        have h8 : Real.pi ^ 3 ≤ 4 ^ 3 :=
          pow_le_pow_left₀ (by linarith [Real.pi_pos]) (le_of_lt Real.pi_lt_four) 3
        norm_num at h8
        linarith
      linarith
    exact hmain

end Work.FTS.EllipticEst.H2W.Lzb
