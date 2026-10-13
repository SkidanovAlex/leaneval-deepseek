import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise bounds for the fundamental profile `F_* = Fstar (3α)`

The reference profile of Elgindi's construction is `F_* = Fstar (3α)`, i.e.
`F_*(z,θ) = 3α · (Γ(θ)/c(3α)) · 2z/(1+z)²` with `Γ(θ) = (sin θ cos²θ)^α` (because
`Gam (3α) θ = (sin θ cos²θ)^((3α)/3) = (sin θ cos²θ)^α`) and `c(3α) ∈ [1/10, 10]`.

This module proves the three pointwise bounds of the *firing* of `F_*` into the physical
vorticity: the sup bound, the `z`-derivative bound, and the angular-derivative bound with the
singular weights `sin^{α-1}θ · cos^{2α-1}θ`, for `0 < α ≤ 1/3`.

The route: on `Iθ` the base `u = sin θ cos²θ` lies in `[0,1]` and `2z/(1+z)² ≤ 1/2` for
`z ≥ 0`, so `|F_*| ≤ 3α·10·1/2 = 15α`; the `z`-derivative is
`3α(Γ/c)·2(1-z)/(1+z)³` with `|2(1-z)/(1+z)³| ≤ 2`, giving `≤ 3α·10·2 = 60α`; and the
angular derivative is `3α·(2z/(1+z)²)/c · ∂_θΓ`, with (on the open quadrant)
`∂_θΓ = α·q(θ)·Γ/sin(2θ)` (`dthU_Gam`) where `q = cos2θ - 1/3` satisfies `|q| ≤ 4/3` and
`Γ/sin(2θ) = (1/2)·sin^{α-1}θ·cos^{2α-1}θ`, giving `≤ 3α·(1/2)·10·(2/3)α·(…) = 10α²·(…)`.

At the endpoints `θ = 0, π/2` the angular profile is `sin^αθ` resp. `cos^{2α}θ`-like, which is
*not* differentiable there (for `α < 1` resp. `2α < 1`); since Mathlib's `deriv` is `0` at
points of non-differentiability, the angular derivative vanishes at the endpoints, where the
right-hand side also vanishes.
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped Real

namespace Work.FTS.FireFix.Clauses

/-! ## The angular profile `Γ(3α) = (sin θ cos²θ)^α` -/

/-- `Γ(3α) = (sin θ cos²θ)^α`: the exponent of `Gam` is `(3α)/3 = α`. -/
theorem gam_three (α θ : ℝ) :
    Work.Spaces.Gam (3 * α) θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := by
  rw [Work.Spaces.Gam]
  congr 1
  ring

/-- The auxiliary angular coefficient `q(θ) = cos(2θ) - 1/3` of `D_θΓ = α q Γ` is bounded by
`4/3`. -/
theorem qfun_abs_le {θ : ℝ} : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply, abs_le]
  constructor <;> nlinarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]

/-- On the open quadrant, `Γ(3α) θ = sin^αθ · cos^{2α}θ`. -/
theorem gam_three_eq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Gam (3 * α) θ = (Real.sin θ) ^ α * (Real.cos θ) ^ (2 * α) := by
  have hs : 0 ≤ Real.sin θ :=
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le
  have hc : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
  have hc2 : (Real.cos θ ^ 2) ^ α = (Real.cos θ) ^ (2 * α) := by
    rw [← Real.rpow_two (Real.cos θ), ← Real.rpow_mul hc (2 : ℝ) α]
  rw [gam_three, Real.mul_rpow hs (by positivity), hc2]

/-! ## The angular derivative of `Γ(3α)` on the open quadrant -/

/-- On the open quadrant `(0, π/2)` the angular derivative of `Γ(3α)` is bounded by
`2α sin^{α-1}θ cos^{2α-1}θ`. -/
theorem deriv_gam_three_bound {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |deriv (fun t : ℝ => Work.Spaces.Gam (3 * α) t) θ|
      ≤ 2 * α * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by
  have hα3 : 0 < 3 * α := by linarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hG0 : 0 ≤ Work.Spaces.Gam (3 * α) θ :=
    Real.rpow_nonneg (mul_nonneg hs.le (sq_nonneg _)) _
  have hdth := Work.Spaces.dthU_Gam (3 * α) θ hα3 hθ
  rw [Work.Spaces.dthU_apply] at hdth
  have hderiv : deriv (fun t : ℝ => Work.Spaces.Gam (3 * α) t) θ
      = 3 * α * Work.Spaces.qfun θ * Work.Spaces.Gam (3 * α) θ / Real.sin (2 * θ) := by
    rw [eq_div_iff (ne_of_gt hs2), mul_comm]
    exact hdth
  have hGid := gam_three_eq (α := α) (θ := θ) hθ
  have e1 : (Real.sin θ) ^ α = (Real.sin θ) ^ (α - 1) * Real.sin θ := by
    conv_lhs => rw [show α = (α - 1) + 1 from by ring]
    rw [Real.rpow_add hs (α - 1) 1, Real.rpow_one]
  have e2 : (Real.cos θ) ^ (2 * α) = (Real.cos θ) ^ (2 * α - 1) * Real.cos θ := by
    conv_lhs => rw [show 2 * α = (2 * α - 1) + 1 from by ring]
    rw [Real.rpow_add hc (2 * α - 1) 1, Real.rpow_one]
  have hA : 0 ≤ (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hc.le _)
  have hkey : 3 * α * |Work.Spaces.qfun θ| ≤ 4 * α := by
    nlinarith [qfun_abs_le (θ := θ), hα, abs_nonneg (Work.Spaces.qfun θ)]
  rw [hderiv, abs_div, abs_of_pos hs2, abs_mul, abs_mul, abs_of_pos hα3, abs_of_nonneg hG0,
    div_le_iff₀ hs2, hGid, e1, e2, Real.sin_two_mul]
  have hB : 0 ≤ Real.sin θ * Real.cos θ := mul_nonneg hs.le hc.le
  nlinarith [hkey, hA, hB, mul_nonneg hA hB]

/-! ## Non-differentiability of `(sin t cos²t)^p` and `(cos t sin²t)^p` at `0`

Both functions have a cusp at `t = 0` (`t^p` resp. `t^{2p}` behaviour), hence Mathlib's
`deriv` (which is `0` at points of non-differentiability) vanishes there. This is what makes
the endpoint cases `θ = 0` and `θ = π/2` of the angular bound trivial. -/

/-- If `φ` vanishes at `0` and is bounded below by `c t^m` near `0⁺` with `m p < 1`, then
`t ↦ φ t ^ p` is not differentiable at `0`: its difference quotient dominates
`c^p t^{mp-1} → +∞`. -/
theorem not_differentiableAt_rpow_of_eventually_ge {φ : ℝ → ℝ} {c p m : ℝ}
    (hφ0 : φ 0 = 0) (hc : 0 < c) (hp : 0 < p) (hmp : m * p < 1)
    (hφ : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), c * t ^ m ≤ φ t) :
    ¬ DifferentiableAt ℝ (fun t => φ t ^ p) 0 := by
  intro hdiff
  have hslope : Tendsto (fun t => φ t ^ p / t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (deriv (fun t => φ t ^ p) 0)) := by
    have h := hdiff.hasDerivAt.tendsto_slope_zero_right
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, hφ0, sub_zero, smul_eq_mul, Real.zero_rpow hp.ne']
    ring
  have hlow : Tendsto (fun t => c ^ p * t ^ (m * p - 1)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Filter.Tendsto.const_mul_atTop (Real.rpow_pos_of_pos hc p)
      (tendsto_rpow_neg_nhdsGT_zero (by linarith))
  have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), c ^ p * t ^ (m * p - 1) ≤ φ t ^ p / t := by
    filter_upwards [hφ, self_mem_nhdsWithin] with t hle ht
    have ht0 : 0 < t := ht
    have h1 : (c * t ^ m) ^ p ≤ (φ t) ^ p :=
      Real.rpow_le_rpow (by positivity) hle hp.le
    have h2 : (c * t ^ m) ^ p = c ^ p * t ^ (m * p) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg ht0.le m), Real.rpow_mul ht0.le m p]
    rw [h2] at h1
    have h3 : c ^ p * t ^ (m * p) / t = c ^ p * t ^ (m * p - 1) := by
      rw [Real.rpow_sub ht0 (m * p) 1, Real.rpow_one]
      ring
    rw [← h3]
    exact div_le_div_of_nonneg_right h1 ht0.le
  have hbig : Tendsto (fun t => φ t ^ p / t) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    rw [Filter.tendsto_atTop] at hlow ⊢
    intro b
    filter_upwards [hlow b, hev] with t hb hle
    linarith
  exact not_tendsto_nhds_of_tendsto_atTop hbig _ hslope

/-- `sin t / t → 1` at `0⁺` (the difference quotient of `sin` at `0`). -/
theorem sin_div_tendsto_zero :
    Tendsto (fun t : ℝ => Real.sin t / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  rw [Real.cos_zero] at h
  refine h.congr' ?_
  filter_upwards with t
  simp only [zero_add, Real.sin_zero, sub_zero, smul_eq_mul]
  ring

/-- `cos t → 1` at `0⁺`. -/
theorem cos_tendsto_zero : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h0 : Tendsto Real.cos (nhds 0) (nhds 1) := by
    rw [← Real.cos_zero]
    exact Real.continuous_cos.continuousAt (x := 0)
  exact h0.mono_left inf_le_left

/-- `cos²t → 1` at `0⁺`. -/
theorem cos_sq_tendsto_zero :
    Tendsto (fun t : ℝ => Real.cos t ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := cos_tendsto_zero
  simpa using h.pow 2

/-- `t ↦ (sin t cos²t)^p` is not differentiable at `0` for `0 < p < 1` (`sin t cos²t ∼ t`). -/
theorem not_differentiableAt_sinCosSq_rpow {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ p) 0 := by
  refine not_differentiableAt_rpow_of_eventually_ge
    (φ := fun t => Real.sin t * Real.cos t ^ 2) (c := 1 / 4) (m := 1)
    (by norm_num) (by norm_num) hp (by linarith) ?_
  filter_upwards [sin_div_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    cos_sq_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with t h1 h2 ht
  have ht0 : 0 < t := ht
  have hs : t / 2 < Real.sin t := by
    have := (lt_div_iff₀ ht0).mp h1
    linarith
  have hs' : 0 < Real.sin t := by linarith
  have hA : Real.sin t * (1 / 2) < Real.sin t * Real.cos t ^ 2 := mul_lt_mul_of_pos_left h2 hs'
  have hB : t / 2 * (1 / 2) < Real.sin t * (1 / 2) := mul_lt_mul_of_pos_right hs (by norm_num)
  rw [Real.rpow_one]
  nlinarith [hA, hB]

/-- `t ↦ (cos t sin²t)^p` is not differentiable at `0` for `0 < p` and `2p < 1`
(`cos t sin²t ∼ t²`). -/
theorem not_differentiableAt_cosSinSq_rpow {p : ℝ} (hp : 0 < p) (hp2 : 2 * p < 1) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => (Real.cos t * Real.sin t ^ 2) ^ p) 0 := by
  refine not_differentiableAt_rpow_of_eventually_ge
    (φ := fun t => Real.cos t * Real.sin t ^ 2) (c := 1 / 8) (m := 2)
    (by norm_num) (by norm_num) hp (by linarith) ?_
  filter_upwards [sin_div_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    cos_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with t h1 h2 ht
  have ht0 : 0 < t := ht
  have hs : t / 2 < Real.sin t := by
    have := (lt_div_iff₀ ht0).mp h1
    linarith
  have hs' : 0 < Real.sin t := by linarith
  have hA : t / 2 * (t / 2) < Real.sin t * Real.sin t := by nlinarith [hs, hs']
  have hB : Real.cos t * (t / 2 * (t / 2)) < Real.cos t * (Real.sin t * Real.sin t) :=
    mul_lt_mul_of_pos_left hA (by linarith)
  rw [Real.rpow_two]
  nlinarith [hB]

/-! ## The endpoint values of the angular derivative -/

/-- `∂_θ (sin θ cos²θ)^α = 0` at `θ = 0` for `0 < α < 1`. -/
theorem deriv_sinCosSq_rpow_zero {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) 0 = 0 :=
  deriv_zero_of_not_differentiableAt (not_differentiableAt_sinCosSq_rpow hα hα1)

/-- The shifted profile `t ↦ (sin t cos²t)^α` equals `s ↦ (cos s sin²s)^α` composed with
`t ↦ π/2 - t`; hence it is not differentiable at `π/2`. -/
theorem deriv_gam_three_piHalf {α : ℝ} (hα : 0 < α) (hα2 : 2 * α < 1) :
    deriv (fun t : ℝ => Work.Spaces.Gam (3 * α) t) (π / 2) = 0 := by
  have hfun : (fun t : ℝ => Work.Spaces.Gam (3 * α) t)
      = fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α := funext fun t => gam_three α t
  have hshift : (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α)
      = fun t : ℝ => (Real.cos (π / 2 - t) * Real.sin (π / 2 - t) ^ 2) ^ α := by
    funext t
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [hfun, hshift]
  apply deriv_zero_of_not_differentiableAt
  have hcomp : (fun t : ℝ => (Real.cos (π / 2 - t) * Real.sin (π / 2 - t) ^ 2) ^ α)
      = (fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α) ∘ (fun t : ℝ => π / 2 - t) := rfl
  rw [hcomp]
  intro hd
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α) 0 := by
    have h1 : DifferentiableAt ℝ (((fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α)
        ∘ (fun t : ℝ => π / 2 - t)) ∘ (fun t : ℝ => π / 2 - t)) 0 :=
      DifferentiableAt.comp (x := 0) (by simpa using hd) (by fun_prop)
    have heq : (((fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α)
        ∘ (fun t : ℝ => π / 2 - t)) ∘ (fun t : ℝ => π / 2 - t))
        = (fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α) := by
      funext s
      simp only [Function.comp_apply]
      rw [show π / 2 - (π / 2 - s) = s from by ring]
    rwa [heq] at h1
  exact not_differentiableAt_cosSinSq_rpow hα hα2 hdiff

/-- `∂_θ (sin θ cos²θ)^α = 0` at `θ = π/2` for `2α < 1`. -/
theorem deriv_sinCosSq_rpow_piHalf {α : ℝ} (hα : 0 < α) (hα2 : 2 * α < 1) :
    deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) (π / 2) = 0 := by
  have hfun : (fun t : ℝ => Work.Spaces.Gam (3 * α) t)
      = fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α := funext fun t => gam_three α t
  rw [← hfun]
  exact deriv_gam_three_piHalf hα hα2

/-- The angular derivative bound in terms of the profile `t ↦ (sin t cos²t)^α`. -/
theorem deriv_sinCosSq_rpow_bound {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) θ|
      ≤ 2 * α * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by
  have hfun : (fun t : ℝ => Work.Spaces.Gam (3 * α) t)
      = fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α := funext fun t => gam_three α t
  rw [← hfun]
  exact deriv_gam_three_bound hα hθ

/-! ## Bounds for the radial profile `F_{*,rad}(z) = 2z/(1+z)²` -/

/-- `2z/(1+z)² ≥ 0` for `z ≥ 0`. -/
theorem fm_fstar_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FM.Fstar z := by
  rw [Work.FM.Fstar]; positivity

/-- `2z/(1+z)² ≤ 1/2` for `z ≥ 0`. -/
theorem fm_fstar_le_half {z : ℝ} (hz : 0 ≤ z) : Work.FM.Fstar z ≤ 1 / 2 := by
  rw [Work.FM.Fstar, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-- `|∂_z (2z/(1+z)²)| = |2(1-z)/(1+z)³| ≤ 2` for `z ≥ 0`. -/
theorem abs_deriv_fm_fstar_le {z : ℝ} (hz : 0 ≤ z) : |deriv Work.FM.Fstar z| ≤ 2 := by
  have h1z : (-1 : ℝ) < z := by linarith
  rw [Work.FM.deriv_Fstar z h1z]
  have h3 : 0 < (1 + z) ^ 3 := by positivity
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h3, div_le_iff₀ h3]
  have h4 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  have h5 : (1 : ℝ) + z ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg z, hz]
  nlinarith [h4, h5]

/-- **The bounds for the fundamental profile `F_* = Fstar (3α)`.**  For `0 < α ≤ 1/3` the
profile and its `z`-derivative are bounded by `60α`, and its angular derivative by
`200α² sin^{α-1}θ cos^{2α-1}θ`, on `z ≥ 0`, `θ ∈ Iθ`. -/
theorem Fstar_bounds {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Fstar (3 * α) z θ| ≤ 60 * α) ∧
      (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |deriv (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ) z| ≤ 60 * α) ∧
      (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |deriv (fun θ' : ℝ => Work.Construction.Fstar (3 * α) z θ') θ|
          ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)) := by
  have hα3 : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c (3 * α) :=
    (Work.Spaces.c_bounds (3 * α) hα3 h3α1).1
  have hc0 : 0 < Work.Spaces.c (3 * α) := by linarith
  have hα1 : α < 1 := by linarith
  have hα2 : 2 * α < 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- the sup bound
    intro z θ hz hθ
    have hF0 : 0 ≤ Work.FM.Fstar z := fm_fstar_nonneg hz
    have hF1 : Work.FM.Fstar z ≤ 1 / 2 := fm_fstar_le_half hz
    have hK0 : 0 ≤ 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) := by positivity
    have hK1 : 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) ≤ 15 * α := by
      rw [div_le_iff₀ hc0]
      nlinarith [hF1, hc10, hF0, hα]
    have hB0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).1
    have hB1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).2
    have hBle : (Real.sin θ * Real.cos θ ^ 2) ^ α ≤ 1 := Real.rpow_le_one hB0 hB1 hα.le
    have hBnn : 0 ≤ (Real.sin θ * Real.cos θ ^ 2) ^ α := Real.rpow_nonneg hB0 α
    have hfac : Work.Construction.Fstar (3 * α) z θ
        = (3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α))
            * (Real.sin θ * Real.cos θ ^ 2) ^ α := by
      rw [Work.Construction.Fstar, gam_three]; ring
    rw [hfac, abs_mul, abs_of_nonneg hK0, abs_of_nonneg hBnn]
    calc 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α)
          * (Real.sin θ * Real.cos θ ^ 2) ^ α
        ≤ 15 * α * 1 := mul_le_mul hK1 hBle hBnn (by linarith)
      _ = 15 * α := by ring
      _ ≤ 60 * α := by linarith
  · -- the `z`-derivative bound
    intro z θ hz hθ
    have hG0 : 0 ≤ Work.Spaces.Gam (3 * α) θ := (Work.Spaces.Gam_bounds (3 * α) θ hα3 hθ).1
    have hG1 : Work.Spaces.Gam (3 * α) θ ≤ 1 := (Work.Spaces.Gam_bounds (3 * α) θ hα3 hθ).2
    have hK0 : 0 ≤ 3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) := by positivity
    have hKle : 3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) ≤ 3 * α * 10 := by
      have h1 : Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α) ≤ 10 := by
        rw [div_le_iff₀ hc0]; nlinarith [hG1, hc10]
      nlinarith [h1, hα]
    have hfun : (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)
        = fun z' => (3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)))
            * Work.FM.Fstar z' := by
      funext z'; rw [Work.Construction.Fstar]
    rw [hfun, deriv_const_mul_field, abs_mul, abs_of_nonneg hK0]
    calc 3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) * |deriv Work.FM.Fstar z|
        ≤ 3 * α * 10 * 2 :=
          mul_le_mul hKle (abs_deriv_fm_fstar_le hz) (abs_nonneg _) (by linarith)
      _ = 60 * α := by ring
  · -- the angular-derivative bound
    intro z θ hz hθ
    have hF0 : 0 ≤ Work.FM.Fstar z := fm_fstar_nonneg hz
    have hF1 : Work.FM.Fstar z ≤ 1 / 2 := fm_fstar_le_half hz
    have hK0 : 0 ≤ 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) := by positivity
    have hKle : 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) ≤ 15 * α := by
      rw [div_le_iff₀ hc0]
      nlinarith [hF1, hc10, hF0, hα]
    have hfun : (fun θ' : ℝ => Work.Construction.Fstar (3 * α) z θ')
        = fun θ' => (3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α))
            * (Real.sin θ' * Real.cos θ' ^ 2) ^ α := by
      funext θ'; rw [Work.Construction.Fstar, gam_three]; ring
    rw [hfun, deriv_const_mul_field, abs_mul, abs_of_nonneg hK0]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · -- `θ = 0`: the angular derivative vanishes
      rw [← h0, deriv_sinCosSq_rpow_zero hα hα1]
      have hz0 : (0 : ℝ) ^ (α - 1) = 0 := Real.zero_rpow (by linarith)
      simp [Real.sin_zero, Real.cos_zero, hz0]
    · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
      · -- `θ = π/2`: the angular derivative vanishes
        rw [hpi, deriv_sinCosSq_rpow_piHalf hα hα2]
        have hz0 : (0 : ℝ) ^ (2 * α - 1) = 0 := Real.zero_rpow (by linarith)
        simp [Real.sin_pi_div_two, Real.cos_pi_div_two, hz0]
      · -- `0 < θ < π/2`: the honest bound
        have hθ' : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, hpi⟩
        have hb := deriv_sinCosSq_rpow_bound hα hθ'
        have hs1 : 0 ≤ (Real.sin θ) ^ (α - 1) :=
          Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2]⟩) _
        have hc1 : 0 ≤ (Real.cos θ) ^ (2 * α - 1) :=
          Real.rpow_nonneg (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [Real.pi_pos]⟩) _
        calc 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α)
              * |deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) θ|
            ≤ 15 * α * (2 * α * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)) :=
              mul_le_mul hKle hb (abs_nonneg _) (by linarith)
          _ = 30 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by ring
          _ ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by
              have hX : 0 ≤ (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
                mul_nonneg hs1 hc1
              nlinarith [hX, sq_nonneg α]

end Work.FTS.FireFix.Clauses
