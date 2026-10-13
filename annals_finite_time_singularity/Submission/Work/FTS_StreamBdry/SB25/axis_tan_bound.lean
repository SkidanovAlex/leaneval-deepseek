import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.axis_tan_bound` — leaf B3 (`AxisTanBound`)

## What is proved

Let `f : ℝ → ℝ`, `v0 A B : ℝ`.  Assume

* `f` is differentiable on `(0, π/2)`,
* `|f θ| ≤ B` there,
* `V(θ) := f' θ - tan θ · f θ` satisfies `|V θ - v0| ≤ A (π/2 - θ)` there.

Then for every `θ ∈ (0, π/2)`,

`|tan θ · f θ + v0/2| ≤ |v0| * (π/2 - θ)^2 + 3 * A * (π/2 - θ)`.

This is leaf **B3** of the lead's per-leaf plan `sources/ftsV2/fts_sb25_leafplans.md`
(the one-dimensional axis expansion at `θ = π/2`, used to compute the edge trace of `ψP`).

## The idea (and why the plan's `x³/3` comparison is replaced by `J`)

Put `G t = f t · cos t + v0 (1 - sin t)`, so that `G' t = cos t · (V t - v0)` on
`(0, π/2)` and `G (π/2) = 0` (this is where `|f| ≤ B` is used: the value at `π/2` is
independent of `f (π/2)`, because `cos (π/2) = 0`).  The sharp bound is
`|G θ| ≤ A · J θ` with `J t = cos t - (π/2 - t) sin t`; indeed `J' t = -(π/2 - t) cos t`,
so `W₁ := G - A J` has `W₁' = cos t (V - v0) + A (π/2 - t) cos t ≥ 0` and
`W₂ := G + A J` has `W₂' ≤ 0`; both vanish at `π/2`, whence `-A J θ ≤ G θ ≤ A J θ`.
(Comparing with `±A (π/2 - t)³/3` as suggested in the plan fails, since
`(π/2 - t) cos t` is *not* dominated by `(π/2 - t)²` near `t = π/2`; `J` is the correct
primitive.)  Finally `J θ = sin u - u cos u` and `cos²θ = sin²u` with `u = π/2 - θ`,
which turns the conclusion into the elementary estimates `sin u - u cos u ≤ u³/3`
and `u² ≤ 9 sin²u`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB25

/-! ## Elementary trigonometric estimates -/

/-- `sin u - u cos u ≤ u³/3` for `u ≥ 0`: the function `u³/3 - sin u + u cos u` has
derivative `u (u - sin u) ≥ 0` and vanishes at `0`. -/
theorem axis_aux_sincos_cube (u : ℝ) (hu : 0 ≤ u) :
    Real.sin u - u * Real.cos u ≤ u ^ 3 / 3 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) (Icc 0 u) :=
    (((continuous_id.pow 3).div_const 3).sub Real.continuous_sin).add
      (continuous_id.mul Real.continuous_cos) |>.continuousOn
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x)
      (interior (Icc 0 u)) := fun x _ =>
    (by fun_prop : DifferentiableAt ℝ
      (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) x).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc 0 u),
      0 ≤ deriv (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun y : ℝ => y ^ 3 / 3 - Real.sin y + y * Real.cos y)
        (x ^ 2 - x * Real.sin x) x := by
      have hA : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
        convert (hasDerivAt_pow 3 x).div_const 3 using 1
        ring
      have hC : HasDerivAt (fun y : ℝ => y * Real.cos y) (Real.cos x - x * Real.sin x) x := by
        have h := (hasDerivAt_id x).mul (Real.hasDerivAt_cos x)
        convert h using 1
        · ext y; rfl
        · simp only [id_eq]; ring
      convert (hA.sub (Real.hasDerivAt_sin x)).add hC using 1
      ring
    rw [hd.deriv]
    have hx0 : 0 ≤ x := le_of_lt hx.1
    nlinarith [Real.sin_le hx0]
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) u) hcont hdiff hderiv
  have h0u : (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) 0
      ≤ (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) u :=
    hmono (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
  simp only at h0u
  norm_num at h0u
  linarith

/-- `u² ≤ 9 sin²u` on `[0, π/2]` (Jordan's inequality `sin u ≥ 2u/π ≥ u/3`). -/
theorem axis_aux_sq_le_nine_sin_sq (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ π / 2) :
    u ^ 2 ≤ 9 * Real.sin u ^ 2 := by
  have hpi : (1 / 3 : ℝ) ≤ 2 / π := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have h1 : 2 / π * u ≤ Real.sin u := Real.mul_le_sin hu0 hu1
  have hs : u / 3 ≤ Real.sin u := by
    have h2 : (1 / 3 : ℝ) * u ≤ 2 / π * u := mul_le_mul_of_nonneg_right hpi hu0
    linarith
  have hsq : (u / 3) ^ 2 ≤ (Real.sin u) ^ 2 := by
    apply sq_le_sq'
    · have : 0 ≤ u / 3 := by positivity
      linarith [le_trans this hs]
    · exact hs
  nlinarith [hsq]

/-- `1 - sin θ ≤ (π/2 - θ)²` on `(0, π/2)`. -/
theorem axis_aux_one_sub_sin_le_sq (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    1 - Real.sin θ ≤ (π / 2 - θ) ^ 2 := by
  have hθ' : θ = π / 2 - (π / 2 - θ) := by ring
  rw [hθ', Real.sin_pi_div_two_sub]
  have h := Real.one_sub_sq_div_two_le_cos (x := π / 2 - θ)
  nlinarith [h]

/-! ## The algebraic rewriting of `tan θ · f θ + v0/2` -/

/-- With `G t = f t cos t + v0 (1 - sin t)`, the identity
`tan θ · f θ + v0/2 = sin θ · G θ / cos²θ + v0 (1 - sin θ)/(2 (1 + sin θ))`. -/
theorem axis_aux_tan_axis_algebra (f : ℝ → ℝ) (v0 θ : ℝ)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    Real.tan θ * f θ + v0 / 2
      = Real.sin θ * (f θ * Real.cos θ + v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2
        + v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ)) := by
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hlt1 : Real.sin θ < 1 := by
    have hc' : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h1s : 1 - Real.sin θ ≠ 0 := by linarith
  have hs : 1 + Real.sin θ ≠ 0 := by linarith
  have hcos2 : Real.cos θ ^ 2 = (1 - Real.sin θ) * (1 + Real.sin θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hA : Real.tan θ * f θ = Real.sin θ * (f θ * Real.cos θ) / Real.cos θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hB : v0 / 2 = Real.sin θ * (v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2
      + v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ)) := by
    rw [hcos2]
    field_simp
    ring
  have hsplit : Real.sin θ * (f θ * Real.cos θ + v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2
      = Real.sin θ * (f θ * Real.cos θ) / Real.cos θ ^ 2
        + Real.sin θ * (v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2 := by
    rw [mul_add, add_div]
  rw [hA, hB, hsplit]
  ring

/-! ## Continuity of `G` on the closed interval `[θ, π/2]`

The endpoint `π/2` is not covered by differentiability; there boundedness of `f` gives
`f t · cos t → 0`. -/

/-- `t ↦ f t cos t + v0 (1 - sin t)` is continuous on `[θ, π/2]` when `f` is differentiable
on `(0,π/2)` and bounded there. -/
theorem axis_aux_G_continuousOn (f : ℝ → ℝ) (v0 B θ : ℝ)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hdiff : ∀ t ∈ Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ f t)
    (hbd : ∀ t ∈ Ioo (0 : ℝ) (π / 2), |f t| ≤ B) :
    ContinuousOn (fun t => f t * Real.cos t + v0 * (1 - Real.sin t)) (Icc θ (π / 2)) := by
  intro x hx
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hx0 : 0 < x := lt_of_lt_of_le hθ.1 hx.1
    have h1 : ContinuousAt f x := (hdiff x ⟨hx0, hlt⟩).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Real.cos t) x := Real.continuous_cos.continuousAt
    have h3 : ContinuousAt (fun t : ℝ => Real.sin t) x := Real.continuous_sin.continuousAt
    have h4 : ContinuousAt (fun t : ℝ => v0 * (1 - Real.sin t)) x :=
      (continuousAt_const.sub h3).const_mul v0
    exact ((h1.mul h2).add h4).continuousWithinAt
  · subst heq
    have hG0 : f (π / 2) * Real.cos (π / 2) + v0 * (1 - Real.sin (π / 2)) = 0 := by
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    show Tendsto (fun t => f t * Real.cos t + v0 * (1 - Real.sin t))
      (𝓝[Icc θ (π / 2)] (π / 2))
      (𝓝 (f (π / 2) * Real.cos (π / 2) + v0 * (1 - Real.sin (π / 2))))
    rw [hG0]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hc : Tendsto (fun t : ℝ => Real.cos t) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
      have := (Real.continuous_cos.tendsto (π / 2)).mono_left
        (nhdsWithin_le_nhds (s := Icc θ (π / 2)) (a := π / 2))
      rwa [Real.cos_pi_div_two] at this
    have hss : Tendsto (fun t : ℝ => Real.sin t) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 1) := by
      have := (Real.continuous_sin.tendsto (π / 2)).mono_left
        (nhdsWithin_le_nhds (s := Icc θ (π / 2)) (a := π / 2))
      rwa [Real.sin_pi_div_two] at this
    have hg : Tendsto (fun t : ℝ => B * |Real.cos t| + |v0| * |1 - Real.sin t|)
        (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => B * |Real.cos t|) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
        simpa using hc.abs.const_mul B
      have h2 : Tendsto (fun t : ℝ => |v0| * |1 - Real.sin t|)
          (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
        have hsub : Tendsto (fun t : ℝ => 1 - Real.sin t)
            (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
          have h0 : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 1) :=
            tendsto_const_nhds
          simpa using h0.sub hss
        simpa using hsub.abs.const_mul |v0|
      simpa using h1.add h2
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards with t using abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rcases lt_or_eq_of_le ht.2 with hlt | hqq
      · have hx0 : 0 < t := lt_of_lt_of_le hθ.1 ht.1
        have hb := hbd t ⟨hx0, hlt⟩
        have hb' : |f t| * |Real.cos t| ≤ B * |Real.cos t| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        calc ‖f t * Real.cos t + v0 * (1 - Real.sin t)‖
            = |f t * Real.cos t + v0 * (1 - Real.sin t)| := rfl
          _ ≤ |f t * Real.cos t| + |v0 * (1 - Real.sin t)| := abs_add_le _ _
          _ = |f t| * |Real.cos t| + |v0| * |1 - Real.sin t| := by rw [abs_mul, abs_mul]
          _ ≤ B * |Real.cos t| + |v0| * |1 - Real.sin t| := by linarith
      · subst hqq
        simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ## The final numerical chain -/

/-- If `|Gval| ≤ A (sin u - u cos u)`, `A ≥ 0` and `0 < u ≤ π/2`, then
`|cos u · Gval / sin²u| ≤ 3 A u`. -/
theorem axis_aux_final_bound (A u Gval : ℝ) (hA : 0 ≤ A) (hu : 0 < u) (hu1 : u ≤ π / 2)
    (hG : |Gval| ≤ A * (Real.sin u - u * Real.cos u)) :
    |Real.cos u * Gval / Real.sin u ^ 2| ≤ 3 * A * u := by
  have hu0 : 0 ≤ u := le_of_lt hu
  have hsinpos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [hu1, Real.pi_pos])
  have hcosnn : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hu1⟩
  have hAJnn : 0 ≤ A * (Real.sin u - u * Real.cos u) := le_trans (abs_nonneg _) hG
  have h1 : |Real.cos u * Gval / Real.sin u ^ 2| = Real.cos u * |Gval| / Real.sin u ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hcosnn, abs_of_pos (pow_pos hsinpos 2)]
  rw [h1]
  have hJle : Real.sin u - u * Real.cos u ≤ u ^ 3 / 3 := axis_aux_sincos_cube u hu0
  have h2 : Real.cos u * |Gval| ≤ Real.cos u * (A * (Real.sin u - u * Real.cos u)) :=
    mul_le_mul_of_nonneg_left hG hcosnn
  have h3 : Real.cos u * (A * (Real.sin u - u * Real.cos u)) ≤ A * (u ^ 3 / 3) := by
    have hc1 : Real.cos u * (A * (Real.sin u - u * Real.cos u))
        ≤ 1 * (A * (Real.sin u - u * Real.cos u)) :=
      mul_le_mul_of_nonneg_right (Real.cos_le_one u) hAJnn
    have h4 := mul_le_mul_of_nonneg_left hJle hA
    linarith
  have h5 : A * (u ^ 3 / 3) / Real.sin u ^ 2 ≤ 3 * A * u := by
    have hsq : u ^ 2 ≤ 9 * Real.sin u ^ 2 := axis_aux_sq_le_nine_sin_sq u hu0 hu1
    rw [div_le_iff₀ (pow_pos hsinpos 2)]
    have hcube : u ^ 3 ≤ 9 * u * Real.sin u ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq hu0
      nlinarith [this]
    have hcube' : u ^ 3 / 3 ≤ 3 * (u * Real.sin u ^ 2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcube' hA]
  calc Real.cos u * |Gval| / Real.sin u ^ 2
      ≤ Real.cos u * (A * (Real.sin u - u * Real.cos u)) / Real.sin u ^ 2 :=
        div_le_div_of_nonneg_right h2 (sq_nonneg _)
    _ ≤ A * (u ^ 3 / 3) / Real.sin u ^ 2 := div_le_div_of_nonneg_right h3 (sq_nonneg _)
    _ ≤ 3 * A * u := h5

/-! ## The leaf -/

theorem axis_tan_bound (f : ℝ → ℝ) (v0 A B : ℝ) :
    Work.FTS_StreamBdry.SB25.AxisTanBound f v0 A B := by
  intro hdiff hbd hclose θ hθ
  -- `0 ≤ A` is forced by the rate hypothesis.
  have hA : 0 ≤ A := by
    have h := hclose (π / 4) (by constructor <;> linarith [Real.pi_pos])
    have hp : (0:ℝ) < π / 2 - π / 4 := by linarith [Real.pi_pos]
    nlinarith [h, abs_nonneg (deriv f (π / 4) - Real.tan (π / 4) * f (π / 4) - v0)]
  set u : ℝ := π / 2 - θ with hu
  have hu_pos : 0 < u := by rw [hu]; linarith [hθ.2]
  have hu_le : u ≤ π / 2 := by rw [hu]; linarith [hθ.1]
  have hθ_eq : θ = π / 2 - u := by rw [hu]; ring
  set G : ℝ → ℝ := fun t => f t * Real.cos t + v0 * (1 - Real.sin t) with hG
  set J : ℝ → ℝ := fun t => Real.cos t - (π / 2 - t) * Real.sin t with hJ
  set W1 : ℝ → ℝ := fun t => G t - A * J t with hW1
  set W2 : ℝ → ℝ := fun t => G t + A * J t with hW2
  have hGc : ContinuousOn G (Icc θ (π / 2)) := by
    rw [hG]; exact axis_aux_G_continuousOn f v0 B θ hθ hdiff hbd
  have hJc : ContinuousOn J (Icc θ (π / 2)) := by
    rw [hJ]; fun_prop
  have hW1c : ContinuousOn W1 (Icc θ (π / 2)) := by
    rw [hW1]; exact hGc.sub (hJc.const_mul A)
  have hW2c : ContinuousOn W2 (Icc θ (π / 2)) := by
    rw [hW2]; exact hGc.add (hJc.const_mul A)
  -- derivatives of `G`, `J`, `W₁`, `W₂`
  have hGd : ∀ x ∈ Ioo θ (π / 2),
      HasDerivAt G (Real.cos x * (deriv f x - Real.tan x * f x - v0)) x := by
    intro x hx
    rw [hG]
    have hx0 : x ∈ Ioo (0:ℝ) (π / 2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    have hcx : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hfx : HasDerivAt f (deriv f x) x := (hdiff x hx0).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => f t * Real.cos t)
        (deriv f x * Real.cos x + f x * (-Real.sin x)) x := hfx.mul (Real.hasDerivAt_cos x)
    have h2 : HasDerivAt (fun t : ℝ => v0 * (1 - Real.sin t)) (v0 * (-(Real.cos x))) x := by
      have h0 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
      have hh := (h0.sub (Real.hasDerivAt_sin x)).const_mul v0
      convert hh using 1
      ring
    refine (h1.add h2).congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hJd : ∀ x ∈ Ioo θ (π / 2), HasDerivAt J (-(π / 2 - x) * Real.cos x) x := by
    intro x hx
    rw [hJ]
    have hid : HasDerivAt (fun t : ℝ => π / 2 - t) (-1) x := by
      have h0 : HasDerivAt (fun _ : ℝ => (π / 2:ℝ)) 0 x := hasDerivAt_const x (π / 2)
      have hh := h0.sub (hasDerivAt_id x)
      convert hh using 1
      · ext t; rfl
      · ring
    have hprod : HasDerivAt (fun t : ℝ => (π / 2 - t) * Real.sin t)
        ((-1) * Real.sin x + (π / 2 - x) * Real.cos x) x := hid.mul (Real.hasDerivAt_sin x)
    refine ((Real.hasDerivAt_cos x).sub hprod).congr_deriv ?_
    ring
  have hW1d : ∀ x ∈ Ioo θ (π / 2), HasDerivAt W1
      (Real.cos x * (deriv f x - Real.tan x * f x - v0) + A * (π / 2 - x) * Real.cos x) x := by
    intro x hx
    rw [hW1]
    refine ((hGd x hx).sub ((hJd x hx).const_mul A)).congr_deriv ?_
    ring
  have hW2d : ∀ x ∈ Ioo θ (π / 2), HasDerivAt W2
      (Real.cos x * (deriv f x - Real.tan x * f x - v0) - A * (π / 2 - x) * Real.cos x) x := by
    intro x hx
    rw [hW2]
    refine ((hGd x hx).add ((hJd x hx).const_mul A)).congr_deriv ?_
    ring
  -- monotonicity signs
  have hW1deriv : ∀ x ∈ Ioo θ (π / 2), 0 ≤ deriv W1 x := by
    intro x hx
    have hx0 : x ∈ Ioo (0:ℝ) (π / 2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    rw [(hW1d x hx).deriv]
    have hcosx : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hVle : -(A * (π / 2 - x)) ≤ deriv f x - Real.tan x * f x - v0 := by
      have := neg_abs_le (deriv f x - Real.tan x * f x - v0)
      linarith [hclose x hx0]
    have hmul := mul_le_mul_of_nonneg_left hVle hcosx
    nlinarith [hmul]
  have hW2deriv : ∀ x ∈ Ioo θ (π / 2), deriv W2 x ≤ 0 := by
    intro x hx
    have hx0 : x ∈ Ioo (0:ℝ) (π / 2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    rw [(hW2d x hx).deriv]
    have hcosx : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hVle : deriv f x - Real.tan x * f x - v0 ≤ A * (π / 2 - x) := by
      have := le_abs_self (deriv f x - Real.tan x * f x - v0)
      linarith [hclose x hx0]
    have hmul := mul_le_mul_of_nonneg_left hVle hcosx
    nlinarith [hmul]
  have hW1mono : MonotoneOn W1 (Icc θ (π / 2)) := by
    have hd : DifferentiableOn ℝ W1 (interior (Icc θ (π / 2))) := by
      rw [interior_Icc]; exact fun x hx => (hW1d x hx).differentiableAt.differentiableWithinAt
    have hd' : ∀ x ∈ interior (Icc θ (π / 2)), 0 ≤ deriv W1 x := by
      intro x hx; rw [interior_Icc] at hx; exact hW1deriv x hx
    exact monotoneOn_of_deriv_nonneg (convex_Icc θ (π / 2)) hW1c hd hd'
  have hW2anti : AntitoneOn W2 (Icc θ (π / 2)) := by
    have hd : DifferentiableOn ℝ W2 (interior (Icc θ (π / 2))) := by
      rw [interior_Icc]; exact fun x hx => (hW2d x hx).differentiableAt.differentiableWithinAt
    have hd' : ∀ x ∈ interior (Icc θ (π / 2)), deriv W2 x ≤ 0 := by
      intro x hx; rw [interior_Icc] at hx; exact hW2deriv x hx
    exact antitoneOn_of_deriv_nonpos (convex_Icc θ (π / 2)) hW2c hd hd'
  have hW1pi : W1 (π / 2) = 0 := by
    rw [hW1, hG, hJ]; norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hW2pi : W2 (π / 2) = 0 := by
    rw [hW2, hG, hJ]; norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hθmem : θ ∈ Icc θ (π / 2) := ⟨le_refl _, le_of_lt hθ.2⟩
  have hπmem : π / 2 ∈ Icc θ (π / 2) := ⟨le_of_lt hθ.2, le_refl _⟩
  have hle1 : G θ ≤ A * J θ := by
    have h := hW1mono hθmem hπmem (le_of_lt hθ.2)
    rw [hW1pi, hW1] at h
    linarith
  have hge2 : -(A * J θ) ≤ G θ := by
    have h := hW2anti hθmem hπmem (le_of_lt hθ.2)
    rw [hW2pi, hW2] at h
    linarith
  have hGabs : |G θ| ≤ A * J θ := abs_le.mpr ⟨hge2, hle1⟩
  -- rewrite `G θ`, `sin θ`, `cos θ` in terms of `u`
  have hJval : J θ = Real.sin u - u * Real.cos u := by
    have h2 : (π / 2 - θ) = u := by linarith [hu]
    have h3 : Real.cos θ = Real.sin u := by rw [hθ_eq, Real.cos_pi_div_two_sub]
    have h4 : Real.sin θ = Real.cos u := by rw [hθ_eq, Real.sin_pi_div_two_sub]
    simp only [hJ, h2, h3, h4]
  have hGabs' : |G θ| ≤ A * (Real.sin u - u * Real.cos u) := by
    rw [← hJval]; exact hGabs
  have hsin_eq : Real.sin θ = Real.cos u := by rw [hθ_eq, Real.sin_pi_div_two_sub]
  have hcos_eq : Real.cos θ = Real.sin u := by rw [hθ_eq, Real.cos_pi_div_two_sub]
  -- the two terms of the rewriting
  have hb1 : |Real.sin θ * G θ / Real.cos θ ^ 2| ≤ 3 * A * u := by
    have hratio : Real.sin θ * G θ / Real.cos θ ^ 2 = Real.cos u * G θ / Real.sin u ^ 2 := by
      rw [hsin_eq, hcos_eq]
    rw [hratio]
    exact axis_aux_final_bound A u (G θ) hA hu_pos hu_le hGabs'
  have hb2 : |v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ))| ≤ |v0| * u ^ 2 := by
    have h1u : 1 - Real.sin θ ≤ u ^ 2 := by
      have h := axis_aux_one_sub_sin_le_sq θ hθ
      simpa [hu] using h
    have h2 : 0 ≤ 1 - Real.sin θ := by linarith [Real.sin_le_one θ]
    have hsinθnn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hpos : 0 < 2 * (1 + Real.sin θ) := by linarith
    have h3 : (1 - Real.sin θ) / (2 * (1 + Real.sin θ)) ≤ u ^ 2 := by
      rw [div_le_iff₀ hpos]
      nlinarith [h1u, h2, sq_nonneg u, hsinθnn]
    rw [abs_div, abs_mul, abs_of_nonneg h2, abs_of_pos hpos]
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg v0)
    calc |v0| * (1 - Real.sin θ) / (2 * (1 + Real.sin θ))
        = |v0| * ((1 - Real.sin θ) / (2 * (1 + Real.sin θ))) := by ring
      _ ≤ |v0| * u ^ 2 := this
  have hfinal : |Real.sin θ * G θ / Real.cos θ ^ 2
      + v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ))| ≤ 3 * A * u + |v0| * u ^ 2 :=
    (abs_add_le _ _).trans (add_le_add hb1 hb2)
  rw [axis_aux_tan_axis_algebra f v0 θ hθ]
  have hfin : 3 * A * u + |v0| * u ^ 2 = |v0| * (π / 2 - θ) ^ 2 + 3 * A * (π / 2 - θ) := by
    rw [hu]; ring
  rw [hfin] at hfinal
  exact hfinal

end Work.FTS_StreamBdry.SB25
