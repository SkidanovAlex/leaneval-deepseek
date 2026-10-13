/-
Copyright: work module for the Elgindi finite-time singularity project.

# First and second derivatives of `θ ↦ (sin (2θ)) ^ (-η)`

For `η > 0` we compute, for **every** `θ : ℝ`,

* `deriv (fun t => (Real.sin (2 * t)) ^ (-η)) θ
     = -2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1)`, and
* `deriv (fun t => deriv (fun t' => (Real.sin (2 * t')) ^ (-η)) t) θ
     = 4 * η * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)
       + 4 * η * (Real.sin (2 * θ)) ^ (-η)`.

The subtlety is that Mathlib's `Real.rpow` is **not** junk on the negative
half-line (`Real.rpow_def_of_neg`: for `x < 0`, `x ^ y = exp (log x * y) * cos (y * π)`),
so `Real.deriv_rpow_const` is available whenever the base is nonzero
(`Real.hasStrictDerivAt_rpow_const_of_ne`) and the chain rule at the points where
`Real.sin (2 * θ) ≠ 0` is a routine `HasDerivAt.rpow_const` computation.

At the **zeros** of `sin (2·)` the situation is different: the map
`θ ↦ (sin (2θ)) ^ p` with `p < 0` is unbounded (hence discontinuous and not
differentiable) in every neighbourhood of such a point, so `deriv` takes the value
`0` there by `deriv_zero_of_not_differentiableAt`, which is exactly what the
right-hand sides above evaluate to (both because `Real.zero_rpow` and because
`Real.cos (2 * θ) ^ 2 = 1` there).  The non-differentiability is proved by
producing a one-sided filter `𝓝[>] θ` or `𝓝[<] θ` along which `sin (2·) → 0⁺`,
whence `(sin (2·)) ^ p → atTop`, contradicting continuity
(`not_tendsto_nhds_of_tendsto_atTop`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open Filter Set
open scoped Topology

namespace SinRpowWeight

/-! ## One-sided behaviour of `sin` at `0` and at the zeros of `sin (2·)` -/

/-- `Real.sin` maps the right neighbourhood of `0` to itself. -/
lemma tendsto_sin_nhdsGT_zero : Tendsto Real.sin (𝓝[>] (0:ℝ)) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using (Real.continuous_sin.continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  · have hpi : ∀ᶠ x in 𝓝[>] (0:ℝ), x < Real.pi :=
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
        (eventually_lt_nhds Real.pi_pos)
    filter_upwards [self_mem_nhdsWithin, hpi] with x hx hxpi
    simp only [Set.mem_Ioi] at hx ⊢
    exact Real.sin_pos_of_pos_of_lt_pi hx hxpi

/-- `Real.sin` maps the left neighbourhood of `0` to itself. -/
lemma tendsto_sin_nhdsLT_zero : Tendsto Real.sin (𝓝[<] (0:ℝ)) (𝓝[<] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using (Real.continuous_sin.continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (0:ℝ) ≤ 𝓝 0)
  · have hpi : ∀ᶠ x in 𝓝[<] (0:ℝ), -Real.pi < x :=
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds : 𝓝[<] (0:ℝ) ≤ 𝓝 0)
        (Ioi_mem_nhds (by linarith [Real.pi_pos]))
    filter_upwards [self_mem_nhdsWithin, hpi] with x hx hxpi
    simp only [Set.mem_Iio] at hx ⊢
    have h2 : 0 < Real.sin (-x) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at h2
    linarith

/-- Negation maps the left neighbourhood of `0` to the right neighbourhood of `0`. -/
lemma tendsto_neg_nhdsLT_zero : Tendsto (fun x : ℝ => -x) (𝓝[<] (0:ℝ)) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using (continuous_neg.continuousAt (x := (0:ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (0:ℝ) ≤ 𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_Ioi]
    linarith

/-- At a zero `θ` of `sin (2·)`, the function `t ↦ sin (2 * t)` tends to `0` from
above along one of the two one-sided filters at `θ`. -/
lemma tendsto_sin_two_side (θ : ℝ) (hθ : Real.sin (2*θ) = 0) :
    Tendsto (fun t => Real.sin (2*t)) (𝓝[>] θ) (𝓝[>] 0) ∨
    Tendsto (fun t => Real.sin (2*t)) (𝓝[<] θ) (𝓝[>] 0) := by
  have hsin : ∀ t : ℝ, Real.sin (2*t) = Real.cos (2*θ) * Real.sin (2*(t-θ)) := by
    intro t
    have h : 2*t = 2*θ + 2*(t-θ) := by ring
    rw [h, Real.sin_add, hθ, zero_mul, zero_add]
  have hcos : Real.cos (2*θ) = 1 ∨ Real.cos (2*θ) = -1 := by
    have h := Real.sin_sq_add_cos_sq (2*θ)
    rw [hθ] at h
    have h1 : Real.cos (2*θ)^2 = 1 := by linarith
    exact sq_eq_one_iff.mp h1
  have hlinR : Tendsto (fun t : ℝ => 2*(t-θ)) (𝓝[>] θ) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun t : ℝ => 2*(t-θ)) θ := by fun_prop
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] θ ≤ 𝓝 θ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ioi] at ht ⊢
      linarith
  have hlinL : Tendsto (fun t : ℝ => 2*(t-θ)) (𝓝[<] θ) (𝓝[<] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun t : ℝ => 2*(t-θ)) θ := by fun_prop
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] θ ≤ 𝓝 θ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Iio] at ht ⊢
      linarith
  rcases hcos with hc | hc
  · left
    have h1 : Tendsto (fun t : ℝ => Real.sin (2*(t-θ))) (𝓝[>] θ) (𝓝[>] 0) :=
      tendsto_sin_nhdsGT_zero.comp hlinR
    have he : (fun t : ℝ => Real.sin (2*t)) = (fun t : ℝ => Real.sin (2*(t-θ))) := by
      funext t; rw [hsin t, hc, one_mul]
    rw [he]; exact h1
  · right
    have h1 : Tendsto (fun t : ℝ => Real.sin (2*(t-θ))) (𝓝[<] θ) (𝓝[<] 0) :=
      tendsto_sin_nhdsLT_zero.comp hlinL
    have h2 : Tendsto (fun t : ℝ => -Real.sin (2*(t-θ))) (𝓝[<] θ) (𝓝[>] 0) :=
      tendsto_neg_nhdsLT_zero.comp h1
    have he : (fun t : ℝ => Real.sin (2*t)) = (fun t : ℝ => -Real.sin (2*(t-θ))) := by
      funext t; rw [hsin t, hc]; ring
    rw [he]; exact h2

/-! ## Non-differentiability at the zeros of `sin (2·)` -/

/-- If `θ` is a zero of `sin (2·)`, `p < 0` and `u` is continuous at `θ` with
`u θ ≠ 0`, then `t ↦ u t * (sin (2 t)) ^ p` is not differentiable at `θ`
(it is unbounded, hence discontinuous, in every neighbourhood of `θ`). -/
lemma not_differentiableAt_sin_two_rpow_mul (θ : ℝ) (hθ : Real.sin (2*θ) = 0)
    {p : ℝ} (hp : p < 0) {u : ℝ → ℝ} (hu : ContinuousAt u θ) (hune : u θ ≠ 0) :
    ¬ DifferentiableAt ℝ (fun t => u t * (Real.sin (2*t))^p) θ := by
  have hpos : 0 < |u θ| := abs_pos.mpr hune
  have key : ∀ (l : Filter ℝ), l ≤ 𝓝 θ →
      Tendsto (fun t => Real.sin (2*t)) l (𝓝[>] 0) →
      Tendsto (fun t => |u t * (Real.sin (2*t))^p|) l atTop := by
    intro l hle hl
    have hg : ∀ b : ℝ, ∀ᶠ t in l, b ≤ (Real.sin (2*t))^p :=
      tendsto_atTop.mp ((tendsto_rpow_neg_nhdsGT_zero hp).comp hl)
    have hspos : ∀ᶠ t in l, 0 < Real.sin (2*t) := (tendsto_nhdsWithin_iff.mp hl).2
    have hc : ∀ᶠ t in l, |u θ| / 2 ≤ |u t| :=
      Tendsto.eventually ((hu.tendsto.mono_left hle).abs) (eventually_ge_nhds (by linarith))
    rw [tendsto_atTop]
    intro A
    filter_upwards [hg (A / (|u θ| / 2)), hc, hspos] with t hA hcu hs
    have h2 : 0 ≤ (Real.sin (2*t))^p := Real.rpow_nonneg hs.le p
    rw [abs_mul, abs_of_nonneg h2]
    by_cases hAc : 0 ≤ A
    · have hdiv : 0 ≤ A / (|u θ| / 2) := div_nonneg hAc (by linarith)
      calc A = (|u θ| / 2) * (A / (|u θ| / 2)) := by field_simp
        _ ≤ |u t| * (Real.sin (2*t))^p := mul_le_mul hcu hA hdiv (abs_nonneg _)
    · push Not at hAc
      exact le_trans hAc.le (mul_nonneg (abs_nonneg _) h2)
  rintro hdiff
  rcases tendsto_sin_two_side θ hθ with hl | hl
  · exact not_tendsto_nhds_of_tendsto_atTop (key _ nhdsWithin_le_nhds hl) _
      ((hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).abs)
  · exact not_tendsto_nhds_of_tendsto_atTop (key _ nhdsWithin_le_nhds hl) _
      ((hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).abs)

/-- At a zero of `sin (2·)`, `t ↦ (sin (2 t)) ^ p` with `p < 0` has derivative `0`. -/
lemma deriv_sin_two_rpow_eq_zero (θ : ℝ) (hθ : Real.sin (2*θ) = 0)
    {p : ℝ} (hp : p < 0) :
    deriv (fun t : ℝ => (Real.sin (2*t))^p) θ = 0 := by
  have hnd : ¬ DifferentiableAt ℝ (fun t : ℝ => (1:ℝ) * (Real.sin (2*t))^p) θ :=
    not_differentiableAt_sin_two_rpow_mul θ hθ hp continuousAt_const one_ne_zero
  have hfun : (fun t : ℝ => (1:ℝ) * (Real.sin (2*t))^p)
      = (fun t : ℝ => (Real.sin (2*t))^p) := by
    funext t; simp
  rw [← hfun]
  exact deriv_zero_of_not_differentiableAt hnd

/-- `cos (2 θ) ≠ 0` at a zero `θ` of `sin (2·)`. -/
lemma cos_two_ne_zero_of_sin_two_eq_zero (θ : ℝ) (h : Real.sin (2*θ) = 0) :
    Real.cos (2*θ) ≠ 0 := by
  intro hc
  have hs := Real.sin_sq_add_cos_sq (2*θ)
  rw [h, hc] at hs
  norm_num at hs

/-- At a zero of `sin (2·)`, the function `-2η cos(2·) · (sin (2·)) ^ (-η-1)`
(`η > 0`) has derivative `0`. -/
lemma deriv_cos_mul_sin_two_rpow_eq_zero (η θ : ℝ) (hη : 0 < η)
    (hθ : Real.sin (2*θ) = 0) :
    deriv (fun t : ℝ => -2*η*Real.cos (2*t) * (Real.sin (2*t))^(-η-1)) θ = 0 := by
  have hcont : ContinuousAt (fun t : ℝ => -2*η*Real.cos (2*t)) θ := by fun_prop
  have hne : (-2*η*Real.cos (2*θ)) ≠ 0 := by
    have := cos_two_ne_zero_of_sin_two_eq_zero θ hθ
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact absurd h'' (ne_of_gt hη)
    · exact this h'
  have hnd : ¬ DifferentiableAt ℝ
      (fun t : ℝ => (-2*η*Real.cos (2*t)) * (Real.sin (2*t))^(-η-1)) θ :=
    not_differentiableAt_sin_two_rpow_mul θ hθ (p := -η-1) (by linarith) hcont hne
  have hfun : (fun t : ℝ => (-2*η*Real.cos (2*t)) * (Real.sin (2*t))^(-η-1))
      = (fun t : ℝ => -2*η*Real.cos (2*t) * (Real.sin (2*t))^(-η-1)) := rfl
  rw [← hfun]
  exact deriv_zero_of_not_differentiableAt hnd

/-! ## The derivatives away from the zeros of `sin (2·)` -/

/-- `x * x ^ y = x ^ (y + 1)` for `x = sin (2θ) ≠ 0` (`Real.rpow_add_one`; valid for
negative bases as well). -/
lemma sin_two_mul_rpow_add_one (θ : ℝ) (h : Real.sin (2*θ) ≠ 0) (y : ℝ) :
    Real.sin (2*θ) * (Real.sin (2*θ))^y = (Real.sin (2*θ))^(y+1) := by
  rw [Real.rpow_add_one h]; ring

/-- First derivative of `θ ↦ (sin (2 θ)) ^ (-η)` away from the zeros of `sin (2·)`. -/
lemma sinRpowDerivOfNe (η θ : ℝ) (h : Real.sin (2*θ) ≠ 0) :
    deriv (fun t : ℝ => (Real.sin (2*t))^(-η)) θ
      = -2*η*Real.cos (2*θ)*(Real.sin (2*θ))^(-η-1) := by
  have h2 : HasDerivAt (fun t : ℝ => 2*t) (2:ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (Real.cos (2*θ)*2) θ := by
    simpa using h2.sin
  have hmain : HasDerivAt (fun t : ℝ => (Real.sin (2*t))^(-η))
      ((Real.cos (2*θ)*2) * (-η) * (Real.sin (2*θ))^(-η-1)) θ :=
    hsin.rpow_const (p := -η) (Or.inl h)
  rw [hmain.deriv]; ring

/-- Second derivative of `θ ↦ (sin (2 θ)) ^ (-η)` away from the zeros of `sin (2·)`. -/
lemma sinRpowDerivDerivOfNe (η θ : ℝ) (h : Real.sin (2*θ) ≠ 0) :
    deriv (fun t : ℝ => -2*η*Real.cos (2*t) * (Real.sin (2*t))^(-η-1)) θ
      = 4*η*(η+1)*(Real.cos (2*θ))^2*(Real.sin (2*θ))^(-2-η)
        + 4*η*(Real.sin (2*θ))^(-η) := by
  have h2 : HasDerivAt (fun t : ℝ => 2*t) (2:ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (Real.cos (2*θ)*2) θ := by
    simpa using h2.sin
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-Real.sin (2*θ) * 2) θ := by
    simpa using h2.cos
  have ha : HasDerivAt (fun t : ℝ => -2*η*Real.cos (2*t)) (4*η*Real.sin (2*θ)) θ := by
    have := hcos.const_mul (-2*η)
    convert this using 1
    ring
  have hb : HasDerivAt (fun t : ℝ => (Real.sin (2*t))^(-η-1))
      ((Real.cos (2*θ)*2) * (-η-1) * (Real.sin (2*θ))^((-η-1)-1)) θ :=
    hsin.rpow_const (p := -η-1) (Or.inl h)
  have hderiv : deriv (fun t : ℝ => -2*η*Real.cos (2*t) * (Real.sin (2*t))^(-η-1)) θ
      = (4*η*Real.sin (2*θ)) * (Real.sin (2*θ))^(-η-1)
        + (-2*η*Real.cos (2*θ)) *
            ((Real.cos (2*θ)*2)*(-η-1)*(Real.sin (2*θ))^((-η-1)-1)) :=
    (ha.mul hb).deriv
  have e1 : Real.sin (2*θ) * (Real.sin (2*θ))^(-η-1) = (Real.sin (2*θ))^(-η) := by
    have h1 := Real.rpow_add_one h (-η-1)
    rw [show (-η-1) + 1 = -η by ring] at h1
    rw [h1, mul_comm]
  have e2 : (-η-1) - 1 = -2 - η := by ring
  rw [hderiv, e2]
  have e3 : (4*η*Real.sin (2*θ)) * (Real.sin (2*θ))^(-η-1)
      = 4*η*(Real.sin (2*θ))^(-η) := by
    rw [← e1]; ring
  have e4 : (-2*η*Real.cos (2*θ)) * ((Real.cos (2*θ)*2)*(-η-1)*(Real.sin (2*θ))^(-2-η))
      = 4*η*(η+1)*(Real.cos (2*θ))^2*(Real.sin (2*θ))^(-2-η) := by ring
  rw [e3, e4]
  ring

end SinRpowWeight

/-- First and second derivatives of `θ ↦ (sin (2 θ)) ^ (-η)`, `η > 0`, valid at
**all** `θ : ℝ`.  At the zeros of `sin (2·)` both sides of the first identity vanish
(the function is not differentiable there and `Real.zero_rpow` kills the right-hand
side), and the second identity reduces to `0 = 0`. -/
theorem sinRpowWeightDerivs (η : ℝ) (hη : 0 < η) :
    (∀ θ : ℝ, deriv (fun t => (Real.sin (2 * t)) ^ (-η)) θ
        = -2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1)) ∧
      (∀ θ : ℝ, deriv (fun t => deriv (fun t' => (Real.sin (2 * t')) ^ (-η)) t) θ
        = 4 * η * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)
          + 4 * η * (Real.sin (2 * θ)) ^ (-η)) := by
  have hfirst : ∀ θ : ℝ, deriv (fun t : ℝ => (Real.sin (2*t))^(-η)) θ
      = -2*η*Real.cos (2*θ)*(Real.sin (2*θ))^(-η-1) := by
    intro θ
    by_cases hθ : Real.sin (2*θ) = 0
    · rw [SinRpowWeight.deriv_sin_two_rpow_eq_zero θ hθ (p := -η) (by linarith), hθ,
        Real.zero_rpow (by linarith : -η - 1 ≠ 0)]
      ring
    · exact SinRpowWeight.sinRpowDerivOfNe η θ hθ
  constructor
  · exact hfirst
  · intro θ
    have hderiv : deriv (fun t : ℝ => (Real.sin (2*t))^(-η))
        = fun t : ℝ => -2*η*Real.cos (2*t)*(Real.sin (2*t))^(-η-1) := funext hfirst
    rw [hderiv]
    by_cases hθ : Real.sin (2*θ) = 0
    · rw [SinRpowWeight.deriv_cos_mul_sin_two_rpow_eq_zero η θ hη hθ, hθ,
        Real.zero_rpow (by linarith : -2 - η ≠ 0),
        Real.zero_rpow (by linarith : -η ≠ 0)]
      ring
    · exact SinRpowWeight.sinRpowDerivDerivOfNe η θ hθ

end Work.FTS.EllipticEst.H2W
