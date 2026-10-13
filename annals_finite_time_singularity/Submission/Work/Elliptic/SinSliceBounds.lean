/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise bounds for a smooth angular slice vanishing at the endpoints

`SinSliceBounds` is the one-dimensional analytic input of `DivisionBySin`: for a function
`h : ℝ → ℝ` which is smooth on an open neighbourhood of `[0, π/2]` and vanishes at `0` and
`π/2`, the slice `h`, its derivative, the quotient `SinQ h = h / sin(2θ)` and the derivative
of that quotient are all bounded on `(0, π/2)`, and `h` itself is `O(sin 2θ)` there.

The proof has three ingredients.

* `h` is `C¹` (indeed `C^∞`) on the closed interval and vanishes at both endpoints, so
  `Work.Elliptic.contDiffOn_one_bounds` bounds `h` by `C · min θ (π/2 - θ)` and `h'` by `C`.
  Since `min θ (π/2 - θ) ≤ (π/2) sin 2θ` on `(0, π/2)` (`Real.mul_le_sin`, Jordan), this gives
  the bound on `h` by a multiple of `sin 2θ`, and hence also the bound on the quotient
  `SinQ h = h / sin 2θ`.
* For the derivative of the quotient, write `W h θ = h' θ sin 2θ - 2 cos 2θ h θ`; the quotient
  rule gives `deriv (SinQ h) θ = W h θ / sin²(2θ)`.  The point is that `W h` vanishes at the
  *second* order at both endpoints: `W h = 0` at `0, π/2` and
  `(W h)' θ = sin 2θ (h'' θ + 4 h θ)`, which vanishes at `0` and `π/2`.  Hence
  `seg_second_order_bound` (applied to `W h` near `0` and to the reflection `θ ↦ W h (π/2 - θ)`
  near `π/2`) yields `|W h θ| ≤ M min(θ, π/2 - θ)²`, and dividing by `sin² 2θ`, which dominates
  `min(θ, π/2 - θ)²` by a constant multiple, gives the bound.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.seg_second_order_bound
import Submission.Work.Elliptic.exists_bound_of_continuousOn_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Elementary angular bounds -/

/-- The closed interval `[0, π/2]` lies in the open set on which a `SmoothSlice` is smooth. -/
private lemma ssb_Icc_subset : Set.Icc 0 (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
  Set.Icc_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])

private lemma ssb_one_le_half_pi : (1 : ℝ) ≤ Real.pi / 2 := by
  have h := Real.pi_gt_three
  linarith

private lemma ssb_arith (θ : ℝ) : Real.pi / 2 * (2 / Real.pi * (2 * θ)) = 2 * θ := by
  field_simp

/-- On `(0, π/2)`, `sin (2θ)` is positive and dominates `min θ (π/2 - θ)`: both `θ` and
`π/2 - θ` are at most `(π/2) sin (2θ)`, by Jordan's inequality `sin x ≥ 2x/π`. -/
private lemma ssb_min_le_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) ∧ min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 * Real.sin (2 * θ) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  refine ⟨hsinpos, ?_⟩
  rcases le_total θ (Real.pi / 4) with hle | hle
  · rw [min_eq_left (by linarith)]
    have h4 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (show (0 : ℝ) ≤ 2 * θ by linarith [hθ.1])
        (show 2 * θ ≤ Real.pi / 2 by linarith [hle])
    have hstep : Real.pi / 2 * (2 / Real.pi * (2 * θ)) ≤ Real.pi / 2 * Real.sin (2 * θ) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    rw [ssb_arith] at hstep
    linarith [hθ.1]
  · rw [min_eq_right (by linarith)]
    have ht : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      rw [show 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) by ring, Real.sin_pi_sub]
    rw [ht]
    have h4 : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) ≤ Real.sin (2 * (Real.pi / 2 - θ)) :=
      Real.mul_le_sin (show (0 : ℝ) ≤ 2 * (Real.pi / 2 - θ) by linarith [hθ.2])
        (show 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 by linarith [hle])
    have hstep : Real.pi / 2 * (2 / Real.pi * (2 * (Real.pi / 2 - θ)))
        ≤ Real.pi / 2 * Real.sin (2 * (Real.pi / 2 - θ)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    rw [ssb_arith] at hstep
    linarith [hθ.2]

/-! ## The numerator of the derivative of the quotient -/

/-- `W h θ = sin(2θ) h'(θ) - 2 cos(2θ) h(θ)`: the numerator of the derivative of
`SinQ h = h / sin(2θ)`. -/
private def ssbW (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => deriv h θ * Real.sin (2 * θ) - 2 * Real.cos (2 * θ) * h θ

private lemma ssb_hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 := h1.sin
  rw [show Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) by ring] at h2
  exact h2

private lemma ssb_hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 := h1.cos
  rw [show -Real.sin (2 * θ) * 2 = -2 * Real.sin (2 * θ) by ring] at h2
  exact h2

/-- The derivative of `W h`: `(W h)' θ = sin(2θ) (h''(θ) + 4 h(θ))`. -/
private lemma ssb_hasDerivAt_W (h : ℝ → ℝ) (hsm : SmoothSlice h) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    HasDerivAt (ssbW h) (Real.sin (2 * θ) * (deriv (deriv h) θ + 4 * h θ)) θ := by
  have hU : Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have h2 : ContDiffOn ℝ 2 h (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hsm.of_le le_top
  have hC2 : ContDiffAt ℝ 2 h θ := h2.contDiffAt hU
  have hdh : HasDerivAt h (deriv h θ) θ := (hC2.differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hddh : HasDerivAt (deriv h) (deriv (deriv h) θ) θ :=
    ((hd1.contDiffAt hU).differentiableAt (by norm_num)).hasDerivAt
  have hA : HasDerivAt (fun x : ℝ => deriv h x * Real.sin (2 * x))
      (deriv (deriv h) θ * Real.sin (2 * θ) + deriv h θ * (2 * Real.cos (2 * θ))) θ :=
    hddh.mul (ssb_hasDerivAt_sin_two θ)
  have hB : HasDerivAt (fun x : ℝ => 2 * Real.cos (2 * x) * h x)
      ((2 * (-2 * Real.sin (2 * θ))) * h θ + (2 * Real.cos (2 * θ)) * deriv h θ) θ :=
    ((ssb_hasDerivAt_cos_two θ).const_mul 2).mul hdh
  have hAB : HasDerivAt (ssbW h)
      ((deriv (deriv h) θ * Real.sin (2 * θ) + deriv h θ * (2 * Real.cos (2 * θ)))
        - ((2 * (-2 * Real.sin (2 * θ))) * h θ + (2 * Real.cos (2 * θ)) * deriv h θ)) θ :=
    hA.sub hB
  have key : (deriv (deriv h) θ * Real.sin (2 * θ) + deriv h θ * (2 * Real.cos (2 * θ)))
      - ((2 * (-2 * Real.sin (2 * θ))) * h θ + (2 * Real.cos (2 * θ)) * deriv h θ)
      = Real.sin (2 * θ) * (deriv (deriv h) θ + 4 * h θ) := by ring
  rw [key] at hAB
  exact hAB

/-- A uniform bound for `|h'' + 4h|` on the closed angular interval. -/
private lemma ssb_C2_bound (h : ℝ → ℝ) (hsm : SmoothSlice h) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ x ∈ Set.Icc 0 (Real.pi / 2),
      |deriv (deriv h) x + 4 * h x| ≤ M₀ := by
  have h2 : ContDiffOn ℝ 2 h (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hsm.of_le le_top
  have hdd : ContDiffOn ℝ 0 (deriv (deriv h)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    (h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ => deriv (deriv h) x + 4 * h x)
      (Set.Icc 0 (Real.pi / 2)) :=
    ((hdd.continuousOn).mono ssb_Icc_subset).add
      (((h2.continuousOn).mono ssb_Icc_subset).const_mul 4)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs] using le_trans (hC x hx) (le_max_left _ _)

/-- Second order vanishing of `W h = sin(2θ) h' - 2 cos(2θ) h` at both endpoints. -/
private lemma ssb_W_snd (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi / 2) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |ssbW h θ| ≤ M * (min θ (Real.pi / 2 - θ)) ^ 2 := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := ssb_C2_bound h hsm
  have hWderiv : ∀ x ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (ssbW h) (Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x))
        (Set.Icc 0 (Real.pi / 2)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := ssb_Icc_subset hx
    have h' : HasDerivAt (ssbW h) (Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x)) x :=
      ssb_hasDerivAt_W h hsm x hx'
    exact h'.hasDerivWithinAt
  have hWbnd : ∀ x ∈ Set.Icc 0 (Real.pi / 2),
      ‖Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x)‖ ≤ (2 * M₀) * x := by
    intro x hx
    have hx1 : x ≤ Real.pi / 2 := hx.2
    have hsin0 : 0 ≤ Real.sin (2 * x) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx1])
    have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsin0]
    calc Real.sin (2 * x) * |deriv (deriv h) x + 4 * h x| ≤ (2 * x) * M₀ :=
          mul_le_mul hsinle (hM₀ x hx) (abs_nonneg _) (by linarith [hx.1])
      _ = 2 * M₀ * x := by ring
  have hhalf1 : ∀ x ∈ Set.Icc 0 (Real.pi / 2), ‖ssbW h x - ssbW h 0‖ ≤ (2 * M₀) * x ^ 2 :=
    seg_second_order_bound (ssbW h)
      (fun x => Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x)) (2 * M₀) (Real.pi / 2)
      (by positivity) (by linarith [Real.pi_pos]) hWderiv hWbnd
  have hW0 : ssbW h 0 = 0 := by simp [ssbW, h0]
  have hfirst : ∀ x ∈ Set.Icc 0 (Real.pi / 2), |ssbW h x| ≤ (2 * M₀) * x ^ 2 := by
    intro x hx
    have hval1 := hhalf1 x hx
    rw [hW0, sub_zero, Real.norm_eq_abs] at hval1
    exact hval1
  have hWpi : ssbW h (Real.pi / 2) = 0 := by
    have h1 : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h2 : Real.cos (2 * (Real.pi / 2)) = -1 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
    simp [ssbW, hp, h1, h2]
  have hWref : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun s : ℝ => ssbW h (Real.pi / 2 - s))
        (-(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t))))
        (Set.Icc 0 (Real.pi / 2)) t := by
    intro t ht
    have hy : Real.pi / 2 - t ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ssb_Icc_subset ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hWy := ssb_hasDerivAt_W h hsm (Real.pi / 2 - t) hy
    have hg : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t :=
      (hasDerivAt_id t).const_sub (Real.pi / 2)
    have hcomp : HasDerivAt (fun s : ℝ => ssbW h (Real.pi / 2 - s))
        (Real.sin (2 * (Real.pi / 2 - t))
          * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)) * (-1)) t :=
      hWy.comp t hg
    have hsin' : Real.sin (2 * (Real.pi / 2 - t)) = Real.sin (2 * t) := by
      rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
    have hval : Real.sin (2 * (Real.pi / 2 - t))
          * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)) * (-1)
        = -(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t))) := by
      rw [hsin']; ring
    rw [hval] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbref : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      ‖-(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)))‖
        ≤ (2 * M₀) * t := by
    intro t ht
    have ht1 : t ≤ Real.pi / 2 := ht.2
    have hy : Real.pi / 2 - t ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hsin0 : 0 ≤ Real.sin (2 * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht1])
    have hsinle : Real.sin (2 * t) ≤ 2 * t := Real.sin_le (by linarith [ht.1])
    have hb := hM₀ (Real.pi / 2 - t) hy
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hsin0]
    calc Real.sin (2 * t) * |deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)|
        ≤ (2 * t) * M₀ := mul_le_mul hsinle hb (abs_nonneg _) (by linarith [ht.1])
      _ = 2 * M₀ * t := by ring
  have hhalf2 : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      ‖(fun s : ℝ => ssbW h (Real.pi / 2 - s)) t - (fun s : ℝ => ssbW h (Real.pi / 2 - s)) 0‖
        ≤ (2 * M₀) * t ^ 2 :=
    seg_second_order_bound (fun s : ℝ => ssbW h (Real.pi / 2 - s))
      (fun t => -(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t))))
      (2 * M₀) (Real.pi / 2) (by positivity) (by linarith [Real.pi_pos]) hWref hbref
  have hsecond : ∀ x ∈ Set.Icc 0 (Real.pi / 2), |ssbW h x| ≤ (2 * M₀) * (Real.pi / 2 - x) ^ 2 := by
    intro x hx
    have ht : Real.pi / 2 - x ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hval2 := hhalf2 (Real.pi / 2 - x) ht
    have harg : Real.pi / 2 - (Real.pi / 2 - x) = x := by ring
    simp only [harg, Real.norm_eq_abs, sub_zero] at hval2
    rw [hWpi] at hval2
    simpa using hval2
  refine ⟨2 * M₀, by positivity, ?_⟩
  intro θ hθ
  have hθIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases le_total θ (Real.pi / 2 - θ) with hle | hle
  · rw [min_eq_left hle]
    exact hfirst θ hθIcc
  · rw [min_eq_right hle]
    exact hsecond θ hθIcc

/-! ## The quotient rule -/

/-- The quotient rule for `SinQ h = h / sin(2θ)`, in the form needed below: on `(0, π/2)`,
`deriv (SinQ h) θ = W h θ / sin²(2θ)`. -/
private lemma ssb_derivSinQ (h : ℝ → ℝ) (hC : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (SinQ h) θ = ssbW h θ / (Real.sin (2 * θ)) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2 : (Real.sin (2 * θ)) ^ 2 ≠ 0 := by positivity
  have hid := (htU_interior_facts h hC).2.2.2.1 θ hθ
  have hSinQ : SinQ h = htU h := rfl
  rw [hSinQ, eq_div_iff hs2]
  simp only [ssbW]
  rw [mul_comm]
  exact hid

/-! ## The bounds on `h` and on `h'` -/

private lemma ssb_pointwise (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv h θ| ≤ C) := by
  have hC1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := (hsm.of_le le_top).mono ssb_Icc_subset
  obtain ⟨C₀, hC₀0, hC₀min, hC₀d⟩ := contDiffOn_one_bounds hC1 h0 hp
  refine ⟨C₀ * (Real.pi / 2), by positivity, ?_, ?_⟩
  · intro θ hθ
    have hmin := (ssb_min_le_sin hθ).2
    calc |h θ| ≤ C₀ * min θ (Real.pi / 2 - θ) := hC₀min θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      _ ≤ C₀ * (Real.pi / 2 * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hmin hC₀0
      _ = C₀ * (Real.pi / 2) * Real.sin (2 * θ) := by ring
  · intro θ hθ
    have h := hC₀d θ hθ
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_mul_of_one_le_right hC₀0 ssb_one_le_half_pi)

/-! ## The main statement -/

theorem SinSliceBounds (h : ℝ → ℝ) (hsm : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv h θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Work.Elliptic.SinQ h θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv (Work.Elliptic.SinQ h) θ| ≤ C) := by
  obtain ⟨C₁, hC₁0, hC₁h, hC₁d⟩ := ssb_pointwise h hsm h0 hp
  obtain ⟨M, hM0, hMW⟩ := ssb_W_snd h hsm h0 hp
  have hC2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) := (hsm.of_le le_top).mono ssb_Icc_subset
  set Cm : ℝ := max 1 (max (C₁ * (Real.pi / 2)) (M * Real.pi ^ 2 / 4)) with hCm
  have hC₁le : C₁ ≤ Cm := by
    rw [hCm]
    calc C₁ ≤ C₁ * (Real.pi / 2) := le_mul_of_one_le_right hC₁0 ssb_one_le_half_pi
      _ ≤ max (C₁ * (Real.pi / 2)) (M * Real.pi ^ 2 / 4) := le_max_left _ _
      _ ≤ max 1 (max (C₁ * (Real.pi / 2)) (M * Real.pi ^ 2 / 4)) := le_max_right _ _
  have hMle : M * Real.pi ^ 2 / 4 ≤ Cm := by
    rw [hCm]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Cm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCm]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro θ hθ
    have hsin := (ssb_min_le_sin hθ).1
    calc |h θ| ≤ C₁ * Real.sin (2 * θ) := hC₁h θ hθ
      _ ≤ Cm * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hC₁le hsin.le
  · intro θ hθ
    exact le_trans (hC₁d θ hθ) hC₁le
  · intro θ hθ
    have hsin := (ssb_min_le_sin hθ).1
    have hdiv : |SinQ h θ| = |h θ| / Real.sin (2 * θ) := by
      simp only [SinQ, abs_div, abs_of_pos hsin]
    rw [hdiv, div_le_iff₀ hsin]
    calc |h θ| ≤ C₁ * Real.sin (2 * θ) := hC₁h θ hθ
      _ ≤ Cm * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hC₁le hsin.le
  · intro θ hθ
    have hsin := (ssb_min_le_sin hθ).1
    have hs2 : 0 < (Real.sin (2 * θ)) ^ 2 := by positivity
    have hkey := ssb_derivSinQ h hC2 hθ
    have hmin0 : 0 ≤ min θ (Real.pi / 2 - θ) :=
      le_min (le_of_lt hθ.1) (by linarith [hθ.2])
    have hmin2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2 * Real.sin (2 * θ)) ^ 2 :=
      pow_le_pow_left₀ hmin0 (ssb_min_le_sin hθ).2 2
    have hb : |ssbW h θ| ≤ M * (Real.pi / 2 * Real.sin (2 * θ)) ^ 2 :=
      le_trans (hMW θ hθ) (mul_le_mul_of_nonneg_left hmin2 hM0)
    have hdiv : |ssbW h θ / (Real.sin (2 * θ)) ^ 2| = |ssbW h θ| / (Real.sin (2 * θ)) ^ 2 := by
      rw [abs_div, abs_of_pos hs2]
    rw [hkey, hdiv]
    calc |ssbW h θ| / (Real.sin (2 * θ)) ^ 2
        ≤ (M * (Real.pi / 2 * Real.sin (2 * θ)) ^ 2) / (Real.sin (2 * θ)) ^ 2 :=
          div_le_div_of_nonneg_right hb hs2.le
      _ = M * Real.pi ^ 2 / 4 := by
          rw [show M * (Real.pi / 2 * Real.sin (2 * θ)) ^ 2
                = (M * (Real.pi ^ 2 / 4)) * (Real.sin (2 * θ)) ^ 2 by ring]
          rw [mul_div_cancel_right₀ _ (ne_of_gt hs2)]
          ring
      _ ≤ Cm := hMle

end Work.Elliptic
