/-
# `Work.StabilityFar.Basic` — elementary lemmas for the far-field layer

Support transport (the vorticity's support stays in a fixed ball), the support of the *time
derivative* of a supported vorticity, the bookkeeping for the two blocks `blockDeriv` of the
derivative of `u.uncurry`, and the elementary facts about the regions `farRegion`/`coreRegion`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.StabilityFar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-! ## The regions -/

theorem isOpen_farRegion (ρ : ℝ) : IsOpen (farRegion ρ) :=
  isOpen_lt continuous_const continuous_norm

theorem isClosed_coreRegion (ρ : ℝ) : IsClosed (coreRegion ρ) :=
  isClosed_le continuous_norm continuous_const

/-- The points of the segment between a far point `x` and a point at distance `≤ 1` from it stay
far: with `x + t(y-x)`, `t ∈ [0,1]`, the displacement from `x` has norm `≤ 1`. -/
theorem farRegion_segment {ρ : ℝ} {x y : R3} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hxy : ‖x - y‖ ≤ 1) (hx : ρ + 1 < ‖x‖) : ρ < ‖x + t • (y - x)‖ := by
  have h1 : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hxy' : ‖y - x‖ ≤ 1 := by rw [norm_sub_rev]; exact hxy
  have h2 : ‖x + t • (y - x) - x‖ ≤ 1 := by
    rw [h1]
    calc t * ‖y - x‖ ≤ 1 * 1 := mul_le_mul ht.2 hxy' (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have h3 : ‖x‖ ≤ ‖x + t • (y - x)‖ + ‖x + t • (y - x) - x‖ := by
    have heq : x = (x + t • (y - x)) - t • (y - x) := by abel
    calc ‖x‖ = ‖(x + t • (y - x)) - t • (y - x)‖ := by rw [← heq]
      _ ≤ ‖x + t • (y - x)‖ + ‖t • (y - x)‖ := norm_sub_le _ _
      _ = ‖x + t • (y - x)‖ + ‖x + t • (y - x) - x‖ := by
          rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  linarith

/-- Every point of a closed interval `[0,T]`, `T > 0`, is uniquely differentiable within it.
(For `T > 0` the interval is convex with non-empty interior, so
`uniqueDiffWithinAt_convex` applies at every point of its closure.) -/
theorem uniqueDiffWithinAt_Icc {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) T) t :=
  uniqueDiffWithinAt_convex (convex_Icc 0 T)
    ⟨T / 2, by rw [interior_Icc]; exact ⟨by linarith, by linarith⟩⟩ (subset_closure ht)

/-! ## Support transport -/

/-- **`St4(a)`: the support of the vorticity stays in a fixed ball.**

If every slice of `ω` is contained in the image of the initial slice under the flow `φ`, if the
initial slice is contained in the ball of radius `R`, and if the flow grows at most by the factor
`E` on the window, then every slice is supported in the ball of radius `E·R`.

For the cut-off solution `ω` is the vorticity of the classical solution with datum `ω₀^L`, the
Lagrangian identity gives the image statement
(`Work.LWP.Transport.support_transport`), and the growth bound follows from the Grönwall bound on
the flow (`Work.LWP.flow_lipschitzOnWith`) together with the a priori `C^{1,α}` bound on `∇u`. -/
theorem slicesSupported_of_image {ω φ : R3 → ℝ → R3} {T R E : ℝ} (hE : 0 ≤ E)
    (him : ∀ t ∈ window T,
      Function.support (ω · t) ⊆ (fun x => φ x t) '' Function.support (ω · 0))
    (hball : ∀ x, x ∈ Function.support (ω · 0) → ‖x‖ ≤ R)
    (hflow : ∀ t ∈ window T, ∀ x : R3, ‖φ x t‖ ≤ E * ‖x‖) :
    SlicesSupported ω (E * R) T := by
  intro t ht y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨x, hx, rfl⟩ := him t ht (by simpa [Function.mem_support] using hy)
  calc ‖φ x t‖ ≤ E * ‖x‖ := hflow t ht x
    _ ≤ E * R := mul_le_mul_of_nonneg_left (hball x hx) hE

/-! ## The support of the time derivative -/

/-- If a slice of `ω` vanishes in a neighbourhood of `t`, then so does `∂ₜω` at `t`: the time
derivative of a function that is identically zero on a neighbourhood is zero. -/
theorem timeDeriv_eq_zero_of_eventuallyEq_zero {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, ω x s = 0) : timeDeriv ω x t = 0 := by
  have h1 : (fun s => ω x s) =ᶠ[𝓝 t] (fun _ => (0 : R3)) := h
  have h2 : deriv (fun s => ω x s) t = deriv (fun _ : ℝ => (0 : R3)) t := h1.deriv_eq
  simpa [timeDeriv] using h2

/-- **A one-sided vanishing criterion for `deriv`.**  If `s ↦ ω x s` vanishes on `[t, t+ε)`, then
its derivative at `t` is `0`: either `ω x` is not differentiable at `t` (and `deriv` defaults to
`0`), or it is, and then its derivative equals the right-hand (within-`Ioi t`) derivative, which
is the derivative of the zero function. -/
theorem timeDeriv_eq_zero_of_eq_zero_on_Ico {ω : R3 → ℝ → R3} {x : R3} {t ε : ℝ} (hε : 0 < ε)
    (h : ∀ s ∈ Set.Ico t (t + ε), ω x s = 0) : timeDeriv ω x t = 0 := by
  show deriv (fun s => ω x s) t = 0
  by_cases hd : DifferentiableAt ℝ (fun s => ω x s) t
  · have h1 : HasDerivWithinAt (fun s => ω x s) (deriv (fun s => ω x s) t) (Set.Ioi t) t :=
      hd.hasDerivAt.hasDerivWithinAt
    have hev : (fun s => ω x s) =ᶠ[𝓝[Set.Ioi t] t] (fun _ => (0 : R3)) := by
      have hmem : (Set.Ioi t ∩ Set.Iio (t + ε)) ∈ 𝓝[Set.Ioi t] t :=
        Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds ((isOpen_Iio (a := t + ε)).mem_nhds
            (by simp only [Set.mem_Iio]; linarith)))
      exact Filter.mem_of_superset hmem (fun s hs => h s ⟨hs.1.le, hs.2⟩)
    have h2 : derivWithin (fun s => ω x s) (Set.Ioi t) t = 0 := by
      rw [Filter.EventuallyEq.derivWithin_eq hev (h t ⟨le_refl t, by linarith⟩)]
      exact congrFun (derivWithin_zero (𝕜 := ℝ) (F := R3) (s := Set.Ioi t)) t
    rw [← h1.derivWithin (uniqueDiffWithinAt_Ioi t), h2]
  · exact deriv_zero_of_not_differentiableAt hd

/-- The mirror image of `timeDeriv_eq_zero_of_eq_zero_on_Ico`: vanishing on `(t-ε, t]` forces
`deriv ω x t = 0`. -/
theorem timeDeriv_eq_zero_of_eq_zero_on_Ioc {ω : R3 → ℝ → R3} {x : R3} {t ε : ℝ} (hε : 0 < ε)
    (h : ∀ s ∈ Set.Ioc (t - ε) t, ω x s = 0) : timeDeriv ω x t = 0 := by
  show deriv (fun s => ω x s) t = 0
  by_cases hd : DifferentiableAt ℝ (fun s => ω x s) t
  · have h1 : HasDerivWithinAt (fun s => ω x s) (deriv (fun s => ω x s) t) (Set.Iio t) t :=
      hd.hasDerivAt.hasDerivWithinAt
    have hev : (fun s => ω x s) =ᶠ[𝓝[Set.Iio t] t] (fun _ => (0 : R3)) := by
      have hmem : (Set.Iio t ∩ Set.Ioi (t - ε)) ∈ 𝓝[Set.Iio t] t :=
        Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds ((isOpen_Ioi (a := t - ε)).mem_nhds
            (by simp only [Set.mem_Ioi]; linarith)))
      exact Filter.mem_of_superset hmem (fun s hs => h s ⟨hs.2, hs.1.le⟩)
    have h2 : derivWithin (fun s => ω x s) (Set.Iio t) t = 0 := by
      rw [Filter.EventuallyEq.derivWithin_eq hev (h t ⟨by linarith, le_refl t⟩)]
      exact congrFun (derivWithin_zero (𝕜 := ℝ) (F := R3) (s := Set.Iio t)) t
    rw [← h1.derivWithin (uniqueDiffWithinAt_Iio t), h2]
  · exact deriv_zero_of_not_differentiableAt hd

/-- **`St4(b)`, the support claim for `∂ₜω`.**  If every slice of `ω` is supported in the ball of
radius `R` on the window, then the same is true of every slice of `∂ₜω`: at a point of the window
the function `s ↦ ω(y,s)`, `‖y‖ > R`, vanishes on a one-sided neighbourhood of `t`, and
`timeDeriv_eq_zero_of_eq_zero_on_Ico`/`_on_Ioc` apply.  (This is the claim that makes the
far-field estimates for `∂ₜu = BS(∂ₜω)` available.) -/
theorem slicesSupported_timeDeriv {ω : R3 → ℝ → R3} {R T : ℝ} (hT : 0 ≤ T)
    (h : SlicesSupported ω R T) :
    SlicesSupported (timeDeriv ω) R T := by
  intro t ht y hy
  by_contra hmem
  have hy' : R < ‖y‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact lt_of_not_ge hmem
  have hvan : ∀ s ∈ window T, ω y s = 0 := by
    intro s hs
    by_contra hne
    have := h s hs y hne
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · refine hy (timeDeriv_eq_zero_of_eq_zero_on_Ico (ε := T + 1 - t) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩
  · refine hy (timeDeriv_eq_zero_of_eq_zero_on_Ioc (ε := T + 2) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1], by linarith [heq, hs.2]⟩


/-! ## The two blocks of `fderiv u.uncurry` -/

/-- The operator norm of `blockDeriv` is at most the sum of the operator norms of its two
blocks. -/
theorem norm_blockDeriv_le (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    ‖blockDeriv u (x, t)‖ ≤ ‖fderiv ℝ (u · t) x‖ + ‖timeDeriv u x t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
  obtain ⟨v, s⟩ := w
  rw [blockDeriv_apply]
  have hD : 0 ≤ ‖fderiv ℝ (u · t) x‖ := norm_nonneg _
  have hT : 0 ≤ ‖timeDeriv u x t‖ := norm_nonneg _
  calc ‖fderiv ℝ (u · t) x v + s • timeDeriv u x t‖
      ≤ ‖fderiv ℝ (u · t) x v‖ + ‖s • timeDeriv u x t‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (u · t) x‖ * ‖v‖ + ‖s‖ * ‖timeDeriv u x t‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (le_of_eq (norm_smul s _))
    _ ≤ (‖fderiv ℝ (u · t) x‖ + ‖timeDeriv u x t‖) * ‖(v, s)‖ := by
        rw [Prod.norm_def]
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left ‖v‖ ‖s‖) hD,
          mul_le_mul_of_nonneg_left (le_max_right ‖v‖ ‖s‖) hT]

/-- The difference of two `blockDeriv`s is bounded by the sum of the differences of the two
blocks. -/
theorem norm_blockDeriv_sub_le (u : R3 → ℝ → R3) (x y : R3) (t τ : ℝ) :
    ‖blockDeriv u (x, t) - blockDeriv u (y, τ)‖
      ≤ ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖ + ‖timeDeriv u x t - timeDeriv u y τ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
  obtain ⟨v, s⟩ := w
  have happ : (blockDeriv u (x, t) - blockDeriv u (y, τ)) (v, s)
      = (fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y) v
        + s • (timeDeriv u x t - timeDeriv u y τ) := by
    rw [_root_.sub_apply, blockDeriv_apply, blockDeriv_apply, _root_.sub_apply]
    module
  rw [happ]
  have hD : 0 ≤ ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖ := norm_nonneg _
  have hT : 0 ≤ ‖timeDeriv u x t - timeDeriv u y τ‖ := norm_nonneg _
  calc ‖(fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y) v
        + s • (timeDeriv u x t - timeDeriv u y τ)‖
      ≤ ‖(fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y) v‖
          + ‖s • (timeDeriv u x t - timeDeriv u y τ)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖ * ‖v‖
          + ‖s‖ * ‖timeDeriv u x t - timeDeriv u y τ‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (le_of_eq (norm_smul s _))
    _ ≤ (‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖
          + ‖timeDeriv u x t - timeDeriv u y τ‖) * ‖(v, s)‖ := by
        rw [Prod.norm_def]
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left ‖v‖ ‖s‖) hD,
          mul_le_mul_of_nonneg_left (le_max_right ‖v‖ ‖s‖) hT]

/-! ## The mean value inequality along a segment -/

/-- **Mean value inequality along a segment**, in the form used for the far-field estimates: if
`f` is differentiable along the segment `[x,y]` and its derivative is bounded by `A` there, then
`‖f y - f x‖ ≤ A‖y - x‖`.  (The far region is not convex, so this is applied to the parametrised
segment `t ↦ x + t(y-x)`, where the estimate `‖x + t(y-x)‖ ≥ ‖x‖ - 1` keeps the segment inside
the region on which the derivative bound holds.) -/
theorem norm_sub_le_of_fderiv_le_segment {f : R3 → R3} {x y : R3} {A : ℝ}
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • (y - x)))
    (hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ f (x + t • (y - x))‖ ≤ A) :
    ‖f y - f x‖ ≤ A * ‖y - x‖ := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
    intro t
    have h := (hasDerivAt_id t).smul_const (y - x)
    have h' : HasDerivAt (fun s : ℝ => s • (y - x)) ((1 : ℝ) • (y - x)) t := h
    simpa using h'.const_add x
  have hcomp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => f (x + s • (y - x)))
        (fderiv ℝ f (x + t • (y - x)) (y - x)) (Set.Icc 0 1) t := by
    intro t ht
    exact ((hdiff t ht).hasFDerivAt.comp_hasDerivWithinAt t ((hderiv t).hasDerivWithinAt))
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ f (x + t • (y - x)) (y - x)‖ ≤ A * ‖y - x‖ := by
    intro t ht
    calc ‖fderiv ℝ f (x + t • (y - x)) (y - x)‖
        ≤ ‖fderiv ℝ f (x + t • (y - x))‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ A * ‖y - x‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => f (x + s • (y - x)))
    (f' := fun t => fderiv ℝ f (x + t • (y - x)) (y - x)) (a := 0) (b := 1) hcomp hbound 1
    (right_mem_Icc.mpr zero_le_one)
  simpa using hmain

end Work.StabilityFar
