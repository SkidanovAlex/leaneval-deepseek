import Mathlib
import Submission.Work.Drive.KnotDefs
import Submission.Work.Drive.knot_tangent_monotone_oneSided

/-!
# Local transverse structure of a smooth knot at a point

The target of this file is `Work.Drive.transverse_structure_local`: at *every* parameter `tb` of a
smooth knot `r` (`IsSmoothKnot r`, so `r` is **analytic**, `period`-periodic, simple on a period and
regular) there is a nonzero vector `n` orthogonal to the velocity `velocity r tb` together with a
`δ > 0` such that, on the left half-neighbourhood `(tb - δ, tb)` of `tb`,

* the curve lies strictly on the negative side of the affine hyperplane through `r tb` with normal
  `n`: `0 < ⟪n, r tb - r θ⟫`, and
* the projected coordinate `θ ↦ ⟪n, r θ⟫` is nondecreasing.

The very same statement, with the single extra hypothesis

`hnd : ∃ k ≥ 2, iteratedDeriv k r tb ∉ Submodule.span ℝ {velocity r tb}`,

is the colleague lemma `Work.Drive.knot_tangent_monotone_oneSided` (proved in
`knot_tangent_monotone_oneSided.lean` by a Taylor-with-Lagrange-remainder argument).  So the only
mathematical content of this file is the *non-flatness* input `hnd`: some iterated derivative of
`r` at `tb` of order at least `2` is not parallel to the velocity.

## Why `hnd` holds

Suppose, on the contrary, that `iteratedDeriv k r tb ∈ ℝ ∙ velocity r tb` for all `k ≥ 2`; since
`iteratedDeriv 1 r tb = velocity r tb` this is saying that **all** iterated derivatives of `r` at
`tb` lie in the line `ℝ ∙ velocity r tb`.  Then the *deviation* from the tangent line,

`t ↦ r t - r tb - ⟪w, r t - r tb⟫ / ‖w‖² • w`,  (`w = velocity r tb`),

is an analytic function all of whose iterated derivatives at `tb` vanish, so by the analytic order
theory (`analyticOrderAt_eq_top`, `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`) it
vanishes on a neighbourhood of `tb`.  As it is analytic on all of `ℝ` and `ℝ` is preconnected, the
*identity principle* (`AnalyticOnNhd.eq_of_eventuallyEq`) upgrades this to vanishing everywhere:
the whole curve lies in the affine line `r tb + ℝ ∙ w`.

Writing `c t := ⟪w, r t - r tb⟫ / ‖w‖²` we get `r t = r tb + c t • w` for all `t`; hence
`c` is `period`-periodic, and since `velocity r t = (deriv c t) • w ≠ 0` (regularity) we have
`deriv c t ≠ 0` everywhere.  Rolle's theorem on `[0, period]` then produces `ξ` with
`deriv c ξ = 0` — a contradiction.

This is where the analyticity of `r` is used in an essential way: for a merely smooth knot the
statement would be **false** (a rounded polygon has straight pieces, at whose interior points no
such `n` exists, since the curve is exactly linear there). -/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

noncomputable section

/-! ### Two elementary helpers -/

/-- The continuous linear functional used to detect the component of a vector along `w`:
it is `‖w‖⁻²` times the scalar product with `w`, so that `spanVelocityFunctional w w = 1` for
`w ≠ 0`. -/
def spanVelocityFunctional (w : Space) : Space →L[ℝ] ℝ := (‖w‖^2)⁻¹ • innerSL ℝ w

lemma spanVelocityFunctional_self {w : Space} (hw : w ≠ 0) : spanVelocityFunctional w w = 1 := by
  rw [spanVelocityFunctional, smul_apply, smul_eq_mul]
  rw [show innerSL ℝ w w = inner ℝ w w from rfl, real_inner_self_eq_norm_sq]
  field_simp

/-- The **deviation from the tangent line** at `x` in direction `w`:
`t ↦ f t - f x - (the component of f t - f x along w) • w`.  It vanishes exactly when `f` is
locally affine with direction `w`. -/
def spanVelocityDeviation (f : ℝ → Space) (x : ℝ) (w : Space) : ℝ → Space :=
  fun t => f t - f x - (spanVelocityFunctional w (f t - f x)) • w

/-! ### Analytic functions flat at a point vanish locally -/

/-- **An analytic function all of whose iterated derivatives vanish at a point vanishes on a
neighbourhood of that point.**  This is the "order is infinite" characterization of
`analyticOrderAt`. -/
lemma eventuallyEq_zero_of_forall_iteratedDeriv_eq_zero {f : ℝ → Space} {x : ℝ}
    (hf : ContDiff ℝ ⊤ f) (h : ∀ k : ℕ, iteratedDeriv k f x = 0) : f =ᶠ[𝓝 x] 0 := by
  have han : AnalyticAt ℝ f x := hf.analyticOnNhd (s := Set.univ) x (Set.mem_univ x)
  have htop : analyticOrderAt f x = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han]
    exact fun i _ => h i
  exact analyticOrderAt_eq_top.mp htop

/-! ### The deviation from the tangent line is flat -/

/-- **If all iterated derivatives of `f` at `x` of order `≥ 1` are parallel to a fixed nonzero
vector `w`, then every iterated derivative of `f - f x - (the `w`-component) • w` at `x` vanishes.**

Indeed, for `k ≥ 1` the `k`-th derivative of the deviation at `x` is
`iteratedDeriv k f x - spanVelocityFunctional w (iteratedDeriv k f x) • w`, and this is zero
because `iteratedDeriv k f x = a • w` with `spanVelocityFunctional w w = 1`. -/
lemma iteratedDeriv_deviation_eq_zero {f : ℝ → Space} {x : ℝ} {w : Space}
    (hf : ContDiff ℝ ⊤ f) (hw : w ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → iteratedDeriv k f x ∈ Submodule.span ℝ {w}) :
    ∀ k : ℕ, iteratedDeriv k (spanVelocityDeviation f x w) x = 0 := by
  have hg : ContDiff ℝ ⊤ (fun t : ℝ => f t - f x) := by fun_prop
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => spanVelocityFunctional w (f t - f x)) := by fun_prop
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [iteratedDeriv_zero]
    simp [spanVelocityDeviation]
  · have hA : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t : ℝ => f t - f x) x :=
      (hg.contDiffAt (x := x)).of_le le_top
    have hB : ContDiffAt ℝ (k : WithTop ℕ∞)
        (fun t : ℝ => (spanVelocityFunctional w (f t - f x)) • w) x :=
      ((hc.contDiffAt (x := x)).of_le le_top).smul_const w
    rw [show spanVelocityDeviation f x w
        = (fun t : ℝ => f t - f x)
          - (fun t : ℝ => (spanVelocityFunctional w (f t - f x)) • w) from rfl,
      iteratedDeriv_sub hA hB]
    have h1 : iteratedDeriv k (fun t : ℝ => f t - f x) x = iteratedDeriv k f x := by
      rw [show (fun t : ℝ => f t - f x) = f - (fun _ => f x) from rfl,
        iteratedDeriv_sub (hf.contDiffAt.of_le le_top) (contDiffAt_const (c := f x)),
        iteratedDeriv_const]
      simp [hkpos.ne']
    have h2 : iteratedDeriv k (fun t : ℝ => (spanVelocityFunctional w (f t - f x)) • w) x
        = (spanVelocityFunctional w (iteratedDeriv k f x)) • w := by
      rw [iteratedDeriv_smul_const ((hc.contDiffAt (x := x)).of_le le_top) w]
      congr 1
      rw [show (fun t : ℝ => spanVelocityFunctional w (f t - f x))
            = spanVelocityFunctional w ∘ (fun t : ℝ => f t - f x) from rfl,
          iteratedDeriv_comp_clm hg (spanVelocityFunctional w) k x, h1]
    rw [h1, h2]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h k hkpos)
    have hL : spanVelocityFunctional w (a • w) = a := by
      rw [map_smul, spanVelocityFunctional_self hw, smul_eq_mul, mul_one]
    rw [← ha, hL, sub_self]

/-! ### Non-flatness of a smooth knot at every point -/

/-- **At every parameter of a smooth knot some iterated derivative of order at least `2` is not
parallel to the velocity.**  Equivalently, the knot is nowhere -- locally -- a straight line, which
is exactly where the analyticity of the knot is used; see the discussion at the top of the file. -/
theorem exists_iteratedDeriv_not_mem_span_velocity {r : ℝ → Space} (hr : IsSmoothKnot r)
    (tb : ℝ) :
    ∃ k : ℕ, 2 ≤ k ∧ iteratedDeriv k r tb ∉ Submodule.span ℝ {velocity r tb} := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  set v : Space := velocity r tb with hv
  have hv0 : v ≠ 0 := by rw [hv]; exact hr.regular tb
  have hper : 0 < period := by rw [period]; positivity
  -- all iterated derivatives of `r` at `tb` are parallel to `v`
  have hGderiv : ∀ k : ℕ, iteratedDeriv k (spanVelocityDeviation r tb v) tb = 0 := by
    refine iteratedDeriv_deviation_eq_zero hr.smooth hv0 ?_
    intro k hk
    rcases k with _ | _ | k
    · omega
    · refine Submodule.mem_span_singleton.mpr ⟨1, ?_⟩
      rw [iteratedDeriv_one, one_smul]
      exact hv
    · rw [hv]
      exact hcon (k + 2) (by omega)
  have hBase : ContDiff ℝ ⊤ (fun t : ℝ => r t - r tb) := hr.smooth.sub contDiff_const
  have hFdiff : ContDiff ℝ ⊤ (fun t : ℝ => (spanVelocityFunctional v (r t - r tb)) • v) :=
    ((ContinuousLinearMap.contDiff (spanVelocityFunctional v)).comp hBase).smul_const v
  have hGcont : ContDiff ℝ ⊤ (spanVelocityDeviation r tb v) := by
    show ContDiff ℝ ⊤ (fun t : ℝ => r t - r tb - (spanVelocityFunctional v (r t - r tb)) • v)
    exact hBase.sub hFdiff
  -- flat at `tb`, hence zero on a neighbourhood of `tb`, hence zero everywhere
  have hGloc : spanVelocityDeviation r tb v =ᶠ[𝓝 tb] 0 :=
    eventuallyEq_zero_of_forall_iteratedDeriv_eq_zero hGcont hGderiv
  have hGglob : spanVelocityDeviation r tb v = 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq hGcont.analyticOnNhd analyticOnNhd_const hGloc
  -- the whole curve lies on the line `r tb + ℝ ∙ v`
  set c : ℝ → ℝ := fun t => spanVelocityFunctional v (r t - r tb) with hcdef
  have hcdiff : ContDiff ℝ ⊤ c := by
    rw [hcdef]
    exact (ContinuousLinearMap.contDiff (spanVelocityFunctional v)).comp hBase
  have hrc : ∀ t : ℝ, r t = r tb + (c t) • v := by
    intro t
    have h := congrFun hGglob t
    simp only [spanVelocityDeviation, Pi.zero_apply] at h
    have h2 : r t - r tb = (spanVelocityFunctional v (r t - r tb)) • v := sub_eq_zero.mp h
    have h3 : c t = spanVelocityFunctional v (r t - r tb) := by rw [hcdef]
    rw [h3, ← h2]
    abel
  -- `c` is periodic ...
  have hcper : ∀ t : ℝ, c (t + period) = c t := by
    intro t
    have h1 := hrc (t + period)
    have h2 := hrc t
    rw [hr.periodic t] at h1
    rw [h2] at h1
    have h5 : c t • v = c (t + period) • v := add_left_cancel h1
    have h6 : (c (t + period) - c t) • v = 0 := by rw [sub_smul, h5, sub_self]
    rcases smul_eq_zero.mp h6 with h7 | h7
    · linarith
    · exact absurd h7 hv0
  -- ... and has nowhere-vanishing derivative, by regularity of the knot
  have hderivc : ∀ x : ℝ, velocity r x = (deriv c x) • v := by
    intro x
    have hcd : DifferentiableAt ℝ c x := (hcdiff.differentiable (by simp)).differentiableAt
    have hfun : r = fun t : ℝ => r tb + (c t) • v := funext hrc
    show deriv r x = (deriv c x) • v
    rw [hfun]
    have hder : deriv (fun t : ℝ => r tb + (c t) • v) x
        = deriv (fun t : ℝ => (c t) • v) x :=
      deriv_const_add (f := fun t : ℝ => (c t) • v) (r tb)
    rw [hder]
    exact (hcd.hasDerivAt.smul_const v).deriv
  have hderivc_ne : ∀ x : ℝ, deriv c x ≠ 0 := by
    intro x h0
    have h := hderivc x
    rw [h0, zero_smul] at h
    exact hr.regular x h
  -- Rolle on `[0, period]` gives the contradiction
  have hcont : ContinuousOn c (Set.Icc 0 period) := hcdiff.continuous.continuousOn
  have heq : c 0 = c period := by
    have h := hcper 0
    simpa using h.symm
  obtain ⟨xi, hxi, hxid⟩ := exists_deriv_eq_zero (f := c) hper hcont heq
  exact hderivc_ne xi hxid

/-! ### The target -/

theorem transverse_structure_local {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) (tb : ℝ) :
    ∃ n : LeanEval.KnotTheory.Quadrisecant.Space, n ≠ 0 ∧
      inner ℝ n (LeanEval.KnotTheory.Quadrisecant.velocity r tb) = 0 ∧ ∃ δ : ℝ, 0 < δ ∧
      (∀ θ : ℝ, tb - δ < θ → θ < tb → 0 < inner ℝ n (r tb - r θ)) ∧
      (∀ θ₁ θ₂ : ℝ, tb - δ < θ₁ → θ₁ ≤ θ₂ → θ₂ < tb →
        inner ℝ n (r tb - r θ₂) ≤ inner ℝ n (r tb - r θ₁)) :=
  knot_tangent_monotone_oneSided hr.smooth (hr.regular tb)
    (exists_iteratedDeriv_not_mem_span_velocity hr tb)

end

end Work.Drive
