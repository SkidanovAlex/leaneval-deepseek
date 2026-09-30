/-
Copyright: work-in-progress area `Profiles` of the aspherical 4-manifold project.

# Filling profiles for the cusp filling of the Ratcliffe–Tschantz manifold

This file fixes the language of the area: the structure `FillProfile` of a pair of
warping profiles `(f, h)` for the metric `dr² + f(r)² dθ² + h(r)² |dw|²` on the
filling piece `[-1,1]² × T²`, together with the concrete building blocks used to
*smooth* a convex, monotone model function into a profile.

Everything is stated for `E4`-free real analysis; the geometry lives in `Cusp/` and
`Curvature/`.

## Main definitions

* `Work.Profiles.FillProfile` — the structure promised to the `CUSP`/`CURV` areas.
* `Work.Profiles.eta` — a fixed nonnegative symmetric `C^∞` bump supported in
  `[-1/4, 1/4]` with total mass `1`.
* `Work.Profiles.mEta` — the constant `∫ e^{-t} η(t) dt`, used to normalise the
  cusp constant.
* `Work.Profiles.prof F η` — the smoothing `x ↦ ∫ t, F (x - t) η t dt`.
* `Work.Profiles.tangentExp K`, `Ffun K`, `Hfun h₀ K` — the convex model functions
  that are smoothed into the profiles.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ContDiff

open MeasureTheory

namespace Work.Profiles

/-- A pair of filling profiles: `f` is the length of the `θ`-circle, `h` the length of
the `w`-directions of the filling piece.

`f` is the identity (`f r = r`, the flat core) on `[0, 1/2]` and `C e^r` (the hyperbolic
rate) on `[3, ∞)`; `h` is the constant `h₀` on `[0, 1/2]` and `D e^r` on `[3, ∞)`.  Both
are smooth, positive, nondecreasing with nondecreasing derivative (convex).

**Smoothness is `ContDiff ℝ ∞`, not `ContDiff ℝ ⊤`.**  In this Mathlib pin `⊤ = ω` on
`ℕ∞ω` means *analytic* (`contDiff_omega_iff_analyticOnNhd`), and a profile is provably never
analytic: an analytic `f` with `f = id` on `[0, 1/2]` equals `id` on all of `ℝ` by the
identity theorem, which contradicts `f r = C e^r` for `r ≥ 3`.  See
`Work.Profiles.no_analytic_profile`.  `ContDiff ℝ ∞` is exactly "smooth", which is what the
convolution construction delivers and what the metric-side arguments use. -/
structure FillProfile where
  (C D h₀ : ℝ)
  (f h : ℝ → ℝ)
  (f_smooth : ContDiff ℝ ∞ f)
  (h_smooth : ContDiff ℝ ∞ h)
  (f_core : ∀ r ≤ 1/2, f r = r)
  (h_core : ∀ r ≤ 1/2, h r = h₀)
  (f_cusp : ∀ r ≥ 3, f r = C * Real.exp r)
  (h_cusp : ∀ r ≥ 3, h r = D * Real.exp r)
  (f_pos : ∀ r > 0, 0 < f r)
  (h_pos : ∀ r, 0 < h r)
  (f_mono : ∀ r, 0 ≤ deriv f r)
  (h_mono : ∀ r, 0 ≤ deriv h r)
  (f_convex : ∀ r, 0 ≤ deriv^[2] f r)
  (h_convex : ∀ r, 0 ≤ deriv^[2] h r)

namespace FillProfile

variable (P : FillProfile)

/-- The constant `h₀` is positive: it is the value of the everywhere-positive `h`. -/
theorem h₀_pos : 0 < P.h₀ := by
  have := P.h_pos 0
  rwa [P.h_core 0 (by norm_num)] at this

/-- The cusp constant `C` is positive, being `f 3 / e^3`. -/
theorem C_pos : 0 < P.C := by
  have h := P.f_pos 3 (by norm_num)
  rw [P.f_cusp 3 le_rfl] at h
  exact pos_of_mul_pos_left h (Real.exp_pos 3).le

/-- The cusp constant `D` is positive, being `h 3 / e^3`. -/
theorem D_pos : 0 < P.D := by
  have h := P.h_pos 3
  rw [P.h_cusp 3 le_rfl] at h
  exact pos_of_mul_pos_left h (Real.exp_pos 3).le

/-- `f` is `C^n` for every finite `n` (in particular `C²`). -/
theorem f_contDiff (n : ℕ) : ContDiff ℝ (↑n) P.f :=
  P.f_smooth.of_le (WithTop.coe_le_coe.mpr le_top)

/-- `h` is `C^n` for every finite `n` (in particular `C²`). -/
theorem h_contDiff (n : ℕ) : ContDiff ℝ (↑n) P.h :=
  P.h_smooth.of_le (WithTop.coe_le_coe.mpr le_top)

theorem f_differentiable : Differentiable ℝ P.f := P.f_smooth.differentiable (by simp)

theorem h_differentiable : Differentiable ℝ P.h := P.h_smooth.differentiable (by simp)

theorem f_continuous : Continuous P.f := P.f_differentiable.continuous

theorem h_continuous : Continuous P.h := P.h_differentiable.continuous

/-- `f` is nondecreasing (`f_mono` at every point, together with differentiability). -/
theorem f_monotone : Monotone P.f :=
  monotone_of_deriv_nonneg (P.f_smooth.differentiable (by simp)) (fun r => P.f_mono r)

/-- `h` is nondecreasing. -/
theorem h_monotone : Monotone P.h :=
  monotone_of_deriv_nonneg (P.h_smooth.differentiable (by simp)) (fun r => P.h_mono r)

/-- `f` is convex. -/
theorem f_convexOn : ConvexOn ℝ Set.univ P.f :=
  convexOn_univ_of_deriv2_nonneg (P.f_smooth.differentiable (by simp))
    ((P.f_smooth.iterate_deriv 1).differentiable (by simp))
    (fun r => P.f_convex r)

/-- `h` is convex. -/
theorem h_convexOn : ConvexOn ℝ Set.univ P.h :=
  convexOn_univ_of_deriv2_nonneg (P.h_smooth.differentiable (by simp))
    ((P.h_smooth.iterate_deriv 1).differentiable (by simp))
    (fun r => P.h_convex r)

/-- `f` is positive at least where it is the identity. -/
theorem f_pos_of_mem_Ioc {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1/2) : 0 < P.f r := by
  rw [P.f_core r hr']; exact hr

end FillProfile

/-- The standard symmetric `C^∞` bump: supported in `[-1/4, 1/4]`, equal to `1` on
`[-1/8, 1/8]`. -/
noncomputable def baseBump : ContDiffBump (0 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩

/-- A fixed nonnegative symmetric `C^∞` bump function supported in `[-1/4, 1/4]` with
total mass `1`. -/
noncomputable def eta : ℝ → ℝ := baseBump.normed volume

/-- The normalisation constant `∫ e^{-t} η(t) dt ∈ (0, e^{1/4}]`.  Normalising the cusp
constant `C` by `mEta` is what makes the smoothed model equal `C e^r` in the cusp. -/
noncomputable def mEta : ℝ := ∫ t, Real.exp (-t) * eta t

/-- Smoothing of a model function `F` against a bump `η`:
`prof F η x = ∫ t, F (x - t) η t`.  For a smooth compactly supported `η` this is smooth
whenever `F` is continuous, and it preserves convexity, monotonicity and any lower
affine bound satisfied by `F`. -/
noncomputable def prof (F η : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t, F (x - t) * η t

/-- The tangent extension of `K e^r` at `2`: it equals `K * Real.exp r` for `r ≥ 2` and the
tangent line `K * Real.exp 2 * (r - 1)` at `2` for `r ≤ 2`.

It is defined as the primitive of the (continuous, nondecreasing) function
`r ↦ K * Real.exp (max r 2)` taking the value `K * Real.exp 2` at `r = 2`, which makes its
differentiability and convexity immediate from the fundamental theorem of calculus:
`deriv (tangentExp K) = fun r => K * Real.exp (max r 2)`. -/
noncomputable def tangentExp (K : ℝ) (r : ℝ) : ℝ :=
  K * Real.exp 2 + ∫ s in (2 : ℝ)..r, K * Real.exp (max s 2)

/-- The model for the profile `f`: `max (id) (tangentExp K)`. -/
noncomputable def Ffun (K : ℝ) (r : ℝ) : ℝ := max r (tangentExp K r)

/-- The model for the profile `h`: `max h₀ (tangentExp K)`. -/
noncomputable def Hfun (h₀ K : ℝ) (r : ℝ) : ℝ := max h₀ (tangentExp K r)

end Work.Profiles
