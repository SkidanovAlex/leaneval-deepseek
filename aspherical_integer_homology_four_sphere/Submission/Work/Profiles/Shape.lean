/-
Copyright: area `Profiles` of the aspherical 4-manifold project.

# The model functions `Ffun` and `Hfun`

`Ffun K r = max r (tangentExp K r)` is the model that is smoothed into the profile `f`, and
`Hfun h₀ K r = max h₀ (tangentExp K r)` the model for `h`.  Both are continuous, monotone and
convex for `K ≥ 0`; the value lemmas record where they agree with the identity, respectively
with the constant `h₀`, and where they agree with `K e^r`.
-/
import Submission.Work.Profiles.TangentExp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory
open scoped Interval ContDiff Topology

namespace Work.Profiles

theorem continuous_Ffun (K : ℝ) : Continuous (Ffun K) :=
  continuous_id.max (continuous_tangentExp K)

theorem continuous_Hfun (h₀ K : ℝ) : Continuous (Hfun h₀ K) :=
  continuous_const.max (continuous_tangentExp K)

theorem monotone_Ffun {K : ℝ} (hK : 0 ≤ K) : Monotone (Ffun K) :=
  monotone_id.sup (monotone_tangentExp hK)

theorem monotone_Hfun {h₀ K : ℝ} (hK : 0 ≤ K) : Monotone (Hfun h₀ K) :=
  (monotone_const (c := h₀)).sup (monotone_tangentExp hK)

theorem convexOn_Ffun {K : ℝ} (hK : 0 ≤ K) : ConvexOn ℝ Set.univ (Ffun K) :=
  (convexOn_id convex_univ).sup (convexOn_tangentExp hK)

theorem convexOn_Hfun {h₀ K : ℝ} (hK : 0 ≤ K) : ConvexOn ℝ Set.univ (Hfun h₀ K) :=
  (convexOn_const h₀ convex_univ).sup (convexOn_tangentExp hK)

theorem Ffun_ge_id (K r : ℝ) : r ≤ Ffun K r := le_max_left _ _

theorem Hfun_ge_const (h₀ K r : ℝ) : h₀ ≤ Hfun h₀ K r := le_max_left _ _

/-- If `K e² ≥ 2` then the tangent line of `K e^·` at `2` lies below the identity up to `3/4`. -/
theorem tangentExp_le_self {K r : ℝ} (hK2 : 2 ≤ K * Real.exp 2) (hr : r ≤ 3/4) :
    tangentExp K r ≤ r := by
  rw [tangentExp_eq_left (le_trans hr (by norm_num))]
  have hA : 0 ≤ K * Real.exp 2 - 1 := by nlinarith [hK2]
  have h1 : r * (K * Real.exp 2 - 1) ≤ (3/4) * (K * Real.exp 2 - 1) :=
    mul_le_mul_of_nonneg_right hr hA
  nlinarith [h1]

theorem Ffun_eq_self {K r : ℝ} (hK2 : 2 ≤ K * Real.exp 2) (hr : r ≤ 3/4) :
    Ffun K r = r :=
  max_eq_left (tangentExp_le_self hK2 hr)

theorem Ffun_eq_exp {K r : ℝ} (hK2 : 2 ≤ K * Real.exp 2) (hr : 2 ≤ r) :
    Ffun K r = K * Real.exp r := by
  have hle : r ≤ tangentExp K r := by
    rw [tangentExp_eq_right hr]
    calc r ≤ 2 * r - 2 := by linarith
      _ = 2 * (1 + (r - 2)) := by ring
      _ ≤ 2 * Real.exp (r - 2) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (r - 2)]) (by norm_num)
      _ ≤ K * Real.exp 2 * Real.exp (r - 2) :=
          mul_le_mul_of_nonneg_right hK2 (Real.exp_pos _).le
      _ = K * Real.exp r := by
          rw [mul_assoc, ← Real.exp_add, show 2 + (r - 2) = r from by ring]
  rw [Ffun, max_eq_right hle, tangentExp_eq_right hr]

theorem Hfun_eq_left {h₀ K r : ℝ} (hK : 0 ≤ K) (hh₀ : 0 ≤ h₀) (hr : r ≤ 3/4) :
    Hfun h₀ K r = h₀ := by
  have hle : tangentExp K r ≤ h₀ := by
    rw [tangentExp_eq_left (le_trans hr (by norm_num))]
    have h1 : K * Real.exp 2 * (r - 1) ≤ K * Real.exp 2 * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [h1, Real.exp_pos 2]
  rw [Hfun, max_eq_left hle]

theorem Hfun_eq_exp {h₀ K r : ℝ} (hK : 0 ≤ K) (hle : h₀ ≤ K * Real.exp 2) (hr : 2 ≤ r) :
    Hfun h₀ K r = K * Real.exp r := by
  have hle' : h₀ ≤ tangentExp K r := by
    rw [tangentExp_eq_right hr]
    exact le_trans hle (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr) hK)
  rw [Hfun, max_eq_right hle', tangentExp_eq_right hr]

end Work.Profiles
