import Mathlib.Order.Interval.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# 1D convexity/concavity from an a.e. second derivative sign (Layer 3)

The maximum-principle bounds `0 ≤ ω ≤ 1` for the scattering profile will be
derived from the Carathéodory ODE `U'' = (v/2)·(U − id)` a.e. (`ScatProfileODE`):
wherever `U > id` (resp. `U < 0`-type regions) the a.e. second derivative has a
sign (`≥ 0` resp. `≤ 0` since `v ≥ 0`), making `U` convex (resp. concave)
there.  This module records the elementary 1D engine: a `C¹` function whose
derivative is absolutely continuous and has a.e. nonnegative (resp.
nonpositive) second derivative is convex (its derivative is monotone).

## Hypotheses (Mathlib idiom)

`f : ℝ → ℝ`, interval `Set.uIcc a b` (the unordered interval — the statements hold
for `a ≤ b`; use `uIcc` so no `a ≤ b` hypothesis is needed):

  * `hf : AbsolutelyContinuousOnInterval (deriv f) a b` — the derivative is
    absolutely continuous on the interval;
  * `hfae : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt (deriv f) (q x) x` — the a.e.
    second derivative is `q` (the Carathéodory content of `U'' = q` a.e.);
  * `hq : ∀ᵐ x, x ∈ Set.uIcc a b → 0 ≤ q x` (resp. `q x ≤ 0`).

Then `deriv f` is monotone (resp. antitone) on `Set.uIcc a b`.  The route: with
`deriv f` absolutely continuous, `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
gives `deriv f y − deriv f x = ∫ x..y, deriv (deriv f)`; by the a.e. identity
`deriv (deriv f) = q` a.e. and the sign of `q`, the integral is `≥ 0` (resp.
`≤ 0`) — one needs `intervalIntegral.integral_nonneg_of_ae`-style facts.
Convexity of `f` itself follows by Mathlib's `convexOn_iff_deriv_mono`-type
results (if available) or by a further integration; the derivative-monotonicity
conclusions are the primary targets.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Set
open scoped ContDiff Topology Real Interval

/-- If `deriv f` is absolutely continuous on `Set.uIcc a b` and its a.e. second
derivative is nonnegative there, then `deriv f` is monotone on `Set.uIcc a b`. -/
theorem monotoneOn_deriv_of_ae_second_nonneg {a b : ℝ} {f q : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval (deriv f) a b)
    (hfae : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → HasDerivAt (deriv f) (q x) x)
    (hq : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → 0 ≤ q x) :
    MonotoneOn (deriv f) (Set.uIcc a b) := by
  intro x hx y hy hxy
  have hsubset : Set.uIcc x y ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hx hy
  have hIcc_subset : Set.Icc x y ⊆ Set.uIcc a b := by
    rw [← uIcc_of_le hxy]
    exact hsubset
  have hxyac : AbsolutelyContinuousOnInterval (deriv f) x y := hf.mono hsubset
  have hfae' : ∀ᵐ t : ℝ, t ∈ Set.uIcc x y → HasDerivAt (deriv f) (q t) t := by
    filter_upwards [hfae] with t ht htxy
    exact ht (hsubset htxy)
  have hderiv_eq : ∀ᵐ t : ℝ, t ∈ Set.uIoc x y → deriv (deriv f) t = q t := by
    filter_upwards [hfae'] with t ht hti
    exact (ht (uIoc_subset_uIcc hti)).deriv
  have hcongr : (∫ t in x..y, deriv (deriv f) t) = ∫ t in x..y, q t := by
    exact intervalIntegral.integral_congr_ae hderiv_eq
  have hq_r : 0 ≤ᵐ[volume.restrict (Set.Icc x y)] q := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hq] with t ht hti
    exact ht (hIcc_subset hti)
  have hint_nonneg : 0 ≤ ∫ t in x..y, q t :=
    intervalIntegral.integral_nonneg_of_ae_restrict hxy hq_r
  have hftc : (∫ t in x..y, deriv (deriv f) t) = deriv f y - deriv f x :=
    hxyac.integral_deriv_eq_sub
  have hstep : 0 ≤ deriv f y - deriv f x := by
    rw [← hftc, hcongr]
    exact hint_nonneg
  linarith

/-- If `deriv f` is absolutely continuous on `Set.uIcc a b` and its a.e. second
derivative is nonpositive there, then `deriv f` is antitone on `Set.uIcc a b`. -/
theorem antitoneOn_deriv_of_ae_second_nonpos {a b : ℝ} {f q : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval (deriv f) a b)
    (hfae : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → HasDerivAt (deriv f) (q x) x)
    (hq : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → q x ≤ 0) :
    AntitoneOn (deriv f) (Set.uIcc a b) := by
  intro x hx y hy hxy
  have hsubset : Set.uIcc x y ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hx hy
  have hIcc_subset : Set.Icc x y ⊆ Set.uIcc a b := by
    rw [← uIcc_of_le hxy]
    exact hsubset
  have hxyac : AbsolutelyContinuousOnInterval (deriv f) x y := hf.mono hsubset
  have hfae' : ∀ᵐ t : ℝ, t ∈ Set.uIcc x y → HasDerivAt (deriv f) (q t) t := by
    filter_upwards [hfae] with t ht htxy
    exact ht (hsubset htxy)
  have hderiv_eq : ∀ᵐ t : ℝ, t ∈ Set.uIoc x y → deriv (deriv f) t = q t := by
    filter_upwards [hfae'] with t ht hti
    exact (ht (uIoc_subset_uIcc hti)).deriv
  have hcongr : (∫ t in x..y, deriv (deriv f) t) = ∫ t in x..y, q t := by
    exact intervalIntegral.integral_congr_ae hderiv_eq
  have hq_r : q ≤ᵐ[volume.restrict (Set.Icc x y)] 0 := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hq] with t ht hti
    exact ht (hIcc_subset hti)
  have hmq_r : 0 ≤ᵐ[volume.restrict (Set.Icc x y)] (-q) := by
    filter_upwards [hq_r] with t ht
    exact neg_nonneg.mpr ht
  have hint_nonpos : (∫ t in x..y, q t) ≤ 0 := by
    have hpos : 0 ≤ ∫ t in x..y, -q t :=
      intervalIntegral.integral_nonneg_of_ae_restrict hxy hmq_r
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  have hftc : (∫ t in x..y, deriv (deriv f) t) = deriv f y - deriv f x :=
    hxyac.integral_deriv_eq_sub
  have hstep : deriv f y - deriv f x ≤ 0 := by
    rw [← hftc, hcongr]
    exact hint_nonpos
  linarith

end Submission.BoseGases
