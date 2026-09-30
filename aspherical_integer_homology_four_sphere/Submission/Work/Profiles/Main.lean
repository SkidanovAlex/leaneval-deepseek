/-
Copyright: area `Profiles` of the aspherical 4-manifold project.

# Existence of filling profiles

The main theorem of the area: for every pair of cusp constants `C ≥ 1`, `D > 0` there is a
filling profile `(f, h)` with `f r = r` and `h r = h₀` on `[0, 1/2]` (the flat core) and
`f r = C e^r`, `h r = D e^r` on `[3, ∞)` (the hyperbolic cusp), smooth, positive, nondecreasing
and convex.

## Construction

Fix the symmetric bump `eta` (`C^∞`, supported in `[-1/4, 1/4]`, mass `1`) and put
`mEta = ∫ e^{-t} eta t`.  With `K = C / mEta`, the model function is `Ffun K = max (id)
(tangentExp K)`, where `tangentExp K` agrees with the identity's tangent line `K e² (r - 1)`
for `r ≤ 2` and with `K e^r` for `r ≥ 2`.  The profile is the smoothing `f = prof (Ffun K) eta`:

* `K e² ≥ 2` (which follows from `C ≥ 1` via `2 * mEta ≤ e²`) puts the crossing point of
  `tangentExp K` with the identity above `2`, so `Ffun K = id` below `3/4` and smoothing
  reproduces the identity on `[0, 1/2]`;
* `Ffun K = K e^r` above `2`, so smoothing reproduces `K e^r · mEta = C e^r` above `3`;
* `Ffun K ≥ id` and `Ffun K` monotone and convex, so `f` is positive, monotone and convex.

For `h` one uses `Hfun h₀ K' = max h₀ (tangentExp K')` with `K' = D / mEta` and
`h₀ = K' e² / 2`: the model is constant `h₀` below `3/2` and `K' e^r` above `2`.
-/
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta
import Submission.Work.Profiles.TangentExp
import Submission.Work.Profiles.Shape
import Submission.Work.Profiles.prof_smooth
import Submission.Work.Profiles.prof_mono
import Submission.Work.Profiles.prof_convexOn
import Submission.Work.Profiles.prof_ge_affine
import Submission.Work.Profiles.prof_core
import Submission.Work.Profiles.prof_core_const
import Submission.Work.Profiles.prof_cusp
import Submission.Work.Profiles.deriv2_nonneg_of_convexOn_smooth
import Submission.Work.Profiles.no_analytic_profile

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory
open scoped ContDiff

namespace Work.Profiles

/-- The `f`-component of the contract with `ContDiff ℝ ⊤` (analytic) smoothness is impossible:
an analytic function agreeing with the identity on `(-∞, 1/2]` is the identity everywhere by the
identity theorem, so it cannot agree with `C e^r` on `[3, ∞)`.  This is why `FillProfile` is
stated with `ContDiff ℝ ∞`; see `no_analytic_profile`. -/
theorem not_contDiff_omega_of_core_cusp (C : ℝ) (f : ℝ → ℝ) (hs : ContDiff ℝ ⊤ f)
    (hcore : ∀ r ≤ 1/2, f r = r) (hcusp : ∀ r ≥ 3, f r = C * Real.exp r) : False :=
  no_analytic_profile ⟨C, f, hs, hcore, hcusp⟩

/-- **Existence of filling profiles, with the explicit construction.**  For every `C ≥ 1` and
`D > 0` the profile
`f = prof (Ffun (C / mEta)) eta`, `h = prof (Hfun (D / mEta * e² / 2) (D / mEta)) eta`
has cusp constants `C` and `D`, core constant `h₀ = (D / mEta) e² / 2`, and all the properties
demanded by `FillProfile`. -/
theorem exists_fillProfile_explicit (C D : ℝ) (hC : 1 ≤ C) (hD : 0 < D) :
    ∃ P : FillProfile, P.C = C ∧ P.D = D ∧
      P.h₀ = (D / mEta) * Real.exp 2 / 2 ∧
      P.f = prof (Ffun (C / mEta)) eta ∧
      P.h = prof (Hfun ((D / mEta) * Real.exp 2 / 2) (D / mEta)) eta := by
  have hm : 0 < mEta := mEta_pos
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hKf_pos : 0 < C / mEta := div_pos hCpos hm
  have hKh_pos : 0 < D / mEta := div_pos hD hm
  -- `2 ≤ K e²` for `K = C / mEta` follows from `2 * mEta ≤ e²` and `1 ≤ C`.
  have hKf2 : 2 ≤ (C / mEta) * Real.exp 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    exact le_trans two_mul_mEta_le (le_mul_of_one_le_left (Real.exp_pos 2).le hC)
  have hh₀_pos : 0 < (D / mEta) * Real.exp 2 / 2 := by positivity
  have hh₀_le : (D / mEta) * Real.exp 2 / 2 ≤ (D / mEta) * Real.exp 2 := by
    have := Real.exp_pos 2
    have := hKh_pos
    linarith
  refine ⟨{
      C := C, D := D, h₀ := (D / mEta) * Real.exp 2 / 2,
      f := prof (Ffun (C / mEta)) eta,
      h := prof (Hfun ((D / mEta) * Real.exp 2 / 2) (D / mEta)) eta,
      f_smooth := prof_smooth eta_smooth eta_hasCompactSupport (continuous_Ffun _),
      h_smooth := prof_smooth eta_smooth eta_hasCompactSupport (continuous_Hfun _ _),
      f_core := prof_core (fun t ht => Ffun_eq_self (K := C / mEta) (r := t) hKf2 ht)
        (continuous_Ffun _) eta_nonneg eta_continuous eta_hasCompactSupport
        eta_eq_zero_of_quarter_le_abs integral_eta integral_eta_mul_id,
      h_core := prof_core_const _ (fun t ht => Hfun_eq_left (h₀ := (D / mEta) * Real.exp 2 / 2)
        (K := D / mEta) (r := t) hKh_pos.le hh₀_pos.le ht)
        (continuous_Hfun _ _) eta_nonneg eta_continuous eta_hasCompactSupport
        eta_eq_zero_of_quarter_le_abs integral_eta,
      f_cusp := fun r hr => by
        have h1 := prof_cusp (K := C / mEta)
          (fun t ht => Ffun_eq_exp (K := C / mEta) (r := t) hKf2 (le_trans (by norm_num) ht))
          (continuous_Ffun _) eta_continuous eta_hasCompactSupport
          eta_eq_zero_of_quarter_le_abs r hr
        have hmE : (∫ t, Real.exp (-t) * eta t) = mEta := rfl
        rw [h1, hmE, div_mul_cancel₀ C hm.ne'],
      h_cusp := fun r hr => by
        have h1 := prof_cusp (K := D / mEta)
          (fun t ht => Hfun_eq_exp (h₀ := (D / mEta) * Real.exp 2 / 2) (K := D / mEta) (r := t)
            hKh_pos.le hh₀_le (le_trans (by norm_num) ht))
          (continuous_Hfun _ _) eta_continuous eta_hasCompactSupport
          eta_eq_zero_of_quarter_le_abs r hr
        have hmE : (∫ t, Real.exp (-t) * eta t) = mEta := rfl
        rw [h1, hmE, div_mul_cancel₀ D hm.ne'],
      f_pos := fun r hr => by
        have h := prof_ge_affine 0 1 (fun t => by simpa using Ffun_ge_id (C / mEta) t)
          (continuous_Ffun _) eta_nonneg eta_continuous eta_hasCompactSupport integral_eta
          integral_eta_mul_id r
        linarith,
      h_pos := fun r => by
        have h := prof_ge_affine ((D / mEta) * Real.exp 2 / 2) 0
          (fun t => by simpa using Hfun_ge_const ((D / mEta) * Real.exp 2 / 2) (D / mEta) t)
          (continuous_Hfun _ _) eta_nonneg eta_continuous eta_hasCompactSupport integral_eta
          integral_eta_mul_id r
        linarith [hh₀_pos],
      f_mono := fun r => (prof_mono (monotone_Ffun hKf_pos.le) (continuous_Ffun _) eta_nonneg
        eta_continuous eta_hasCompactSupport).deriv_nonneg,
      h_mono := fun r => (prof_mono (monotone_Hfun hKh_pos.le) (continuous_Hfun _ _) eta_nonneg
        eta_continuous eta_hasCompactSupport).deriv_nonneg,
      f_convex := fun r => deriv2_nonneg_of_convexOn_smooth
        (prof_convexOn (convexOn_Ffun hKf_pos.le) (continuous_Ffun _) eta_nonneg eta_continuous
          eta_hasCompactSupport)
        (prof_smooth eta_smooth eta_hasCompactSupport (continuous_Ffun _)) r,
      h_convex := fun r => deriv2_nonneg_of_convexOn_smooth
        (prof_convexOn (convexOn_Hfun hKh_pos.le) (continuous_Hfun _ _) eta_nonneg eta_continuous
          eta_hasCompactSupport)
        (prof_smooth eta_smooth eta_hasCompactSupport (continuous_Hfun _ _)) r },
    rfl, rfl, rfl, rfl, rfl⟩

/-- **Existence of filling profiles.**  For every `C ≥ 1` and `D > 0` there is a `FillProfile`
with those cusp constants. -/
theorem exists_fillProfile (C D : ℝ) (hC : 1 ≤ C) (hD : 0 < D) :
    ∃ P : FillProfile, P.C = C ∧ P.D = D := by
  obtain ⟨P, hC', hD', -, -, -⟩ := exists_fillProfile_explicit C D hC hD
  exact ⟨P, hC', hD'⟩

end Work.Profiles
