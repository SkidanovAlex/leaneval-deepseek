import Submission.NBody.MarchalBumpScalar
import Submission.NBody.EnergyAe

/-!
# From the action difference to `actionOn`

The symmetric-bump argument produces the strict inequality
`∫ (lagR η - lagR γ) < 0` on the window `[t₀ - λT, t₀ + λT]` (and `η = γ` outside).  This module
converts it into `actionOn m h η a b < actionOn m h γ a b`:

* `integral_eq_of_ae_indicator` — an interval integral localised to a window on which the integrand
  is supported (a.e.);
* `actionOn_lt_of_integral_lt` — the `ofReal`/`integral` form of the action turns the strict
  inequality of integrals into the strict inequality of actions.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Localisation of an interval integral to a window.**  If `f` vanishes a.e. on the two outer
pieces `(a,c]` and `(d,b]`, then `∫_a^b f = ∫_c^d f`. -/
lemma integral_eq_of_ae_indicator {f : ℝ → ℝ} {a b c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b)
    (hleft : f =ᵐ[volume.restrict (Set.Ioc a c)] (fun _ : ℝ => (0:ℝ)))
    (hmid : IntervalIntegrable f volume c d)
    (hright : f =ᵐ[volume.restrict (Set.Ioc d b)] (fun _ : ℝ => (0:ℝ))) :
    ∫ t in a..b, f t = ∫ t in c..d, f t := by
  have hleft0 : ∫ t in a..c, f t = 0 := by
    have h : (fun t : ℝ => f t) =ᵐ[volume.restrict (Set.uIoc a c)] (fun _ : ℝ => (0:ℝ)) := by
      rw [Set.uIoc_of_le hac]
      exact hleft
    rw [intervalIntegral.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp h), intervalIntegral.integral_zero]
  have hright0 : ∫ t in d..b, f t = 0 := by
    have h : (fun t : ℝ => f t) =ᵐ[volume.restrict (Set.uIoc d b)] (fun _ : ℝ => (0:ℝ)) := by
      rw [Set.uIoc_of_le hdb]
      exact hright
    rw [intervalIntegral.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp h), intervalIntegral.integral_zero]
  have h1 : IntervalIntegrable f volume a c := by
    refine (intervalIntegrable_const (c := (0:ℝ))).congr_ae ?_
    rw [Set.uIoc_of_le hac]
    exact hleft.symm
  have h4 : IntervalIntegrable f volume d b := by
    refine (intervalIntegrable_const (c := (0:ℝ))).congr_ae ?_
    rw [Set.uIoc_of_le hdb]
    exact hright.symm
  have hstep1 : (∫ t in a..b, f t) = (∫ t in a..c, f t) + (∫ t in c..b, f t) :=
    (intervalIntegral.integral_add_adjacent_intervals h1 (hmid.trans h4)).symm
  have hstep2 : (∫ t in c..b, f t) = (∫ t in c..d, f t) + (∫ t in d..b, f t) :=
    (intervalIntegral.integral_add_adjacent_intervals hmid h4).symm
  rw [hstep1, hstep2, hleft0, hright0]
  ring

/-- **The strict inequality of actions.** -/
theorem actionOn_lt_of_integral_lt {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {h : ℝ} (hh : 0 ≤ h)
    {γ η : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hac' : AbsolutelyContinuousOnInterval η a b)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t))
    (hnc' : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (η t))
    (hfin : actionOn m h γ a b < ⊤) (hfin' : actionOn m h η a b < ⊤)
    (hint1 : IntervalIntegrable (fun t => lagR m h (η t) (deriv η t)) volume a b)
    (hint2 : IntervalIntegrable (fun t => lagR m h (γ t) (deriv γ t)) volume a b)
    (hlt : ∫ t in a..b, (lagR m h (η t) (deriv η t) - lagR m h (γ t) (deriv γ t)) < 0) :
    actionOn m h η a b < actionOn m h γ a b := by
  have h1 := actionOn_eq_ofReal_integral_lagR_of_ae hab hm hh hac hnc hfin
  have h2 := actionOn_eq_ofReal_integral_lagR_of_ae hab hm hh hac' hnc' hfin'
  rw [h1, h2]
  refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?_ |>.mpr ?_
  · refine intervalIntegral.integral_nonneg hab fun t _ => ?_
    rw [lagR_eq hm]
    have hU := U_nonneg hm (η t)
    have hw : (0:ℝ) ≤ ‖deriv η t‖_[m] ^ 2 := sq_nonneg _
    linarith
  · have hsub : ∫ t in a..b, (lagR m h (η t) (deriv η t) - lagR m h (γ t) (deriv γ t))
        = (∫ t in a..b, lagR m h (η t) (deriv η t))
          - (∫ t in a..b, lagR m h (γ t) (deriv γ t)) :=
      intervalIntegral.integral_sub hint1 hint2
    linarith [hlt, hsub]

/-- **The endgame: the symmetric bump contradicts minimality.**  All the data of the blow-up
argument (the two-sided asymptotics, the outward direction) is funnelled through the strict
negativity of the action difference on the window. -/
theorem not_isHMinimizer_of_window_negative {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    (hh : 0 ≤ h) {γ : ℝ → EN E N} {a b t₀ T lam : ℝ} (hab : a < b)
    {k : Finset (Fin N)} {i₀ : Fin N} {δ : E} (hδ : δ ≠ 0) (hlam : 0 < lam) (hT : 0 ≤ T)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hacη : AbsolutelyContinuousOnInterval (bumpCurve m k i₀ δ T lam t₀ γ) a b)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t))
    (hncη : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      WithoutCollisions (bumpCurve m k i₀ δ T lam t₀ γ t))
    (hfin : actionOn m h γ a b < ⊤)
    (hfinη : actionOn m h (bumpCurve m k i₀ δ T lam t₀ γ) a b < ⊤)
    (hint1 : IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)) volume a b)
    (hint2 : IntervalIntegrable (fun t => lagR m h (γ t) (deriv γ t)) volume a b)
    (hleft : (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      =ᵐ[volume.restrict (Set.Ioc a (t₀ - lam * T))] (fun _ : ℝ => (0:ℝ)))
    (hmid : IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      volume (t₀ - lam * T) (t₀ + lam * T))
    (hright : (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      =ᵐ[volume.restrict (Set.Ioc (t₀ + lam * T) b)] (fun _ : ℝ => (0:ℝ)))
    (horders : a ≤ t₀ - lam * T) (horders2 : t₀ + lam * T ≤ b)
    (hwin : ∫ t in (t₀ - lam * T)..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t)) < 0)
    (hmin : IsHMinimizer m h γ a b) : False := by
  have hloc := integral_eq_of_ae_indicator (f := fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
    horders (by nlinarith [mul_nonneg hlam.le hT]) horders2 hleft hmid hright
  have hlt : ∫ t in a..b, (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t)) < 0 := by
    rw [hloc]; exact hwin
  have hact := actionOn_lt_of_integral_lt (fun i => (hm i).le) hh hab.le hac hacη hnc hncη
    hfin hfinη hint1 hint2 hlt
  have hlt₀ : a ≤ t₀ := by nlinarith [mul_nonneg hlam.le hT]
  have ha : lam * T ≤ |a - t₀| := by
    rw [abs_of_nonpos (by linarith), neg_sub]
    linarith
  have hb : lam * T ≤ |b - t₀| := by
    have h2 : t₀ ≤ b := by nlinarith [mul_nonneg hlam.le hT]
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine not_isHMinimizer_of_action_lt hab hacη ?_ ?_ hact hmin
  · rw [bumpCurve_eq_of_le hδ hlam ha]
  · rw [bumpCurve_eq_of_le hδ hlam hb]

end Submission.NBody
