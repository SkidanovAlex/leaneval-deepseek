import Mathlib
import Submission.Work.SphereJordan.SpanHyp
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.SphereJordan.incrOn
import Submission.Work.Smooth.SphereJordan.windNumberCircleCurve
import Submission.Work.SphereJordan.annulusTargetCurves
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

/-!
# Toolkit for the pairing identities of the two-cuts curves

This module collects the elementary bookkeeping which the proof of
`Work.SphereJordan.windNumberPairingIdentities` needs:

* the number `kap = 2πI`;
* the rotated unit circle `rotC S`;
* `windNumber_incOn_period`: the winding number of a `2π`-periodic plane curve is, up to `kap`,
  the argument increment over one period;
* `incOn_split4`: the increment over `[0,2π]` splits into the four quarters;
* `pathIncTot_rev` / `incIn_rev_neg`: the increment over `[b,a]` is minus the increment over
  `[a,b]`, *without* any non-vanishing hypothesis (both sides are `0` when the arc meets the base
  point);
* `incOn_sub_period`: the increment is invariant under a `2π`-shift of the interval;
* `incOn_eq_of_forall'`: reparametrised arcs have the same increment.
-/

open Set
open Classical

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- `2πI`, the increment of one full turn. -/
def kap : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem kap_ne_zero : kap ≠ 0 :=
  Work.Smooth.SphereJordan.two_pi_I_ne_zero

/-- The unit circle, rotated so as to start at `cutDir S`; the parameter equals the angle. -/
def rotC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ℝ → ℂ :=
  fun r => Work.Smooth.SphereJordan.cutDir S * Complex.exp (((r : ℝ) : ℂ) * Complex.I)

theorem continuous_rotC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Continuous (rotC S) := by
  unfold rotC; fun_prop

theorem rotC_periodic (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Function.Periodic (rotC S) (2 * Real.pi) := by
  intro r
  unfold rotC
  rw [show ((r + 2 * Real.pi : ℝ) : ℂ) = (r : ℂ) + ((2 * Real.pi : ℝ) : ℂ) from by
      push_cast; ring,
    add_mul, Complex.exp_add]
  rw [show Complex.exp ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) = 1 from by
    rw [show ((((2 * Real.pi : ℝ)) : ℂ)) = (2 : ℂ) * (Real.pi : ℂ) from by push_cast; ring]
    exact Complex.exp_two_pi_mul_I]
  ring

theorem norm_rotC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (r : ℝ) : ‖rotC S r‖ = 1 := by
  unfold rotC
  rw [norm_mul, Work.Smooth.SphereJordan.norm_cutDir, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem rotC_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : ‖x‖ < 1) (r : ℝ) :
    rotC S r ≠ x := by
  intro h
  have h1 := norm_rotC S r
  rw [h] at h1
  rw [h1] at hx
  exact lt_irrefl 1 hx

/-- **Two arcs that agree after reparametrisation have the same increment.** -/
theorem incOn_eq_of_forall' {γ δ : ℝ → ℂ} (hγ : Continuous γ) (hδ : Continuous δ) {z : ℂ}
    {a b c d : ℝ}
    (h : ∀ t : unitInterval, γ (a + (t : ℝ) * (b - a)) = δ (c + (t : ℝ) * (d - c))) :
    incOn γ hγ z a b = incOn δ hδ z c d := by
  rw [incOn, incOn]
  refine pathIncTot_congr (fun t => ?_)
  simp only [ContinuousMap.coe_mk]
  rw [h t]

/-- **The winding number is the increment over one period**, divided by `2πI`. -/
theorem windNumber_incOn_period (Γ : Work.Smooth.Jordan.PlaneCurve) {x : ℂ}
    (hav : ∀ t : ℝ, Γ.γ t ≠ x) :
    (Work.Smooth.SphereJordan.windNumber Γ.γ Γ.cont x : ℂ) * kap =
      incOn Γ.γ Γ.cont x 0 (2 * Real.pi) := by
  have h := incOn_period Γ.cont Γ.periodic x hav 0
  rw [zero_add] at h
  exact h.symm

/-- **The increment over one period splits into the four quarters.** -/
theorem incOn_split4 (Γ : Work.Smooth.Jordan.PlaneCurve) {x : ℂ}
    (hav : ∀ t : ℝ, Γ.γ t ≠ x) :
    incOn Γ.γ Γ.cont x 0 (2 * Real.pi) =
      incOn Γ.γ Γ.cont x 0 (Real.pi / 2) + incOn Γ.γ Γ.cont x (Real.pi / 2) Real.pi +
        incOn Γ.γ Γ.cont x Real.pi (3 * Real.pi / 2) +
        incOn Γ.γ Γ.cont x (3 * Real.pi / 2) (2 * Real.pi) := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hav' : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Γ.γ t ≠ x := fun t _ => hav t
  have h1 := incOn_add Γ.cont (show (0 : ℝ) ≤ Real.pi by linarith)
    (show Real.pi ≤ 2 * Real.pi by linarith) hav'
  have h2 := incOn_add Γ.cont (show (0 : ℝ) ≤ Real.pi / 2 by linarith)
    (show Real.pi / 2 ≤ Real.pi by linarith) (fun t _ => hav t)
  have h3 := incOn_add Γ.cont (show Real.pi ≤ 3 * Real.pi / 2 by linarith)
    (show 3 * Real.pi / 2 ≤ 2 * Real.pi by linarith) (fun t _ => hav t)
  rw [h1, h2, h3]
  ring

/-- The reversal of the parametrisation of the unit interval. -/
theorem revI_val' (t : unitInterval) : ((revI t : unitInterval) : ℝ) = 1 - (t : ℝ) := by
  change (1 : ℝ) + (0 - 1) * (t : ℝ) = 1 - (t : ℝ)
  ring

theorem revI_involutive' (t : unitInterval) : revI (revI t) = t := by
  apply Subtype.ext
  rw [revI_val', revI_val']
  ring

/-- **Reversal of the total increment**: no non-vanishing hypothesis is needed, since a path that
meets `0` has increment `0` in either direction. -/
theorem pathIncTot_rev (c : C(unitInterval, ℂ)) : pathIncTot (c.comp revI) = -pathIncTot c := by
  by_cases hc : ∀ t, c t ≠ 0
  · have hcomp : ∀ t, c.comp revI t ≠ 0 := fun t => hc _
    obtain ⟨Λ, hΛ, -, -⟩ := Work.Smooth.SphereJordan.argChangeLift c hc
    rw [pathIncTot_eq_of_lift (c.comp revI) hcomp (Λ.comp revI) (fun t => by
          simp only [ContinuousMap.comp_apply]; rw [hΛ]),
        pathIncTot_eq_of_lift c hc Λ hΛ]
    simp only [ContinuousMap.comp_apply]
    rw [show revI 1 = 0 from Subtype.ext (by rw [revI_val']; norm_num),
      show revI 0 = 1 from Subtype.ext (by rw [revI_val']; norm_num)]
    ring
  · have hcomp : ¬ ∀ t, c.comp revI t ≠ 0 := by
      intro hcomp
      refine hc fun t => ?_
      have h := hcomp (revI t)
      rwa [ContinuousMap.comp_apply, revI_involutive'] at h
    unfold pathIncTot
    rw [dif_neg hcomp, dif_neg hc]
    simp

/-- **Reversal of the increment**, with no non-vanishing hypothesis. -/
theorem incIn_rev_neg {γ : ℝ → ℂ} (hγ : Continuous γ) {z : ℂ} {a b : ℝ} :
    incOn γ hγ z b a = -incOn γ hγ z a b := by
  let p : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval => γ (a + (t : ℝ) * (b - a)) - z, by fun_prop⟩
  let q : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval => γ (b + (t : ℝ) * (a - b)) - z, by fun_prop⟩
  have hp' : incOn γ hγ z a b = pathIncTot p := rfl
  have hq' : incOn γ hγ z b a = pathIncTot q := rfl
  have hqp : pathIncTot q = pathIncTot (p.comp revI) := pathIncTot_congr (fun t => by
    show γ (b + (t : ℝ) * (a - b)) - z =
      γ (a + (((revI t : unitInterval) : ℝ)) * (b - a)) - z
    rw [revI_val']
    congr 1
    ring)
  rw [hp', hq', hqp, pathIncTot_rev]


/-- **Multiplying a path by a nonzero constant does not change its increment.** -/
theorem pathIncTot_const_mul (u : ℂ) (hu : u ≠ 0) (p : C(unitInterval, ℂ)) :
    pathIncTot (ContinuousMap.const unitInterval u * p) = pathIncTot p := by
  by_cases hp : ∀ t, p t ≠ 0
  · have hup : ∀ t, (ContinuousMap.const unitInterval u * p) t ≠ 0 := fun t =>
      mul_ne_zero hu (hp t)
    obtain ⟨Λ, hΛ, -, -⟩ := Work.Smooth.SphereJordan.argChangeLift p hp
    have hΛu : ∀ t,
        Complex.exp ((ContinuousMap.const unitInterval (Complex.log u) + Λ) t) =
          (ContinuousMap.const unitInterval u * p) t := by
      intro t
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.mul_apply,
        Complex.exp_add, Complex.exp_log hu, hΛ t]
    rw [pathIncTot_eq_of_lift _ hup _ hΛu, pathIncTot_eq_of_lift p hp Λ hΛ]
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  · have hup : ¬ ∀ t, (ContinuousMap.const unitInterval u * p) t ≠ 0 := by
      intro h
      obtain ⟨t, ht⟩ := not_forall.mp hp
      have ht' : p t = 0 := by simpa using ht
      exact h t (by rw [ContinuousMap.mul_apply, ContinuousMap.const_apply, ht', mul_zero])
    unfold pathIncTot
    rw [dif_neg hup, dif_neg hp]

/-- **The increment of the rotated unit circle about an interior point is one turn.** -/
theorem incOn_rotC_period (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : ‖x‖ < 1) :
    incOn (rotC S) (continuous_rotC S) x 0 (2 * Real.pi) = kap := by
  set u : ℂ := Work.Smooth.SphereJordan.cutDir S with hu_def
  have hu : u ≠ 0 := Work.Smooth.SphereJordan.cutDir_ne_zero S
  set y : ℂ := x / u with hy_def
  have hy : ‖y‖ < 1 := by
    rw [hy_def, norm_div, Work.Smooth.SphereJordan.norm_cutDir, div_one]; exact hx
  set p : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval =>
      Work.Smooth.SphereJordan.circleCurve.γ (0 + (t : ℝ) * (2 * Real.pi - 0)) - y,
      (Work.Smooth.SphereJordan.circleCurve.cont.comp (by fun_prop)).sub continuous_const⟩
    with hp_def
  set c₁ : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval => rotC S (0 + (t : ℝ) * (2 * Real.pi - 0)) - x,
      ((continuous_rotC S).comp (by fun_prop)).sub continuous_const⟩ with hc₁_def
  have hc₁ : incOn (rotC S) (continuous_rotC S) x 0 (2 * Real.pi) = pathIncTot c₁ := by
    rw [incOn]
  have hconst : pathIncTot c₁ = pathIncTot (ContinuousMap.const unitInterval u * p) := by
    refine pathIncTot_congr (fun t => ?_)
    simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, ContinuousMap.coe_mk, hp_def,
      hc₁_def, hu_def, hy_def]
    have hrot : rotC S (0 + (t : ℝ) * (2 * Real.pi - 0)) =
        u * Work.Smooth.SphereJordan.circleCurve.γ (0 + (t : ℝ) * (2 * Real.pi - 0)) := by
      rw [rotC, Work.Smooth.SphereJordan.circleCurve_apply, Work.Smooth.Jordan.circlePoint_coe]
    rw [hrot, hu_def]
    have hud : Work.Smooth.SphereJordan.cutDir S ≠ 0 :=
      Work.Smooth.SphereJordan.cutDir_ne_zero S
    field_simp
  have hmul := pathIncTot_const_mul u hu p
  have hq : pathIncTot p = incOn (Work.Smooth.SphereJordan.circleCurve.γ)
      (Work.Smooth.SphereJordan.circleCurve.cont) y 0 (2 * Real.pi) := by
    rw [incOn]
  have hper : incOn (Work.Smooth.SphereJordan.circleCurve.γ)
      (Work.Smooth.SphereJordan.circleCurve.cont) y 0 (2 * Real.pi) =
      (Work.Smooth.SphereJordan.windNumber (Work.Smooth.SphereJordan.circleCurve.γ)
        (Work.Smooth.SphereJordan.circleCurve.cont) y : ℂ) * kap := by
    have h := incOn_period (Work.Smooth.SphereJordan.circleCurve.cont)
      (Work.Smooth.SphereJordan.circleCurve.periodic) y
      (fun t => by
        intro hcon
        have h1 : ‖Work.Smooth.SphereJordan.circleCurve.γ t‖ = 1 :=
          Work.Smooth.SphereJordan.norm_circleCurve_apply t
        rw [hcon] at h1
        rw [h1] at hy
        exact lt_irrefl 1 hy) 0
    rw [zero_add] at h
    exact h
  have hwind : Work.Smooth.SphereJordan.windNumber (Work.Smooth.SphereJordan.circleCurve.γ)
      (Work.Smooth.SphereJordan.circleCurve.cont) y = 1 :=
    Work.Smooth.SphereJordan.windNumberCircleCurve y hy
  rw [hc₁, hconst, hmul, hq, hper, hwind]
  simp

/-- **The increment is invariant under a `2π`-shift of the parameter interval.** -/
theorem incOn_sub_period {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (z : ℂ) (a b : ℝ) :
    incOn γ hγ z (a - 2 * Real.pi) b = incOn γ hγ z a (b + 2 * Real.pi) := by
  refine incOn_eq_of_forall' hγ hγ (fun t => ?_)
  show γ ((a - 2 * Real.pi) + (t : ℝ) * (b - (a - 2 * Real.pi))) =
    γ (a + (t : ℝ) * ((b + 2 * Real.pi) - a))
  have h : (a - 2 * Real.pi) + (t : ℝ) * (b - (a - 2 * Real.pi)) + 2 * Real.pi =
      a + (t : ℝ) * ((b + 2 * Real.pi) - a) := by ring
  rw [← h]
  exact (hper (a - 2 * Real.pi + (t : ℝ) * (b - (a - 2 * Real.pi)))).symm

end

end Work.SphereJordan
