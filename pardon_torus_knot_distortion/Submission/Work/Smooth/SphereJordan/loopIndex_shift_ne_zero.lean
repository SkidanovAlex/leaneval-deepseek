import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy
import Submission.Work.Smooth.SphereJordan.windNumber_ne_zero_of_antiperiodic
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic

/-!
# The index of a shifted chord loop of a simple closed plane curve

Let `γ : ℝ → ℂ` be continuous, `2π`-periodic and injective on one period `[0, 2π)`, and let
`θ ∈ (0, 2π)`.  Then the closed loop

`t ↦ γ t - γ (t + θ)`

has non-zero index around the origin.

The argument is in three steps.

* `ne_of_shift` — injectivity on one period says that a shift by `θ ∈ (0, 2π)` never returns:
  `γ t ≠ γ (t + θ)` (via the period lattice `exists_int_sub_eq_of_periodic_injOn`).
* `loopIndex_shift_eq` — **the index does not depend on the shift** `θ ∈ (0, 2π)`: the affine
  interpolation of the shift parameter is a nowhere vanishing homotopy of closed loops, so the
  homotopy invariance of the index applies.
* `loopIndex_shift_pi_ne_zero` — at `θ = π` the loop *is* non-zero, because the chord curve
  `c t = γ t - γ (t + π)` is anti-periodic (`c (t + π) = -c t`) and nowhere vanishing, so
  `windNumber_ne_zero_of_antiperiodic` gives a non-zero index of its own loop, which is exactly the
  `π`-shift loop.

Combining the last two gives the statement for the given `θ`.
-/

noncomputable section

open Set

namespace Work.Smooth.SphereJordan

/-- Congruence of the loops attached to pointwise equal `2π`-periodic curves. -/
theorem curveLoop_congr {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, f t = g t) : curveLoop f hf = curveLoop g hg :=
  ContinuousMap.ext fun t => h (2 * Real.pi * (t : ℝ))

/-- No non-zero integer multiple of `2π` lies strictly between `0` and `2π`. -/
theorem int_eq_zero_of_mul_two_pi_mem_Ioo {k : ℤ}
    (h0 : 0 < (k : ℝ) * (2 * Real.pi)) (h1 : (k : ℝ) * (2 * Real.pi) < 2 * Real.pi) :
    k = 0 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk0 : (0 : ℝ) < (k : ℝ) := by nlinarith
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk0' : (0 : ℤ) < k := by exact_mod_cast hk0
  have hk1' : k < 1 := by exact_mod_cast hk1
  omega

/-- **A non-trivial shift of a simple closed plane curve never returns.**  If `γ` is `2π`-periodic
and injective on `[0, 2π)`, then `γ t ≠ γ (t + θ)` for `θ ∈ (0, 2π)`. -/
theorem ne_of_shift {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {t θ : ℝ} (hθ0 : 0 < θ)
    (hθ2 : θ < 2 * Real.pi) : γ t ≠ γ (t + θ) := by
  intro h
  obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj h
  have hk' : -θ = (k : ℝ) * (2 * Real.pi) := by linarith
  have hpos : (0 : ℝ) < ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    nlinarith
  have hlt : ((-k : ℤ) : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    push_cast
    nlinarith
  have hk0 : -k = 0 := int_eq_zero_of_mul_two_pi_mem_Ioo hpos hlt
  have hk0' : k = 0 := by omega
  rw [hk0'] at hk'
  simp only [Int.cast_zero, zero_mul] at hk'
  linarith

/-- **The index of the shifted chord loop of a simple closed plane curve is independent of the
shift** `θ ∈ (0, 2π)`. -/
theorem loopIndex_shift_eq {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ θ' : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) (hθ'0 : 0 < θ')
    (hθ'2 : θ' < 2 * Real.pi) :
    loopIndex (curveLoop (fun t => γ t - γ (t + θ))
        (hγ.sub (hγ.comp (continuous_id.add continuous_const)))) =
      loopIndex (curveLoop (fun t => γ t - γ (t + θ'))
        (hγ.sub (hγ.comp (continuous_id.add continuous_const)))) := by
  have hcontθ : Continuous fun t : ℝ => γ t - γ (t + θ) :=
    hγ.sub (hγ.comp (continuous_id.add continuous_const))
  have hcontθ' : Continuous fun t : ℝ => γ t - γ (t + θ') :=
    hγ.sub (hγ.comp (continuous_id.add continuous_const))
  -- the interpolated shift parameter
  let Θ : unitInterval → ℝ := fun s => (1 - (s : ℝ)) * θ + (s : ℝ) * θ'
  have hΘpos : ∀ s : unitInterval, 0 < Θ s := by
    intro s
    unfold Θ
    rcases le_total θ θ' with h | h
    · nlinarith [hθ0, s.2.1, s.2.2, h]
    · nlinarith [hθ'0, s.2.1, s.2.2, h]
  have hΘlt : ∀ s : unitInterval, Θ s < 2 * Real.pi := by
    intro s
    unfold Θ
    rcases le_total θ θ' with h | h
    · nlinarith [hθ'2, s.2.1, s.2.2, h]
    · nlinarith [hθ2, s.2.1, s.2.2, h]
  have hΘcont : Continuous Θ := by
    unfold Θ
    fun_prop
  -- the homotopy
  let F : unitInterval × unitInterval → ℂ := fun p =>
    γ (2 * Real.pi * (p.1 : ℝ)) - γ (2 * Real.pi * (p.1 : ℝ) + Θ p.2)
  have h1c : Continuous fun p : unitInterval × unitInterval => 2 * Real.pi * (p.1 : ℝ) := by
    fun_prop
  have h2c : Continuous fun p : unitInterval × unitInterval =>
      2 * Real.pi * (p.1 : ℝ) + Θ p.2 :=
    h1c.add (hΘcont.comp continuous_snd)
  have hFcont : Continuous F := (hγ.comp h1c).sub (hγ.comp h2c)
  let H : C(unitInterval × unitInterval, ℂ) := ⟨F, hFcont⟩
  have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := by
    rintro ⟨t, s⟩ h0
    have heq : γ (2 * Real.pi * (t : ℝ)) = γ (2 * Real.pi * (t : ℝ) + Θ s) := sub_eq_zero.mp h0
    exact ne_of_shift hper hinj (hΘpos s) (hΘlt s) heq
  have hΘ0 : Θ (0 : unitInterval) = θ := by
    unfold Θ
    norm_num
  have hΘ1 : Θ (1 : unitInterval) = θ' := by
    unfold Θ
    norm_num
  have hH0 : ∀ t : unitInterval, H (t, 0) = (curveLoop (fun t => γ t - γ (t + θ)) hcontθ) t := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + Θ (0 : unitInterval))
      = γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ)
    rw [hΘ0]
  have hH1 : ∀ t : unitInterval, H (t, 1) = (curveLoop (fun t => γ t - γ (t + θ')) hcontθ') t := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + Θ (1 : unitInterval))
      = γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ')
    rw [hΘ1]
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - γ (2 * Real.pi * ((0 : unitInterval) : ℝ) + Θ s)
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - γ (2 * Real.pi * ((1 : unitInterval) : ℝ) + Θ s)
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
    rw [h0, h1]
    have ha : γ (2 * Real.pi) = γ 0 := by simpa using (hper 0)
    have hb : γ (2 * Real.pi + Θ s) = γ (0 + Θ s) := by
      rw [zero_add, add_comm (2 * Real.pi) (Θ s)]
      exact hper (Θ s)
    rw [ha, hb]
  have hne0 : ∀ t : unitInterval, (curveLoop (fun t => γ t - γ (t + θ)) hcontθ) t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ) ≠ 0
    exact sub_ne_zero.mpr (ne_of_shift hper hinj hθ0 hθ2)
  have hne1 : ∀ t : unitInterval, (curveLoop (fun t => γ t - γ (t + θ')) hcontθ') t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ') ≠ 0
    exact sub_ne_zero.mpr (ne_of_shift hper hinj hθ'0 hθ'2)
  exact loopIndex_eq_of_homotopy hne0 hne1 H hHne hH0 hH1 hHloop

/-- **The index of the `π`-shifted chord loop of a simple closed plane curve is non-zero.**

The chord curve `c t = γ t - γ (t + π)` is continuous, `2π`-periodic, nowhere vanishing (by
injectivity) and anti-periodic (`c (t + π) = -c t`), so `windNumber_ne_zero_of_antiperiodic` gives
that its own loop — which is the `π`-shift loop of `γ` — has non-zero index. -/
theorem loopIndex_shift_pi_ne_zero {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    loopIndex (curveLoop (fun t => γ t - γ (t + Real.pi))
        (hγ.sub (hγ.comp (continuous_id.add continuous_const)))) ≠ 0 := by
  let c : ℝ → ℂ := fun t => γ t - γ (t + Real.pi)
  have hcont : Continuous c := hγ.sub (hγ.comp (continuous_id.add continuous_const))
  have hcper : Function.Periodic c (2 * Real.pi) := by
    intro t
    show γ (t + 2 * Real.pi) - γ (t + 2 * Real.pi + Real.pi) = γ t - γ (t + Real.pi)
    have h1 : t + 2 * Real.pi + Real.pi = (t + Real.pi) + 2 * Real.pi := by ring
    rw [h1, hper t, hper (t + Real.pi)]
  have hcanti : ∀ t : ℝ, c (t + Real.pi) = -c t := by
    intro t
    show γ (t + Real.pi) - γ (t + Real.pi + Real.pi) = -(γ t - γ (t + Real.pi))
    have h1 : t + Real.pi + Real.pi = t + 2 * Real.pi := by ring
    rw [h1, hper t]
    ring
  have hcne : ∀ t : ℝ, c t ≠ 0 := by
    intro t h
    exact ne_of_shift hper hinj (θ := Real.pi) Real.pi_pos (by linarith [Real.pi_pos]) (sub_eq_zero.mp h)
  have hanti := windNumber_ne_zero_of_antiperiodic hcont hcper hcanti hcne
  have hcurve : curveLoop (fun t => c t - 0) (hcont.sub continuous_const) = curveLoop c hcont :=
    curveLoop_congr _ _ (fun t => sub_zero (c t))
  change loopIndex (curveLoop (fun t => c t - 0) (hcont.sub continuous_const)) ≠ 0 at hanti
  rw [hcurve] at hanti
  exact hanti

theorem loopIndex_shift_ne_zero {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    loopIndex (curveLoop (fun t => γ t - γ (t + θ))
      (hγ.sub (hγ.comp (continuous_id.add continuous_const)))) ≠ 0 := by
  rw [loopIndex_shift_eq hγ hper hinj hθ0 hθ2 Real.pi_pos (by linarith [Real.pi_pos])]
  exact loopIndex_shift_pi_ne_zero hγ hper hinj

end Work.Smooth.SphereJordan
